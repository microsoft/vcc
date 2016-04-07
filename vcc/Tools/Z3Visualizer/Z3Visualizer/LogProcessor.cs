//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.IO;
using System.Text;
using System.Text.RegularExpressions;
using System.Windows.Forms;
using Z3AxiomProfiler.QuantifierModel;

namespace Z3AxiomProfiler
{
  public class LogProcessor
  {
    private int curlineNo = 0;
    private int beginCheckSeen = 0;
    private bool interestedInCurrentCheck = true;
    private int checkToConsider = 1;
    private int eofSeen = 0;
    private Conflict curConfl = null;
    private List<Literal> cnflResolveLits = new List<Literal>();
    private Instantiation lastInst = null;
    private Term decideClause = null;
    private Term[] EmptyTerms = new Term[0];
    private Dictionary<string, List<string>> boogieFiles = new Dictionary<string, List<string>>();
    private Dictionary<string, string> shortnameMap = new Dictionary<string, string>();
    private Dictionary<int, Literal> literalById = new Dictionary<int, Literal>();
    private FunSymbol currentFun;
    private int cnflCount;
    private ResolutionLiteral currResRoot, currResNode;

    public LogProcessor(List<FileInfo> bplFileInfos, bool skipDecisions, int cons)
    {
      checkToConsider = cons;
      lastInst = null;
      curlineNo = 0;
      this.skipDecisions = skipDecisions;
      if (bplFileInfos != null)
        LoadBoogieFiles(bplFileInfos);
    }


    public Model model = new Model();
    public bool skipDecisions = false;

    public void LoadBoogieFiles(List<FileInfo> bplFileInfos)
    {
      List<string> doubleShortNames = new List<string>();
      foreach (FileInfo fi in bplFileInfos) {
        string shortname;
        string basename = fi.Name.Replace(".", "").Replace("_", "").ToLower();
        if (basename.Length > 8)
          shortname = basename.Substring(0, 8);
        else
          shortname = basename;

        if (boogieFiles.ContainsKey(shortname)) {
          doubleShortNames.Add(shortname);
          MessageBox.Show("Overlapping shortname for boogiefiles: " + shortname);
        } else if (fi.Exists) {
          shortnameMap[shortname] = fi.Name;
          List<string> lines = new List<string>();
          using (TextReader rd = new StreamReader(fi.OpenRead())) {
            string line;
            while ((line = rd.ReadLine()) != null) {
              lines.Add(line);
            }
          }
          boogieFiles[fi.Name] = lines;
        }
      }
      foreach (string shortname in doubleShortNames) {
        if (shortnameMap.ContainsKey(shortname)) {
          shortnameMap.Remove(shortname);
        }
      }
    }

    string StringReplaceIgnoreCase(string input, string search, string repl)
    {
      string regexppattern = String.Format("^{0}", search);
      Regex re = new Regex(regexppattern, RegexOptions.IgnoreCase);

      return re.Replace(input, repl); 
    }

    void loadBoogieToken(Quantifier quant)
    {
      string result = "";
      string[] tokens = quant.Qid.Split(':', '.');
      string shortname = tokens[0].ToLower();
      if (shortname != "bg" && shortname != "bv" && shortname != "unknown" && shortnameMap.ContainsKey(shortname)) {
        string fullname = shortnameMap[shortname];
        quant.Qid = StringReplaceIgnoreCase(quant.Qid, shortname, fullname);
        //quant.Name = quant.Name.Replace(shortname, fullname);
        List<string> lines = boogieFiles[fullname];
        int lineNo = int.Parse(tokens[1]) - 1;
        int col = int.Parse(tokens[2]) - 1;
        if (lines.Count > lineNo && lines[lineNo].Length > col) {
          string cur = lines[lineNo] + "\n";
          int pos = col;
          int lev = 1;

          string tmp = cur.Substring(pos);
          if (!tmp.StartsWith("forall") && !tmp.StartsWith("exists")) {
            string c2 = cur.Substring(0, pos);
            int x = c2.LastIndexOf("forall");
            if (x < 0)
              x = c2.LastIndexOf("exists");
            if (x >= 0) {
              pos = x;
              tmp = cur.Substring(pos);
            }
          }

          if (!(tmp.StartsWith("forall") || tmp.StartsWith("exists"))) {
            while (pos >= 0 && (cur[pos] == '(' || char.IsWhiteSpace(cur[pos]))) pos--;
            while (pos >= 0 && cur[pos] != '\n') pos--;
            pos++;
            result = cur.Substring(pos);
          } else {
            StringBuilder res = new StringBuilder();
            int lastRet = 0;
            while (res.Length < 600) {
              if (pos >= cur.Length) {
                ++lineNo;
                if (lines.Count <= lineNo) break;
                pos = 0;
                cur = lines[lineNo] + "\n";
                continue;
              }
              switch (cur[pos]) {
                case ')': lev--; break;
                case '(': lev++; break;
                case '\n': lastRet = res.Length; break;
                default: break;
              }
              if (lev == 0) break;
              res.Append(cur[pos]);
              /*
              if (res.Length - lastRet > 150) {
                res.Append('\n');
                lastRet = res.Length;
              }
               */
              pos++;
            }
            result = res.ToString();
          }
        } else {
          if (lines.Count > 0)
            Console.WriteLine("not enough lines: {0}", quant.Qid);
          result = null;
        }
      } else {
        result = null;
      }
      if (result != null)
        quant.Body = result.Trim();
    }


    Term GetTerm(string key)
    {
      if (key == ";") return null;
      key = RemoveParen(key);
      if (!model.terms.ContainsKey(key)) {
        model.terms[key] = new Term(key, EmptyTerms);
      }
      return model.terms[key];
    }

    private static string RemoveParen(string key)
    {
      if (key[key.Length - 1] == ')')
        key = key.Replace(")", "");
      return key;
    }

    Term[] GetArgs(int off, string[] words)
    {
      if (words.Length <= off)
        return EmptyTerms;
      Term[] args = new Term[words.Length - off];
      for (int i = 0; i < args.Length; ++i)
        args[i] = GetTerm(words[i + off]);
      return args;
    }

    public void ComputeCost()
    {
      if (eofSeen == 0 && beginCheckSeen <= 1) {
        Console.WriteLine("Warning: no [eof] marker found; log might be incomplete");
      }

      for (int i = model.instances.Count - 1; i >= 0; i--) {
        Instantiation inst = model.instances[i];
        int deps = 0;
        foreach (Term t in inst.Responsible) {
          if (t.Responsible != null) deps++;
        }
        foreach (Term t in inst.Responsible) {
          if (t.Responsible != null) {
            t.Responsible.Cost += inst.Cost / deps;
            t.Responsible.Quant.CrudeCost += inst.Cost / deps;
          }
        }
      }
    }

    private long GetId(string w)
    {
      return long.Parse(w.Substring(1));
    }

    private Term GetProofTerm(string w)
    {
      w = RemoveParen(w);
      if (w[0] == '#') {
        long id = GetId(RemoveParen(w));
        Common tmp;
        if (model.proofSteps.TryGetValue(id, out tmp) && tmp is Term) {
          return (Term)tmp;
        }
      }
      return new Term(w, EmptyTerms);
    }


    char[] sep = { ' ', '\r', '\n' };

    public void ParseSingleLine(string line)
    {
      curlineNo++;
      if (line == "") return;

      if (beginCheckSeen > checkToConsider) return;

      //if ((curlineNo & 0xffff) == 0)
      //  Console.Write(".");

      if (line[line.Length - 1] == ' ') line = line.Substring(0, line.Length - 1);
      if (line.StartsWith("[unit-resolution") || line.StartsWith("[th-lemma"))
        line = "#0 := " + line;
      line = line.Replace("(not #", "(not_#");
      string[] words = line.Split(sep, StringSplitOptions.RemoveEmptyEntries);

      try {
        if (ParseProofStep(words)) return;
        if (ParseModelLine(words)) return;
        ParseTraceLine(line, words);
      } catch (Exception) {
        Console.WriteLine("Exception when parsing: '{0}'", line);
        throw;
      }
    }

    bool modelInState = false;

    private bool ParseModelLine(string[] words)
    {
      if (words.Length == 1) {
        switch (words[0]) {
          case "}":
            currentFun = null;
            return true;
          case "partitions:": // V1
          case "Counterexample:":
            model.NewModel();
            return true;
          case ".":
          case "END_OF_MODEL":
            eofSeen++;
            return true;
        }
        if (model.IsV1Part(words[0])) return true;
        return false;
      }

      if (words[0] == "***") {
        switch (words[1]) {
          case "MODEL":
            model.NewModel();
            return true;
          case "END_MODEL":
            eofSeen++;
            modelInState = false;
            return true;
          case "STATE":
            modelInState = true;
            return true;
        }
      }

      if (modelInState) return true;

      switch (words[0]) {
        case "labels:":
        case "Z3":
        case "function":
          return true;
      }

      if (currentFun == null && model.IsV1Part(words[0]) && (words.Length < 3 || words[2] != "{")) {
        return ParseV1ModelLine(words);
      }

      if (words.Length < 3) return false;
      return DoParseModelLine(words);
    }

    private bool DoParseModelLine(string[] words)
    {
      if (words[words.Length - 2] != "->") return false;
      if (currentFun != null) {
        if (words[0] == "else") return true;
        FunApp fapp = new FunApp();
        fapp.Args = new Partition[words.Length - 2];
        for (int i = 0; i < fapp.Args.Length; ++i)
          fapp.Args[i] = model.PartitionByName(words[i]);
        fapp.Value = model.PartitionByName(words[words.Length - 1]);
        fapp.Fun = currentFun;
        currentFun.Apps.Add(fapp);
        fapp.Value.Values.Add(fapp);
        return true;
      } else if (words.Length == 3) {
        FunSymbol fs = model.FunSymbolByName(words[0]);
        if (words[2] == "{") {
          currentFun = fs;
        } else {
          FunApp fapp = new FunApp();
          fapp.Args = new Partition[0];
          fapp.Fun = fs;
          fapp.Value = model.PartitionByName(words[words.Length - 1]);
          fs.Apps.Add(fapp);
          fapp.Value.Values.Add(fapp);
        }
        return true;
      } else {
        return false;
      }
    }

    private bool ParseV1ModelLine(string[] words)
    {
      if (words.Length == 1) return true;
      for (int i = 0; i < words.Length; ++i)
        words[i] = words[i].Replace("{", "").Replace("}", "").Replace(":int", "");
      int end = words.Length;
      string val = null;
      if (end - 2 > 0 && words[end - 2] == "->") {
        end--;
        val = words[end];
        end--;
      }
      string[] tmp = new string[3];
      tmp[1] = "->";
      int err = 0;
      if (val != null) {
        Partition part = model.PartitionByName(val);
        model.modelPartsByName[words[0]] = part;
        tmp[2] = val;
      } else {
        tmp[2] = words[0];
      }
      for (int i = 1; i < end; ++i) {
        tmp[0] = words[i];
        if (!DoParseModelLine(tmp)) err++;
      }
      return err == 0;
    }

    public delegate bool Predicate2<T, S>(T t, S s);

    static public bool ForAll2<T, S>(T[] a1, S[] a2, Predicate2<T, S> pred)
    {
      if (a1.Length != a2.Length)
        throw new System.ArgumentException();
      for (int i = 0; i < a1.Length; ++i)
        if (!pred(a1[i], a2[i])) return false;
      return true;
    }

    private string[] StripGeneration(string[] words, out int x)
    {
      x = -1;
      if (words.Length > 3 && words[words.Length - 2] == ";") {
        string[] copy = new string[words.Length - 2];
        Array.Copy(words, copy, copy.Length);
        x = int.Parse(words[words.Length - 1]);
        return copy;
      }
      return words;
    }

    internal static Term Negate(Term a)
    {
      if (a.Name == "not")
        return a.Args[0];
      else
        return new Term("not", new Term[] { a });
    }

    internal static Term[] NegateAll(Term[] oargs)
    {
      Term[] args = new Term[oargs.Length];
      for (int i = 0; i < args.Length; ++i) {
        args[i] = Negate(oargs[i]);
      }
      return args;
    }

    private void ParseTraceLine(string line, string[] words)
    {
      switch (words[0]) {
        case "[mk-quant]":
          {
            Term[] args = GetArgs(3, words);

            /*
              if (words[2] == "not" && args[0].Name == "or") {
                words[2] = "And";
                args = NegateAll(args[0].Args);
              } 
             */

            Term t = new Term("FORALL" + words[1], args);
            model.terms[words[1]] = t;

            if (args.Length != 0)
            {
              Quantifier q = CreateQuantifier(words[1], words[2]);
              q.BodyTerm = t;
              if (words[2] != "null")
                q.PrintName = words[2] + "[" + words[1] + "]";
              else
                q.PrintName = words[1];
              q.ComputeBody();
            }
          } break;

        case "[mk-app]": {
            Term[] args = GetArgs(3, words);

          /*
            if (words[2] == "not" && args[0].Name == "or") {
              words[2] = "And";
              args = NegateAll(args[0].Args);
            } 
           */

            Term t = new Term(words[2], args);
            model.terms[words[1]] = t;
          } break;

        case "[attach-enode]": {
            Term t = GetTerm(words[1]);
            int gen = int.Parse(words[2]);
            if (lastInst != null && t.Responsible != lastInst) {
              // make a copy of the term, if we were going to override the Responsible field
              t = new Term(t);
              model.terms[words[1]] = t;
            }
            if (lastInst != null)
              t.Responsible = lastInst;
          }  break;
        
        case "[new-match]": {
            if (!interestedInCurrentCheck) break;
            if (words.Length < 3) break;
            Instantiation inst = new Instantiation();
            Term[] args = GetArgs(3, words);
            int firstNull = Array.IndexOf(args, null);
            if (firstNull < 0) {
              inst.Bindings = args;
              inst.Responsible = EmptyTerms;
            } else {
              inst.Bindings = new Term[firstNull];
              inst.Responsible = new Term[args.Length - firstNull - 1];
              Array.Copy(args, 0, inst.Bindings, 0, inst.Bindings.Length);
              Array.Copy(args, firstNull + 1, inst.Responsible, 0, inst.Responsible.Length);
            }

            inst.Quant = CreateQuantifier(words[2], words[2]);
            model.fingerprints[words[1]] = inst;
          } break;

        case "[instance]": {
            if (!interestedInCurrentCheck) break;
            Instantiation inst;
            if (!model.fingerprints.TryGetValue(words[1], out inst)) {
              System.Console.WriteLine("fingerprint not found {0} {1}", words[0], words[1]);
              break;
            }
            // model.fingerprints.Remove(words[1]);
            if (inst.LineNo != 0) {
              var tmp = new Instantiation();
              inst.CopyTo(tmp);
              inst = tmp;
            }
            AddInstance(inst);
            int pos = 2;
            if (words.Length > pos && words[pos] != ";") {
              long id = GetId(words[pos]);
              model.proofSteps[id] = inst;
              pos++;
            }
            if (words.Length - 1 > pos && words[pos] == ";") {
              ++pos;
              inst.Z3Generation = int.Parse(words[pos]);
              ++pos;
            } else {
              inst.Z3Generation = -1;
            }
          } break;
        case "[end-of-instance]": lastInst = null; break;


        case "[decide-and-or]":
          if (!interestedInCurrentCheck) break;
          if (words.Length >= 2)
            decideClause = GetTerm(words[1]);
          break;

        // we're getting [assign] anyhow
        case "[decide]": break;

        case "[assign]": {
            if (!interestedInCurrentCheck) break;
            if (skipDecisions || words.Length < 2) break;
            ScopeDesc d = model.scopes[model.scopes.Count - 1];
            Literal l = GetLiteral(words[1], false);
            if (d.Literal == null)
              d.Literal = l;
            else
              d.Implied.Add(l);
            int pos = 2;
            if (pos < words.Length && words[pos] == "decision")
              pos++;
            if (pos < words.Length) {
              string kw = words[pos++];
              switch (kw) {
                case "clause":
                case "bin-clause":
                  Term[] expl = new Term[words.Length - pos];
                  for (int i = 0; i < expl.Length; ++i)
                    expl[i] = GetLiteralTerm(words[pos++]);
                  l.Explanation = expl;
                  break;
                case "justification": break;
                default:
                  if (kw != "axiom") 
                    l.Explanation = new Term[] { GetTerm(kw) };
                  break;
              }
            }
          } break;

        case "[push]":
          if (!interestedInCurrentCheck) break;
          if(!skipDecisions)
            model.PushScope();
          break;

        case "[pop]":
          if (!interestedInCurrentCheck) break;
          if (skipDecisions || words.Length < 2) break;
          model.PopScopes(int.Parse(words[1]), curConfl);
          curConfl = null;
          break;

        case "[begin-check]":
          beginCheckSeen++;
          interestedInCurrentCheck = checkToConsider == beginCheckSeen;
          if (beginCheckSeen > 1 && checkToConsider == 1)
            Console.WriteLine("More than a single search log in the file, sticking to the first one; use /c:N option to override");
          break;

        case "[query-done]":
          if (interestedInCurrentCheck) eofSeen++;
          break;

        case "[eof]":
          eofSeen++;
          break;

        case "[resolve-process]":
          if (!interestedInCurrentCheck) break;
          if (skipDecisions || words.Length < 2) break;
          currResNode = new ResolutionLiteral();
          currResNode.Term = GetLiteralTerm(words[1], out currResNode.Negated, out currResNode.Id);
          if (currResRoot == null) {
            currResRoot = currResNode;
          } else {
            var t = currResRoot.Find(currResNode.Id);
            if (t != null)
              currResNode = t;
            else
              Console.WriteLine("cannot attach to conflict {0}", words[1]);
          }
          break;

        case "[resolve-lit]":
          if (!interestedInCurrentCheck) break;
          if (skipDecisions || words.Length < 3 || currResNode == null) break; 
          {
            var l = new ResolutionLiteral();
            l.Term = GetLiteralTerm(words[2], out l.Negated, out l.Id);
            l.LevelDifference = int.Parse(words[1]);
            currResNode.Results.Add(l);
          }
          break;

        case "[conflict]":
          if (!interestedInCurrentCheck) break;
          if (skipDecisions) break;
          curConfl = new Conflict();
          curConfl.Id = cnflCount++;
          curConfl.ResolutionLits = cnflResolveLits.ToArray();
          cnflResolveLits.Clear();
          curConfl.LineNo = curlineNo;
          curConfl.Cost = curlineNo;
          if (model.conflicts.Count > 0)
            curConfl.Cost -= model.conflicts[model.conflicts.Count - 1].LineNo;
          model.conflicts.Add(curConfl);
          curConfl.ResolutionRoot = currResRoot;
          currResRoot = null;
          currResNode = null;
          for (int i = 1; i < words.Length; ++i) {
            string w = words[i];
            Literal lit = GetLiteral(w,false);
            if (lit != null)
              curConfl.Literals.Add(lit);
          }
          break;

        // obsolete
        case "[mk-enode]":
        case "[mk-bool-var]": {
            int generation;

            if (words.Length < 3) break;
            words = StripGeneration(words, out generation);
            Term[] args = GetArgs(3, words);
            Term t;
            if (lastInst == null &&
                model.terms.TryGetValue(words[1], out t) &&
                t.Name == words[2] && t.Args.Length == args.Length &&
                ForAll2(t.Args, args, delegate(Term x, Term s) { return x == s; })) {
              // nothing
            } else {
              t = new Term(words[2], args);
              t.Responsible = lastInst;
              model.terms[words[1]] = t;
            }
          } break;

        // V1 stuff
        case "[create]": {
            if (words.Length < 4) break;
            Term[] args = GetArgs(4, words);
            Term t = new Term(args.Length == 0 ? words[3] : words[3].Substring(1), args);
            t.Responsible = lastInst;
            model.terms[words[1]] = t;
          } break;
        case "[fingerprint]": {
            if (words.Length < 3) break;
            Instantiation inst = new Instantiation();
            inst.Responsible = GetArgs(3, words);
            model.fingerprints[words[1]] = inst;
          } break;
        case "[mk_const]": if (words.Length < 2) break; model.terms.Remove("#" + words[1]); break;
        case "[create_ite]": if (words.Length < 2) break; model.terms.Remove("#" + words[1]); break;

        case "[done-instantiate-fp]": lastInst = null; break;
        case "[instantiate-fp]": {
            if (words.Length < 4) break;
            Instantiation inst;
            if (!model.fingerprints.TryGetValue(words[2], out inst)) {
              System.Console.WriteLine("fingerprint not found {0}", words[0]);
              break;
            }
            if (inst.Quant != null) {
              //Console.WriteLine("multi inst");
              break;
            }
            inst.Quant = CreateQuantifier(words[1], words[1]);
            AddInstance(inst);
            for (int i = 4; i < words.Length; ++i)
              words[i] = words[i].Substring(words[i].IndexOf(':') + 1);
            inst.Bindings = GetArgs(4, words);
          } break;
        case "[conflict-resolve]":
          if (!interestedInCurrentCheck) break;
          if (skipDecisions) break;
          cnflResolveLits.Add(GetLiteral(words[1], true));
          break;
        case "[conflict-lit]":
          if (curConfl != null && words.Length >= 2) {
            Literal lit = new Literal();
            curConfl.Literals.Add(lit);
            int pos = 1;
            if (words[pos] == "(not") {
              lit.Negated = true;
              pos++;
            }
            if (words.Length <= pos) break;
            string no = words[pos].Substring(1).Replace(":", "").Replace(")", "");
            if (!int.TryParse(no, out lit.Id))
              Console.WriteLine("cannot get literal number of {0}", no);
            pos++;
            if (words.Length <= pos) break;
            if (words[pos] == "not") pos++;
            if (words.Length <= pos) break;
            string sym = words[pos].Replace("(", "");
            pos++;
            if (sym != "FORALL") {
              for (int i = pos; i < words.Length; i++) {
                int idx = words[i].IndexOf(":");
                if (idx > 0) words[i] = words[i].Substring(0, idx);
              }
              lit.Term = new Term(sym, GetArgs(pos, words));
            }
          }
          break;
        case "[end-conflict]": break;


        case "[used]": break;
        case "WARNING:": break;
        default:
          Console.WriteLine("wrong line: '{0}'", line);
          break;
      }
    }

    private bool ParseProofStep(string[] words)
    {
      if (words.Length >= 3 && words[0].Length >= 2 && words[0][0] == '#' && words[1] == ":=") {
        long id = GetId(words[0]);
        if (words[2][0] == '(') {
          if (words.Length == 3 && words[2].StartsWith("(not_"))
            words = new string[] { words[0], words[1], "(not", words[2].Substring(5) };          
          Term[] args = new Term[words.Length - 3];
          for (int i = 0; i < args.Length; ++i)
            args[i] = GetProofTerm(words[i + 3]);
          model.proofSteps[id] = new Term(words[2].Substring(1), args);
        } else if (words[2][0] == '[') {
          string name = words[2].Substring(1);
          List<Common> proofArgs = new List<Common>();
          int pos = 3;

          Common prevInst;
          if (name == "quant-inst]:" && model.proofSteps.TryGetValue(id, out prevInst))
            proofArgs.Add(prevInst);

          if (words[2].Contains("]:")) {
            name = name.Substring(0, name.Length - 2);
          } else {
            while (pos < words.Length) {
              string cur = words[pos];
              if (cur.Contains("]:"))
                cur = cur.Substring(0, cur.Length - 2);
              Common tmp;
              if (model.proofSteps.TryGetValue(GetId(cur), out tmp))
                proofArgs.Add(tmp);
              else {
                Console.WriteLine("missing proof step: " + cur);
              }
              if (words[pos++].Contains("]:")) break;
            }
          }
          ProofRule res = new ProofRule();
          res.Name = name;
          res.Premises = proofArgs.ToArray();
          if (pos < words.Length)
            res.Consequent = GetProofTerm(words[pos]);
          model.proofSteps[id] = res;
        } else {
          model.proofSteps[id] = new Term(words[2], EmptyTerms);
        }
        return true;
      } else {
        return false;
      }
    }

    private Term GetLiteralTerm(string w, out bool negated, out int id)
    {
      id = 0;
      negated = false;
      if (w.Length < 2) return null;

      switch (w[0]) {
        case '-':
          negated = true;
          goto case '+';
        case '+':
          w = w.Substring(1);
          break;
        case '#':
          break;
        case '(':
          if (w.StartsWith("(not_#")) {
            w = w.Substring(5, w.Length - 6);
            negated = true;
          }
          break;
      }
      if (w[0] == '#')
        id = int.Parse(w.Substring(1));
      return GetTerm(w);
    }

    private Literal GetLiteral(string w, bool reuse)
    {
      Literal lit = new Literal();
      lit.Term = GetLiteralTerm(w, out lit.Negated, out lit.Id);

      var id = lit.Id;
      if (lit.Negated) id = -id;

      if (reuse) {
        Literal tmp;
        if (literalById.TryGetValue(id, out tmp))
          return tmp;
      }

      literalById.TryGetValue(-id, out lit.Inverse);
      if (lit.Inverse != null && lit.Inverse.Inverse == null) lit.Inverse.Inverse = lit;
      literalById[id] = lit;

      lit.Clause = this.decideClause;
      this.decideClause = null;
      return lit;
    }

    private Term GetLiteralTerm(string w)
    {
      Literal l = GetLiteral(w, true);
      if (l.Negated) {
        if (l.Term.NegatedVersion == null)
          l.Term.NegatedVersion = new Term("not", new Term[] { l.Term });
        return l.Term.NegatedVersion;
      } else {
        return l.Term;
      }
    }

    private void AddInstance(Instantiation inst)
    {
      Quantifier quant = inst.Quant;
      inst.LineNo = curlineNo;
      lastInst = inst;
      inst.Cost = 1.0;
      quant.Instances.Add(inst);
      model.quantifierInstantiations.Add(quant);
      model.AddInstance(inst);
      foreach (Term t in inst.Responsible)
        if (t.Responsible != null) {
          t.Responsible.Dependants.Add(inst);
        }
    }

    private Quantifier CreateQuantifier(string name, string qid)
    {
      Quantifier quant;
      if (!model.quantifiers.TryGetValue(name, out quant)) {
        quant = new Quantifier();
        quant.Qid = qid;
        quant.Instances = new List<Instantiation>();
        model.quantifiers[name] = quant;

        loadBoogieToken(quant);
      }
      return quant;
    }


  }


}
