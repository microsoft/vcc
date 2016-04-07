//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Text;

namespace Z3AxiomProfiler.QuantifierModel
{

  public class Model
  {
    public Dictionary<string, Term> terms = new Dictionary<string, Term>();
    public Dictionary<string, Quantifier> quantifiers = new Dictionary<string, Quantifier>();
    public Dictionary<string, Instantiation> fingerprints = new Dictionary<string, Instantiation>();
    public List<Quantifier> quantifierInstantiations = new List<Quantifier>(); // TODO use instances instead, as they have more info
    public List<Instantiation> instances = new List<Instantiation>();
    public List<Conflict> conflicts = new List<Conflict>();

    public List<FunSymbol> modelFuns = new List<FunSymbol>();
    public Dictionary<string, FunSymbol> modelFunsByName = new Dictionary<string, FunSymbol>();
    public Dictionary<string, Partition> modelPartsByName = new Dictionary<string, Partition>();
    public List<Common> models = new List<Common>();

    public Dictionary<long, Common> proofSteps = new Dictionary<long, Common>();

    public List<ScopeDesc> scopes = new List<ScopeDesc>();
    public Scope rootScope;
    public string LogFileName;

    internal static Literal MarkerLiteral = new Literal();

    public Model()
    {
      MarkerLiteral.Id = -13;
      MarkerLiteral.Term = new Term("marker", new Term[] { });
      PushScope();
    }

    public List<Quantifier> GetQuantifiersSortedByInstantiations()
    {
      List<Quantifier> qList = new List<Quantifier>();
      foreach (Quantifier q in quantifiers.Values) {
        qList.Add(q);
      }
      qList.Sort(delegate(Quantifier q1, Quantifier q2) { return q2.Cost.CompareTo(q1.Cost); });
      return qList;
    }

    public List<Quantifier> GetQuantifiersSortedByOccurence()
    {
      return quantifierInstantiations;
    }

    public void PushScope()
    {
      ScopeDesc d = new ScopeDesc();
      scopes.Add(d);
    }

    public void AddInstance(Instantiation inst)
    {
      instances.Add(inst);
      scopes[scopes.Count - 1].InstanceCount++;
    }

    public void PopScopes(int n, Conflict cnfl)
    {
      Debug.Assert(n <= scopes.Count - 1);

      Scope cur = new Scope();
      cur.lev = -(scopes.Count - n - 1);
      cur.Conflict = cnfl;
      for (int i = scopes.Count - 1; i >= scopes.Count - n; --i) {
        if (scopes[i].Scope != null) {
          scopes[i].Scope.AddChildScope(cur);
          cur = scopes[i].Scope;
        }
        cur.OwnInstanceCount += scopes[i].InstanceCount;
        Literal l = scopes[i].Literal;
        if (l != null) {
          l.Implied = new Literal[scopes[i].Implied.Count];
          scopes[i].Implied.CopyTo(l.Implied);
          cur.Literals.Add(l);
          foreach (var x in l.Implied)
            x.Cause = l;
        }
      }
      scopes.RemoveRange(scopes.Count - n, n);

      int end = scopes.Count - 1;
      if (scopes[end].Scope == null) {
        scopes[end].Scope = new Scope();
        scopes[end].Scope.lev = end;
      }
      scopes[end].Scope.AddChildScope(cur);
      scopes[end].Implied.Add(MarkerLiteral);
    }

    public Common SetupImportantInstantiations()
    {
      List<Common> res = new List<Common>();
      if (this.proofSteps.ContainsKey(0)) {
        List<ImportantInstantiation> roots = new List<ImportantInstantiation>();
        List<ImportantInstantiation> allUsed = new List<ImportantInstantiation>();
        List<Quantifier> quantsByMaxDepth = new List<Quantifier>();
        List<Common> quantLabels = new List<Common>();
        res.Add(Common.Callback("QUANTS BY MAX USEFUL DEPTH", delegate() { return quantLabels; }));
        res.Add(Common.Callback("ALL PROOF INSTS", delegate() { return allUsed; }));
        CollectInsts((ProofRule)proofSteps[0]);
        foreach (var imp in importants.Values) {
          if (imp.DepCount == 0)
            roots.Add(imp);
          imp.Quant.UsefulInstances++;
          if (imp.UseCount > 0) allUsed.Add(imp);
        }
        roots.Sort(delegate(ImportantInstantiation i1, ImportantInstantiation i2) { return i2.WDepth.CompareTo(i1.WDepth); });

        foreach (var r in roots) ComputeMaxDepth(r);

        foreach (var q in quantifiers.Values) {
          if (q.MaxDepth > 0)
            quantsByMaxDepth.Add(q);
        }
        quantsByMaxDepth.Sort(delegate(Quantifier q1, Quantifier q2) { 
          if(q1.MaxDepth == q2.MaxDepth)
            return q2.UsefulInstances.CompareTo(q1.UsefulInstances); 
          else
            return q2.MaxDepth.CompareTo(q1.MaxDepth);
        });
        foreach (var q in quantsByMaxDepth)
          quantLabels.Add(new ForwardingNode(q.MaxDepth + "   " + q.UsefulInstances + "    " + q.ToString(), q));

        importants.Clear();
        visitedRules.Clear();
        foreach (var r in roots)
          res.Add(r);
      }
      return Common.Callback("PROOF-INST", delegate() { return res; });
    }

    private void ComputeMaxDepth(ImportantInstantiation imp)
    {
      Quantifier q = imp.Quant;
      q.CurDepth++;
      if (q.CurDepth > q.MaxDepth)
        q.MaxDepth = q.CurDepth;
      foreach (var ch in imp.ResponsibleInsts)
        ComputeMaxDepth(ch);
      q.CurDepth--;
    }

    private Dictionary<Instantiation, ImportantInstantiation> importants = new Dictionary<Instantiation, ImportantInstantiation>();
    private Dictionary<ProofRule, bool> visitedRules = new Dictionary<ProofRule, bool>();

    private void CollectInsts(ProofRule prf)
    {
      if (visitedRules.ContainsKey(prf)) return;
      visitedRules.Add(prf, true);
      if (prf.Name == "quant-inst") {
        ImportantInstantiation imp = AddInst((Instantiation)prf.Premises[0]);
        imp.UseCount++;
      }
      foreach (var p in prf.Premises) {
        ProofRule pr = p as ProofRule;
        if (pr != null) CollectInsts(pr);
      }
    }

    private ImportantInstantiation AddInst(Instantiation instantiation)
    {
      ImportantInstantiation imp;
      if (importants.TryGetValue(instantiation, out imp)) return imp;

      imp = new ImportantInstantiation(instantiation);
      importants.Add(instantiation, imp);
      foreach (var t in instantiation.Responsible) {
        if (t.Responsible != null) {
          ImportantInstantiation x = AddInst(t.Responsible);
          imp.ResponsibleInsts.Add(x);
          x.DepCount++;
        }
      }
      return imp;
    }

    public bool IsV1Part(string fn)
    {
      int dummy;
      return fn.StartsWith("*") && int.TryParse(fn.Substring(1), out dummy);
    }

    public virtual int FunAppBadness(FunApp f)
    {
      // TODO read rules from file

      string fn = f.Fun.Name;
      switch (fn) {
        case "$ghost_emb":
        case "$int_to_ptrset":
        case "$int_to_ptr":
          return 100;

        case "$array":
        case "$ptr":
          return 40;
        case "$phys_ptr_cast":
        case "$spec_ptr_cast":
        case "$field_plus":
          return 35;
        case "$idx_prim":
        case "$dot":
          return 30;
        case "$read_ptr_m":
          return 35;

        default:
          if (fn.StartsWith("#distTp"))
            return 100;
          if (fn.StartsWith("$st_"))
            return 60;

          // general
          if (fn.StartsWith("unique-value!"))
            return 100;
          if (fn.StartsWith("val!") || IsV1Part(fn))
            return 200;
          if (fn.StartsWith("call") && (fn.Contains("formal@") || fn.Contains("formal_")))
            return 100;

          if (f.Args.Length == 0) return 20;

          return f.Args.Length + 50;
      }
    }

    bool IsModelConstant(string s)
    {
      if (s == "true" || s == "false") return true;

      if (s.Length == 0) return false;
      if (!Char.IsDigit(s[0]) && s[0]!='-') return false;
      for (int i = 1; i < s.Length; ++i)
        if (!Char.IsDigit(s[i])) return false;
      return true;
    }

    public void NewModel()
    {
      var copy = modelFuns;
      if (copy.Count > 0)
        models.Add(new CallbackNode("MODEL #" + models.Count, delegate() { return this.ModelKids(copy); }));
      modelFuns = new List<FunSymbol>();
      modelFunsByName.Clear();
      modelPartsByName.Clear();
    }

    public FunSymbol FunSymbolByName(string name)
    {
      FunSymbol fn;
      if (modelFunsByName.TryGetValue(name, out fn)) return fn;
      fn = new FunSymbol();
      fn.Name = name;
      fn.AllSymbols = this.modelFuns;
      this.modelFuns.Add(fn);
      modelFunsByName.Add(name, fn);
      return fn;
    }


    public Partition PartitionByName(string name)
    {
      Partition part;
      if (modelPartsByName.TryGetValue(name, out part))
        return part;
      part = new Partition();
      part.Id = name;
      part.model = this;
      modelPartsByName.Add(name, part);

      FunSymbol consts = FunSymbolByName(name);
      FunApp fapp = new FunApp();
      fapp.Fun = consts;
      fapp.Args = new Partition[0];
      fapp.Value = part;
      consts.Apps.Add(fapp);
      part.Values.Add(fapp);

      return part;
    }

    IEnumerable<Common> ModelKids(List<FunSymbol> allFuns)
    {
      List<FunSymbol> realFuns = new List<FunSymbol>();
      List<FunApp> literals = new List<FunApp>();
      List<FunApp> consts = new List<FunApp>();

      allFuns.Sort(delegate(FunSymbol f1, FunSymbol f2) { return string.CompareOrdinal(f1.Name, f2.Name); });
      foreach (var fs in allFuns) {
        if (fs.Apps.Count == 1 && fs.Apps[0].Args.Length == 0) {
          if (IsModelConstant(fs.Name))
            literals.Add(fs.Apps[0]);
          else if (FunAppBadness(fs.Apps[0]) < 100)
            consts.Add(fs.Apps[0]);
        } else {
          //if (!IsV1Part(fs.Name))
            realFuns.Add(fs);
        }
      }
      yield return Common.Callback("LITERALS", delegate() { return literals; });
      yield return Common.Callback("CONSTS", delegate() { return consts; });
      foreach (var c in realFuns) yield return c;
    }

  }

  public class ScopeDesc
  {
    public Scope Scope;
    public Literal Literal;
    public List<Literal> Implied = new List<Literal>();
    public int InstanceCount;
  }

  public abstract class Common
  {
    //public abstract void Expand(MainForm f, TreeNodeCollection coll);
    public virtual string ToolTip() { return ToString(); }
    public abstract IEnumerable<Common> Children();
    public virtual bool HasChildren() { return true; }
    public virtual bool AutoExpand() { return false; }
    public virtual int ForeColor() { return 0x000000; }

    public static IEnumerable<T> ConvertIEnumerable<T, S>(IEnumerable<S> x)
      where S : T
    {
      foreach (var y in x) yield return y;
    }

    public static CallbackNode Callback<T>(string name, MyFunc<IEnumerable<T>> fn)
      where T : Common
    {
      return new CallbackNode(name, delegate() { return ConvertIEnumerable<Common,T>(fn()); });
    }

    public static CallbackNode CallbackExp<T>(string name, IEnumerable<T> iter)
      where T : Common
    {
      List<T> cache = new List<T>(iter);
      var res = new CallbackNode(name + " [" + cache.Count + "]", delegate() { return ConvertIEnumerable<Common, T>(cache); });
      if (cache.Count <= 3)
        res.autoExpand = true;
      return res;
    }
  }

  public class ForwardingNode : Common
  {
    public Common Fwd;
    string name;

    public ForwardingNode(string n, Common c)
    {
      name = n;
      Fwd = c;
    }
    public override IEnumerable<Common> Children()
    {
      return Fwd.Children();
    }
    public override int ForeColor()
    {
      return Fwd.ForeColor();
    }
    public override bool HasChildren()
    {
      return Fwd.HasChildren();
    }
    public override string ToolTip()
    {
      return Fwd.ToolTip();
    }
    public override string ToString()
    {
      return name;
    }
  }

  public class LabelNode : Common
  {
    string name;

    public LabelNode(string s)
    {
      name = s;
    }

    public override IEnumerable<Common> Children()
    {
      yield break;
    }

    public override string ToString()
    {
      return name;
    }

    public override bool HasChildren()
    {
      return false;
    }
  }

  public delegate T MyFunc<T>();

  public class CallbackNode : Common
  {
    MyFunc<IEnumerable<Common>> callback;
    string name;
    internal bool autoExpand;

    public CallbackNode(string name, MyFunc<IEnumerable<Common>> cb)
    {
      this.name = name;
      callback = cb;
    }

    public override string ToString()
    {
      return name;
    }

    public override IEnumerable<Common> Children()
    {
      return callback();
    }

    public override bool AutoExpand()
    {
      return autoExpand;
    }
  }

  public class Scope : Common
  {
    public readonly List<Literal> Literals = new List<Literal>();
    public Literal[] ImpliedAtParent;
    public Conflict Conflict;
    public readonly List<Scope> ChildrenScopes = new List<Scope>();
    public int lev;
    public Scope parentScope;
    int recConflictCount = -1;
    int recInstanceCount = -1;
    int recInstanceDepth = -1;
    int maxConflictSize = 0;
    bool recInstanceCountComputed;
    int id = -1;
    int subid = 0;

    public int OwnInstanceCount;

    public int InstanceCount
    {
      get {
        if (recInstanceCountComputed) return recInstanceCount;
        recInstanceCountComputed = true;
        recInstanceCount = OwnInstanceCount;
        foreach (var c in ChildrenScopes)
          recInstanceCount += c.InstanceCount;
        return recInstanceCount;
      }
    }

    public string LastDecisionQID()
    {
      if (Conflict == null || Literals.Count == 0) return null;

      Literal l = Literals[Literals.Count - 1];
      if (l.Clause == null || l.Clause.Name != "or" || l.Clause.Args[0].Name != "not") return null;
      string qid = l.Clause.Args[0].Args[0].Name;
      return qid;
    }

    internal void AddChildScope(Scope s)
    {
      ChildrenScopes.Add(s);
      s.parentScope = this;
    }

    public int RecInstanceDepth
    {
      get
      {
        var dummy = RecConflictCount;
        return recInstanceDepth;
      }
    }

    public int RecConflictCount
    {
      get
      {
        if (recConflictCount >= 0) return recConflictCount;
        recConflictCount = 0;
        if (Conflict != null)
          maxConflictSize = Conflict.Literals.Count;
        foreach (var c in ChildrenScopes) {
          recConflictCount += c.RecConflictCount;
          if (c.maxConflictSize > maxConflictSize)
            maxConflictSize = c.maxConflictSize;
          if (c.recInstanceDepth > recInstanceDepth)
            recInstanceDepth = c.recInstanceDepth;
        }
        recInstanceDepth += OwnInstanceCount;
        if (Conflict != null) recConflictCount++;
        return recConflictCount;
      }
    }

    public override string ToString()
    {
      if (id == -1) {
        if (Conflict == null) {
          if (ChildrenScopes != null && ChildrenScopes.Count > 0) {
            ChildrenScopes[0].ToString();
            id = ChildrenScopes[0].id;
            subid = ChildrenScopes[0].subid + 1;
          } else {
            id = 0;
          }
        } else {
          id = Conflict.Id;
        }
      }

      string res = string.Format("Scope#{5}: {0} / {2} inst, {1} lits [{3}lev:{4}]", 
        InstanceCount, Literals.Count, OwnInstanceCount, lev <0 ? "f" : "", lev < 0 ? -lev : lev, 
        string.Format("{0}.{1}",id,subid));
      if(ChildrenScopes.Count > 0)
        res += string.Format(", {0} children [rec: {1}, {2} inst/cnfl]", 
                             ChildrenScopes.Count, RecConflictCount, 
                             (RecConflictCount == 0)? "inf" :
                             (InstanceCount/RecConflictCount).ToString());
      var dummy = RecConflictCount;
      if (maxConflictSize > 0)
        res += string.Format(" maxCnflSz: {0}", maxConflictSize);
      return res;
    }

    public override string ToolTip()
    {
      if (Conflict != null)
        return Conflict.ToolTip();
      else return "No conflict";
    }

    public void PropagateImpliedByChildren()
    {
      if (Literals.Count > 0) {
        int scopeNo = 0;
        int firstMarker = -1;
        int prevMarker = -1;
        var last = Literals[0];
        var lastImpl = last.Implied;

        for (int idx = 0; idx <= lastImpl.Length; ++idx) {
          if (idx == lastImpl.Length || lastImpl[idx] == Model.MarkerLiteral) {
            if (firstMarker < 0) firstMarker = idx;
            if (prevMarker >= 0) {
              var arr = new Literal[idx - prevMarker - 1];
              Array.Copy(lastImpl, prevMarker + 1, arr, 0, arr.Length);
              var scope = ChildrenScopes[scopeNo++];
              scope.ImpliedAtParent = arr;
              foreach (var l in arr)
                l.Cause = scope;
            }
            prevMarker = idx;
          }
        }
        if (!(scopeNo == ChildrenScopes.Count || scopeNo == ChildrenScopes.Count - 1))
          Debug.Fail("");

        if (scopeNo > 0) {
          last.Implied = new Literal[firstMarker];
          Array.Copy(lastImpl, last.Implied, firstMarker);
        }
      }

      foreach (var v in ChildrenScopes)
        v.PropagateImpliedByChildren();
    }

    public void AccountLastDecision(Model m)
    {
      string qid = this.LastDecisionQID();
      Quantifier q;
      if (qid != null && m.quantifiers.TryGetValue(qid, out q)) {
        q.GeneratedConflicts++;
      }
      foreach (var c in ChildrenScopes)
        c.AccountLastDecision(m);
    }

    public void ComputeConflictCost(List<Conflict> acc)
    {
      Literals.Reverse();

      int pos = acc.Count;
      foreach (var c in ChildrenScopes)
        c.ComputeConflictCost(acc);
      if (Conflict != null) acc.Add(Conflict);
      if (acc.Count == pos) return;
      double off = (double)OwnInstanceCount / (acc.Count - pos);
      if (off > 0)
        while (pos < acc.Count) {
          acc[pos].InstCost += off;
          pos++;
        }
    }

    public override IEnumerable<Common> Children()
    {
      yield return Callback("LITERALS [" + Literals.Count + "]", delegate() { return Literals; });
      if (Conflict != null)
        yield return Conflict;
      if (ImpliedAtParent != null)
        yield return Callback("AT PARENT [" + ImpliedAtParent.Length + "]", delegate() { return ImpliedAtParent; });
      foreach (var c in ChildrenScopes) {
        yield return c;
      }
    }
  }


  public class Quantifier : Common
  {
    public string Qid;
    public string PrintName;
    public string Body;
    public Term BodyTerm;
    public List<Instantiation> Instances;
    public double CrudeCost;

    public int CurDepth;
    public int MaxDepth;
    public int UsefulInstances;
    public int GeneratedConflicts;

    //public override void Expand(MainForm f, TreeNodeCollection coll)
    //{
    //    foreach (Instantiation i in Instances)
    //    {
    //        coll.Add(f.MakeNode(i));
    //    }
    //}

    public override string ToString()
    {
      if (PrintName == null) PrintName = Qid;
      string costFormat = String.Format("{0:0}         ", Cost).Substring(0, 9);
      return string.Format("{0:0} {1}  (direct: {2}, cnfl: {3})", costFormat, PrintName, Instances.Count, GeneratedConflicts);
    }

    public override string ToolTip()
    {
      ComputeBody();
      return Body;
    }

    public int Weight
    {
      get {
        // TODO
        if (Body.Contains("{:weight 0")) return 0;
        return 1;
      }
    }

    private Common TheMost(string tag, Comparison<Instantiation> cmp)
    {
      Instances.Sort(cmp);
      int len = 100;
      if (Instances.Count < len)
        len = Instances.Count;
      Common[] first = new Common[len];
      for (int i = 0; i < len; ++i)
        first[i] = Instances[i];
      return new CallbackNode(tag, delegate() { return first; });
    }

    public override IEnumerable<Common> Children()
    {
      Common[] theCommons = new Common[] {
      };

      /*
      if (Instances.Count < 20) {
        List<Instantiation> sortedInstantiationList = Instances;
        sortedInstantiationList.Sort(delegate(Instantiation i1, Instantiation i2) { return i2.Depth.CompareTo(i1.Depth); });
        return ConvertIEnumerable<Common,Instantiation>(sortedInstantiationList);
      } else { */

      if (BodyTerm == null)
        BodyTerm = new Term("?", new Term[] { });

        return new Common[] {
          //new LabelNode("Real cost " + RealCost),
          Callback("REAL COST", delegate() { return new Common[] { new LabelNode(RealCost + "") }; }),
          BodyTerm,
          TheMost("DEEP", delegate(Instantiation i1, Instantiation i2) { return i2.Depth.CompareTo(i1.Depth); }),
          TheMost("COSTLY", delegate(Instantiation i1, Instantiation i2) { return i2.Cost.CompareTo(i1.Cost); }),
          TheMost("FIRST", delegate(Instantiation i1, Instantiation i2) { return i1.LineNo.CompareTo(i2.LineNo); }),
          TheMost("LAST", delegate(Instantiation i1, Instantiation i2) { return i2.LineNo.CompareTo(i1.LineNo); }),
          Callback("ALL [" + Instances.Count + "]", delegate() { return Instances; }),
        };
    }

    public override int ForeColor()
    {
      if (Weight == 0)
        return 0x000088;
      return base.ForeColor();
    }

    private double InstanceCost(Instantiation inst, int lev)
    {
      if (lev != 0 && inst.Quant == this) return 0;
      double res = 1;
      foreach (var ch in inst.Dependants) {
        int cnt = 0;
        foreach (var other in ch.Responsible)
          if (other.Responsible != null) cnt++;
        res += InstanceCost(ch, lev + 1) / cnt;
      }
      return res;
    }

    private double realCost;
    public double RealCost
    {
      // this is slow
      get
      {
        if (realCost != 0) return realCost;
        foreach (var inst in this.Instances)
          realCost += InstanceCost(inst, 0);
        return realCost;
      }
    }

    public double Cost
    {
      get
      {
        //return RealCost;
        return CrudeCost + Instances.Count;
      }
    }

    internal void ComputeBody()
    {
      if (Body == null) {
        Body = "?";
        if (BodyTerm != null)
          Body = BodyTerm.ToString();
      }
    }
  }

  public class Instantiation : Common
  {
    public Quantifier Quant;
    public Term[] Bindings;
    public Term[] Responsible;
    public int LineNo;
    public double Cost;
    public List<Instantiation> Dependants = new List<Instantiation>();
    public int Z3Generation;
    int depth;
    int wdepth = -1;

    //void HandleParms(string pref, Term[] args, TreeNodeCollection coll)
    //{
    //    for (int i = 0; i < args.Length; ++i)
    //    {
    //        TreeNode nested = args[i].ToNestedNode();
    //        TreeNode[] children;
    //        if (nested.Nodes.Count == 0)
    //            children = new TreeNode[] { };
    //        else
    //            children = new TreeNode[] { nested };
    //        coll.Add(new TreeNode(pref + "  " + args[i].Stats + "  " +
    //                              args[i].ToString(),
    //                              children));
    //    }
    //}

    //public override void Expand(MainForm f, TreeNodeCollection coll)
    //{
    //    TreeNode info = new TreeNode("INFO");
    //    coll.Add(info);
    //    HandleParms("BIND", Bindings, info.Nodes);
    //    HandleParms("BLAME", Responsible, info.Nodes);
    //    foreach (Term t in Responsible)
    //    {
    //        if (t.Responsible != null)
    //            coll.Add(f.MakeNode(t.Responsible));
    //    }
    //}

    public void CopyTo(Instantiation inst)
    {
      inst.Quant = Quant;
      inst.Bindings = (Term[])Bindings.Clone();
      inst.Responsible = (Term[])Responsible.Clone();
    }

    public int Depth
    {
      get
      {
        if (depth == 0)
        {
          int max = 0;
          //depth = 1;
          foreach (Term t in Responsible)
          {
            if (t.Responsible != null)
            {
              if (t.Responsible.Depth > max) max = t.Responsible.Depth;
            }
          }
          depth = max + 1;
        }
        return depth;
      }
    }

    public int WDepth
    {
      get
      {
        if (wdepth == -1) {
          int max = 0;
          //depth = 1;
          foreach (Term t in Responsible) {
            if (t.Responsible != null) {
              if (t.Responsible.WDepth > max) max = t.Responsible.WDepth;
            }
          }
          wdepth = max + Quant.Weight;
        }
        return wdepth;
      }
    }



    public override string ToString()
    {
      StringBuilder s = new StringBuilder();
      s.Append(Quant.PrintName);
      int size = 0, depth = 0;
      foreach (Term t in Bindings)
      {
        size += t.Size;
        if (t.Depth > depth) depth = t.Depth;
      }
      s.AppendFormat("  {0} ({5}) / |{1}:{2}| @{3} {4:0.0} ", Depth, size, depth, LineNo, Cost, WDepth);
      foreach (Term t in Bindings)
      {
        s.Append("  ");
        s.Append(t.Desc);
      }
      if (s.Length > 500) s.Length = 500;
      return s.ToString();
    }

    public override string ToolTip()
    {
      Quant.ComputeBody();
      return Quant.Body;
    }

    public override IEnumerable<Common> Children()
    {
      if (Responsible != null) {
        List<Term> sortedResponsibleList = new List<Term>(this.Responsible);
        sortedResponsibleList.Sort(delegate(Term t1, Term t2)
        {
          int d1 = t1.Responsible == null ? 0 : t1.Responsible.Depth;
          int d2 = t2.Responsible == null ? 0 : t2.Responsible.Depth;
          return d2.CompareTo(d1);
        });
        foreach (Term t in sortedResponsibleList) {
          if (t.Responsible != null) {
            yield return t.Responsible;
          }
        }
        yield return Callback("BLAME", delegate() { return sortedResponsibleList; });
      }

      if (Bindings.Length > 0) {
        yield return Callback("BIND", delegate() { return Bindings; });
      }

      if (Dependants.Count > 0) {
        Dependants.Sort(delegate(Instantiation i1, Instantiation i2) { return i2.Cost.CompareTo(i1.Cost); });
        yield return Callback("YIELDS", delegate() { return Dependants; });
      }
    }
  }


  public class Term : Common
  {
    public string Name;
    public Term[] Args;
    public Instantiation Responsible;
    public int Size;
    public int Depth;
    public Term NegatedVersion;

    public Term(string name, Term[] args)
    {
      Name = String.Intern(name);
      Args = args;
      foreach (Term t in Args)
      {
        Size += t.Size;
        Depth = Depth > t.Depth ? Depth : t.Depth;
      }
      Size++;
      Depth++;
    }

    public Term(Term t)
    {
      Name = t.Name;
      Args = t.Args;
      Size = t.Size;
      Depth = t.Depth;
      Responsible = t.Responsible;
    }

    //public TreeNode ToNestedNode()
    //{
    //    if (Depth < 5)
    //        return new TreeNode(ToString());
    //    TreeNode[] children = new TreeNode[Args.Length];
    //    for (int i = 0; i < Args.Length; ++i)
    //        children[i] = Args[i].ToNestedNode();
    //    return new TreeNode(Desc, children);
    //}

    public string Sig
    {
      get { return Name + "/" + Args.Length; }
    }

    public void CWriteTo(StringBuilder s, bool states)
    {
      if (s.Length > 1096) return;

      if (Sig == "$ptr/2" && Args[1].Sig == "$ref/1")
      {
        if (states)
        {
          s.Append("((");
          Args[0].CWriteTo(s, states);
          s.Append(") ");
        }
        Args[1].Args[0].CWriteTo(s, states);
        if (states)
          s.Append(")");

      } else if ((Sig == "$select.mem/2" || Sig == "select1/2" || Sig == "$read_ptr_m/3") && Args[1].Sig == "$dot/2")
      {

        s.Append("(");
        Args[1].Args[0].CWriteTo(s, states);
        s.Append(")->");
        Args[1].Args[1].CWriteTo(s, states);
        if (states)
        {
          s.Append(" @ ");
          Args[0].CWriteTo(s, states);
        }
      }
      else if (Sig == "$read_ptr_m/3")
      {
        s.Append("*(");
        Args[1].CWriteTo(s, states);
        s.Append(")");
        if (states)
        {
          s.Append(" @ ");
          Args[0].CWriteTo(s, states);
        }
      }
      else if (Sig == "$dot/2")
      {
        s.Append("&(");
        Args[0].CWriteTo(s, states);
        s.Append(")->");
        Args[1].CWriteTo(s, states);
      }
      else if (Sig == "$ptr/2" && Args[1].Sig == "$ghost_ref/2")
      {
        s.Append("&(");
        Args[1].Args[0].CWriteTo(s, states);
        s.Append(")->");
        Args[1].Args[1].CWriteTo(s, states);
      }
      else if (Sig == "$ptr/2" && Args[1].Sig == "$st_ref_cnt_ptr/1" && Args[1].Args[0].Sig == "select1/2")
      {
        s.Append("&(");
        Args[1].Args[0].Args[1].CWriteTo(s, states);
        s.Append(")->ref_cnt");
        if (states)
        {
          s.Append(" @ ");
          Args[1].Args[0].Args[0].CWriteTo(s, states);
        }
      }
      else if (Sig == "$rev_ref_cnt_ptr/1" && Args[0].Sig == "$ptr/2" && Args[0].Args[1].Sig == "$st_ref_cnt_ptr/1" && Args[0].Args[1].Args[0].Sig == "select1/2")
      {
        s.Append("%");
        Args[0].Args[1].Args[0].Args[1].CWriteTo(s, states);
      }
      else if (Sig == "$ghost_emb/1" && Args[0].Sig == "$ghost_ref/2")
      {
        s.Append("%");
        Args[0].Args[0].CWriteTo(s, states);
      }
      else if (Sig.StartsWith("$select.$map") && Args.Length == 2) {
        Args[0].CWriteTo(s, states);
        s.Append("[");
        Args[1].CWriteTo(s, states);
        s.Append("]");
      }
      else if (Sig == "$ts_emb/1" && Args[0].Sig == "select1/2")
      {
        s.Append("(");
        Args[0].Args[1].CWriteTo(s, states);
        s.Append(")->$$emb");
        if (states)
        {
          s.Append(" @ ");
          Args[0].Args[0].CWriteTo(s, states);
        }
      }
      else if (Sig == "$emb/2")
      {
        s.Append("(");
        Args[1].CWriteTo(s, states);
        s.Append(")->$$emb");
        if (states)
        {
          s.Append(" @ ");
          Args[0].CWriteTo(s, states);
        }
      }
      else if (Sig == "$ptr/2" && !states)
      {
        Args[1].CWriteTo(s, states);
      }
      else if (Sig == "$owns_set_field/1")
      {
        s.Append("$owns");        
      }
      else if (Sig == "$index_within/2" && Args[0].Sig == "$idx/3" && Args[0].Args[0] == Args[1] && Args[0].Args[2].Sig == "$typ/1" && Args[0].Args[2].Args[0] == Args[1])
      {
        Args[0].Args[1].CWriteTo(s, states);
      } else if (Sig.StartsWith("MapType") && Sig.Contains("Select/")) {
        Args[0].CWriteTo(s, states);
        s.Append("[");
        for (int i = 1; i < Args.Length; ++i) {
          if (i != 1) s.Append(", ");
          Args[i].CWriteTo(s, states);
        }
        s.Append("]");
      } else if (Sig.EndsWith("/1") && Name.StartsWith("U_2_")) {
        Args[0].CWriteTo(s, states);
      } else {
        s.Append(Name);
        if (Args.Length == 0) return;
        s.Append('(');
        for (int i = 0; i < Args.Length; ++i) {
          if (i != 0) s.Append(", ");
          Args[i].CWriteTo(s, states);
        }
        s.Append(')');
      }
    }

    public string AsCString(bool states)
    {
      StringBuilder sb = new StringBuilder("C: ");
      CWriteTo(sb, states);
      return sb.ToString();
    }

    public void WriteTo(StringBuilder s)
    {
      if (s.Length > 1096) return;
      s.Append(Name);
      if (Args.Length == 0) return;
      s.Append('(');
      for (int i = 0; i < Args.Length; ++i)
      {
        if (i != 0) s.Append(", ");
        Args[i].WriteTo(s);
      }
      s.Append(')');
    }

    public override string ToString()
    {
      StringBuilder b = new StringBuilder();
      WriteTo(b);
      return b.ToString();
    }

    public string Desc
    {
      get
      {
        return Name + " |" + Size + ":" + Depth + "|";
      }
    }

    public string Stats
    {
      get { return Size + ":" + Depth; }
    }

    public override string ToolTip()
    {
      return string.Format("{0}\n\n{1}", ToString(), AsCString(false));
    }

    public override bool HasChildren()
    {
      return (Args.Length > 0) && (Size > 3);      
    }

    public override IEnumerable<Common> Children()
    {
      //yield return new LabelNode(AsCString(true));
      foreach (Term t in Args) {
        yield return t;
      }
    }
  }


  public class Literal : Common
  {
    public bool Negated;
    public Term Term;
    public int Id;
    public Term Clause;
    public Term[] Explanation;
    public Common Cause;
    public Literal Inverse;
    public Literal[] Implied;

    public override string ToString()
    {
      string t;
      bool isBin = Term.Args.Length == 2;

      if (Negated && Term.Name == "or") {
        Negated = false;
        Term = new Term("And", LogProcessor.NegateAll(Term.Args));
      }

      if (isBin)
        foreach (char c in Term.Name) {
          if (Char.IsLetterOrDigit(c)) {
            isBin = false;
            break;
          }
        }

      if (Term == null) t = "(nil)";
      else if (isBin)
      {
        t = string.Format("{0}  {1}  {2}", Term.Args[0].AsCString(false), Term.Name, Term.Args[1].AsCString(false));
      }
      else
      {
        t = Term.AsCString(false);
      }
      return string.Format("{0}p{1}  {3}{2}", Negated ? "~" : "", Id, t, Implied == null ? "" : "[+" + Implied.Length + "] ");
    }

    public override IEnumerable<Common> Children()
    {
      if (Term != null) 
        yield return Term;
      if (Explanation != null) {
        yield return Common.Callback("EXPLANATION [" + Explanation.Length + "]", () => Explanation);
      }
      if (Clause != null) {
        yield return new LabelNode("FROM CLAUSE:");
        yield return Clause;
      }
      if (Cause != null)
        yield return Callback("CAUSE", () => new Common[] { Cause });
      if (Inverse != null)
        yield return Callback("INVERSE", () => new Common[] { Inverse });
      if (Implied != null && Implied.Length > 0)
        yield return Callback("IMPLIED [" + Implied.Length + "]", () => Implied);
    }

    public override int ForeColor()
    {
      if (Clause != null)
        return 0x995555;
      else return base.ForeColor();
    }
  }

  public class ResolutionLiteral : Literal
  {
    public List<ResolutionLiteral> Results = new List<ResolutionLiteral>();
    public int LevelDifference;

    public override IEnumerable<Common> Children()
    {
      //foreach (var e in base.Children()) yield return e;
      foreach (var e in Results) yield return e;
    }

    public override int ForeColor()
    {
      if (LevelDifference == 0)
        return 0x995555;
      else return base.ForeColor();
    }

    public override bool HasChildren()
    {
      return Results.Count > 0;
    }
    public ResolutionLiteral Find(int id)
    {
      if (this.Id == id) return this;
      foreach (var c in Results) {
        var r = c.Find(id);
        if (r != null) return r;
      }
      return null;
    }
  }

  public class Conflict : Common
  {
    public List<Literal> Literals = new List<Literal>();
    public Literal[] ResolutionLits;
    public int LineNo;
    public int Id;
    public int Cost;
    public double InstCost;
    public ResolutionLiteral ResolutionRoot;

    public bool Useful
    {
      get
      {
        foreach (Literal l in Literals)
          if (l.Term != null) return true;
        return false;
      }
    }

    public void PrintAsCsv(StringBuilder sb, int id)
    {
      sb.AppendFormat("{0},{1},{2},{3}", id++, LineNo, Cost, Literals.Count);
      foreach (var l in Literals)
        sb.AppendFormat(",\"{0}\"", l.ToString());
      sb.Append("\r\n");
    }

    public static StringBuilder CsvHeader()
    {
      return new StringBuilder("#,Line#,LineDelta (Cost),#Lits,Lits\r\n");
    }

    public override string ToString()
    {
      return string.Format("Confl#{3} {0} lits, {1:0} ops {2:0} inst", Literals.Count, Cost / 100.0, InstCost, Id);
         
    }

    public override string ToolTip()
    {
      StringBuilder sb = new StringBuilder();
      foreach (Literal l in Literals)
      {
        sb.Append(l.ToString()).Append("\n");
      }
      return sb.ToString();
    }

    public override IEnumerable<Common> Children()
    {
      if (ResolutionLits.Length > 0)
        yield return Common.Callback("RESOLVED FROM", () => ResolutionLits);
      if (ResolutionRoot != null)
        yield return Common.Callback("RESOLVED FROM", () => new Common[] { ResolutionRoot });
      yield return Common.Callback("CAUSES", delegate()
      {
        var r = new List<Common>();
        foreach (var l in Literals) {
          if (l.Inverse != null) {
            if (l.Inverse.Clause != null)
              r.Add(l.Inverse);
            else if (l.Inverse.Cause != null)
              r.Add(l.Inverse.Cause);
          }
        }
        return r;
      });
      foreach (var l in Literals)
        yield return l;
    }
  }


  public class ProofRule : Common
  {
    public string Name;
    public Common[] Premises;
    public Term Consequent;

    public override string ToString()
    {
      return Name;
    }

    public override IEnumerable<Common> Children()
    {
      yield return Consequent;
      foreach (var p in Premises)
        yield return p;
    }
  }

  public class ImportantInstantiation : Instantiation
  {
    public int UseCount;
    public int DepCount;
    public List<ImportantInstantiation> ResponsibleInsts = new List<ImportantInstantiation>();

    public ImportantInstantiation(Instantiation par)
    {
      Quant = par.Quant;
      Bindings = par.Bindings;
      Responsible = par.Responsible;
      LineNo = par.LineNo;
      Cost = par.Cost;
      Z3Generation = par.Z3Generation;
    }

    public override IEnumerable<Common> Children()
    {
      if (ResponsibleInsts != null) {
        ResponsibleInsts.Sort(delegate(ImportantInstantiation i1, ImportantInstantiation i2)
        {
          if (i1.WDepth == i2.WDepth) return i2.Depth.CompareTo(i1.Depth);
          else return i2.WDepth.CompareTo(i1.WDepth);
        });
        foreach (var i in ResponsibleInsts)
          yield return i;
        yield return Callback("BLAME", delegate() { return Responsible; });
      }
      if (Bindings.Length > 0) {
        yield return Callback("BIND", delegate() { return Bindings; });
      }
    }

    public override int ForeColor()
    {
      if (Quant.Weight == 0)
        return 0x888888;
      //if (UseCount > 0)
      //  return 0x008800;
      else
        return base.ForeColor();
    }
  }


  // --------------------------------------------------------------------------------------------
  // Model stuff
  // --------------------------------------------------------------------------------------------

  public class FunSymbol : Common
  {
    public string Name;
    public List<FunApp> Apps = new List<FunApp>();
    public List<FunSymbol> AllSymbols;

    static bool appsByPartition = false;

    public override IEnumerable<Common> Children()
    {
      if (Apps.Count == 1)
        return Apps[0].Children();
      else {
        if (appsByPartition) {
          // group by partition
          Dictionary<string, List<Common>> byPart = new Dictionary<string, List<Common>>();
          foreach (var f in Apps) {
            List<Common> tmp;
            if (!byPart.TryGetValue(f.Value.Id, out tmp)) {
              tmp = new List<Common>();
              byPart.Add(f.Value.Id, tmp);
            }
            tmp.Add(f);
          }
          // sort by partition size
          List<List<Common>> lists = new List<List<Common>>(byPart.Values);
          lists.Sort(delegate(List<Common> x, List<Common> y) { return y.Count - x.Count; });
          List<Common> res = new List<Common>();
          foreach (var l in lists)
            res.AddRange(l);
          return res;
        } else {
          Apps.Sort(delegate(FunApp a1, FunApp a2)
          {
            for (int i = 0; i < a1.Args.Length; ++i) {
              int tmp = string.CompareOrdinal(a1.Args[i].ShortName(), a2.Args[i].ShortName());
              if (tmp != 0) return tmp;
            }
            return 0;
          });
          return Common.ConvertIEnumerable<Common,FunApp>(Apps);
        }
      }
    }

    static long[] maxValues = new long[] { short.MaxValue, int.MaxValue, long.MaxValue };
    static string[] maxValueNames = new string[] { "INT16", "INT32", "INT64" };

    string cachedDisplayName;
    public string DisplayName
    {
      get
      {
        if (cachedDisplayName == null) {
          cachedDisplayName = Name;

          int idx = Name.LastIndexOf("@@");
          if (idx > 0) {
            int end = idx + 2;
            while (end < Name.Length && Char.IsDigit(Name[end]))
              end++;
            if (end == Name.Length)
              cachedDisplayName = Name.Substring(0, idx);
          }

          long v;
          if (long.TryParse(cachedDisplayName, out v)) {
            for (int i = 0; i < maxValues.Length; ++i) {
              long diff = v - maxValues[i];
              if (Math.Abs((double)diff) < maxValues[i] / 100) {
                cachedDisplayName = MaxValueName("MAX", i, diff);
                break;
              }
            }

            for (int i = 0; i < maxValues.Length; ++i) {
              long diff = v - (-maxValues[i]-1);
              if (Math.Abs((double)diff) < maxValues[i] / 100) {
                cachedDisplayName = MaxValueName("MIN", i, diff);
                break;
              }
            }

            // TODO: should use bignums to handle MAXUINT64+/-
            for (int i = 0; i < maxValues.Length - 1; ++i) {
              long diff = v - (maxValues[i] + maxValues[i]);
              if (Math.Abs((double)diff) < maxValues[i] / 100) {
                cachedDisplayName = MaxValueName("MAXU", i, diff);                
                break;
              }
            }
          }
        }

        return cachedDisplayName;
      }
    }

    private string MaxValueName(string pref, int i, long diff)
    {
      pref += maxValueNames[i];
      if (diff == 0) return pref;
      return string.Format("{0}{1}{2}", pref, diff >= 0 ? "+" : "", diff);
    }

    public override string ToString()
    {
      if (Apps.Count == 1)
        return Apps[0].ToString();
      else
        return DisplayName + " [" + Apps.Count + "]";
    }
  }

  public class FunApp : Common
  {
    public FunSymbol Fun;
    public Partition[] Args;
    public Partition Value;

    public string ShortName()
    {
      if (Args.Length > 0) {
        StringBuilder sb = new StringBuilder(Fun.DisplayName);
        sb.Append("(");
        foreach (var a in Args)
          sb.Append(a.ShortName()).Append(", ");
        sb.Length = sb.Length - 2;
        sb.Append(")");
        return sb.ToString();
      } else {
        return Fun.DisplayName;
      }
    }

    public override string ToString()
    {
      string self = ShortName();
      if (Value.BestApp() != this)
        return self + " = " + Value.ShortName();
      else
        return self;
    }

    private IEnumerable<Common> Eq()
    {
      foreach (var other in Value.Values) {
        if (other != this)
          yield return new ForwardingNode("= " + other.ShortName(), other);
      }
    }

    public override IEnumerable<Common> Children()
    {
      foreach (var p in Args)
        yield return p.BestApp();
      yield return CallbackExp("EQ", this.Eq());
      yield return CallbackExp("USERS", this.Filter());
    }

    private IEnumerable<Common> Filter()
    {
      foreach (var fs in Fun.AllSymbols) {
        FunSymbol ffs = new FunSymbol();
        ffs.Name = fs.Name;
        foreach (var fapp in fs.Apps) {
          foreach (var a in fapp.Args) {
            if (a == this.Value) {
              ffs.Apps.Add(fapp);
              break;
            }
          }
        }
        if (ffs.Apps.Count > 0)
          yield return ffs;
      }
    }
  }

  public class Partition
  {
    public List<FunApp> Values = new List<FunApp>();
    public string Id;
    internal Model model;
    string shortName;
    FunApp bestApp;

    public FunApp BestApp()
    {
      if (bestApp != null)
        return bestApp;

      int cntMin = 0;
      int minBadness = 0;

      foreach (var f in Values) {
        int cur = model.FunAppBadness(f);
        if (bestApp == null || cur <= minBadness) {
          if (minBadness < cur) cntMin = 0;
          cntMin++;
          minBadness = cur;
          bestApp = f;
        }
      }

      if (cntMin > 1) {
        string prevName = bestApp.ShortName();
        foreach (var f in Values) {
          int cur = model.FunAppBadness(f);
          if (cur == minBadness) {
            string curName = f.ShortName();
            if (curName.Length < prevName.Length ||
                (curName.Length == prevName.Length && string.CompareOrdinal(curName, prevName) < 0)) {
              prevName = curName;
              bestApp = f;
            }
          }
        }
      }

      return bestApp;
    }

    public string ShortName()
    {
      if (shortName != null)
        return shortName;

      FunApp best = BestApp();
      shortName = Id;
      shortName = best.ShortName();

      return shortName;
    }
  }
}