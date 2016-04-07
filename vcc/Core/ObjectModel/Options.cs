//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.IO;
using Microsoft.Cci;
using Microsoft.Cci.Ast;

namespace Microsoft.Research.Vcc
{

  public sealed class VccOptions : FrameworkOptions
  {
    public List<string> HandledOptions = new List<string>();
    public List<string> BoogieOptions = new List<string>();
    public bool NoPreprocessor;
    public List<string> PreprocessorOptions = new List<string>();
    public bool RunTestSuite;
    public double RunTestSuiteMultiThreaded = -1;
    public bool TranslateToBPL;
    public List<string> Z3Options = new List<string>();
    public bool TimeStats;
    public string XmlLogFile;
    public string/*?*/ ClPath;
    public List<string> Functions = new List<string>();
    public List<string> FunctionsWithExactName = new List<string>();
    public List<string> WeightOptions = new List<string>();
    public bool RunningFromCommandLine;
    public uint? VerifyUpToLine;
    public bool RunInBatchMode;
    public Dictionary<long, bool> DisabledWarnings = new Dictionary<long, bool>();
    public bool AggressivePruning;
    public List<string> PipeOperations = new List<string>();
    public Dictionary<string, List<string>> PluginOptions = new Dictionary<string, List<string>>();
    public bool DumpBoogie;
    public bool WarningsAsErrors;
    public int WarningLevel = 1;
    public bool DebugOnWarningOrError;
    public bool SaveModelForBvd;
    public bool RunInspector;
    public bool DetailedTimes;
    public bool PrintCEVModel;
    public int PointerSize = 64;
    public bool YarraMode;
    public int DumpTriggers; // 0-none, 1-C syntax, 2-C+Boogie syntax
    public bool KeepPreprocessorFiles;
    public bool OpsAsFunctions;
    public string VerificationLocation;
    public string OutputDir;
    public string IgnoreIncludes;
    public string PreludePath;
    public int TerminationLevel = 1;
    public bool TerminationForPure { get { return TerminationLevel >= 1; } }
    public bool TerminationForGhost { get { return TerminationLevel >= 2; } }
    public bool TerminationForAll { get { return TerminationLevel >= 3; } }
    public bool ExplicitTargetsGiven {
      get {
        return VerificationLocation != null || 0 < Functions.Count || 0 < FunctionsWithExactName.Count;
      }
    }
    public int DefExpansionLevel = 3;
    public bool NoVerification;
    public bool DeterminizeOutput;

    public void CopyFrom(VccOptions other)
    {
      // base class:
      this.CheckedArithmetic = other.CheckedArithmetic;
      this.CodePage = other.CodePage;
      this.DisplayCommandLineHelp = other.DisplayCommandLineHelp;
      this.DisplayVersion = other.DisplayVersion;
      this.OutputFileName = other.OutputFileName;

      this.FileNames.Clear(); this.FileNames.AddRange(other.FileNames);
      this.ReferencedAssemblies.Clear(); this.ReferencedAssemblies.AddRange(other.ReferencedAssemblies);

      // this class
      this.HandledOptions.Clear(); this.HandledOptions.AddRange(other.HandledOptions);
      this.BoogieOptions.Clear(); this.BoogieOptions.AddRange(other.BoogieOptions);
      this.WeightOptions.Clear(); this.WeightOptions.AddRange(other.WeightOptions);
      this.PreprocessorOptions.Clear(); this.PreprocessorOptions.AddRange(other.PreprocessorOptions);
      this.Z3Options.Clear(); this.Z3Options.AddRange(other.Z3Options);
      this.Functions.Clear(); this.Functions.AddRange(other.Functions);
      this.FunctionsWithExactName.Clear(); this.FunctionsWithExactName.AddRange(other.FunctionsWithExactName);
      this.PipeOperations.Clear(); this.PipeOperations.AddRange(other.PipeOperations);

      this.DisabledWarnings.Clear();
      foreach (var kv in other.DisabledWarnings)
        this.DisabledWarnings[kv.Key] = kv.Value;
      this.PluginOptions.Clear();
      foreach (var kv in other.PluginOptions)
        this.PluginOptions[kv.Key] = new List<string>(kv.Value);

      this.NoPreprocessor = other.NoPreprocessor;
      this.RunTestSuite = other.RunTestSuite;
      this.RunTestSuiteMultiThreaded = other.RunTestSuiteMultiThreaded;
      this.TranslateToBPL = other.TranslateToBPL;
      this.TimeStats = other.TimeStats;
      this.XmlLogFile = other.XmlLogFile;
      this.ClPath = other.ClPath;
      this.RunningFromCommandLine = other.RunningFromCommandLine;
      this.VerifyUpToLine = other.VerifyUpToLine;
      this.RunInBatchMode = other.RunInBatchMode;
      this.AggressivePruning = other.AggressivePruning;
      this.DumpBoogie = other.DumpBoogie;
      this.WarningsAsErrors = other.WarningsAsErrors;
      this.WarningLevel = other.WarningLevel;
      this.DebugOnWarningOrError = other.DebugOnWarningOrError;
      this.SaveModelForBvd = other.SaveModelForBvd;
      this.RunInspector = other.RunInspector;
      this.DetailedTimes = other.DetailedTimes;
      this.PrintCEVModel = other.PrintCEVModel;
      this.PointerSize = other.PointerSize;
      this.DumpTriggers = other.DumpTriggers;
      this.KeepPreprocessorFiles = other.KeepPreprocessorFiles;
      this.OpsAsFunctions = other.OpsAsFunctions;
      this.OutputDir = other.OutputDir;
      this.VerificationLocation = other.VerificationLocation;
      this.YarraMode = other.YarraMode;
      this.IgnoreIncludes = other.IgnoreIncludes;
      this.TerminationLevel = other.TerminationLevel;
      this.DefExpansionLevel = other.DefExpansionLevel;
      this.NoVerification = other.NoVerification;
      this.DeterminizeOutput = other.DeterminizeOutput;
      this.PreludePath = other.PreludePath;
    }
  }

  public class OptionParser : OptionParser<VccOptions>
  {

    private OptionParser(MetadataHostEnvironment hostEnvironment)
      : base(hostEnvironment) {
      //^ assume this.options != null;
      this.options.CheckedArithmetic = true;
    }

    private static void CheckOptions(MetadataHostEnvironment hostEnvironment, VccOptions options)
    {
      if (options.RunTestSuite &&
          options.RunTestSuiteMultiThreaded != -1 &&
          !String.IsNullOrEmpty(options.XmlLogFile)) {
          DummyExpression dummyExpression = new DummyExpression(SourceDummy.SourceLocation);
          hostEnvironment.ReportError(new AstErrorMessage(dummyExpression,
                                                          Microsoft.Cci.Ast.Error.InvalidCompilerOption,
                                                          "Cannot combine /xml with /suite /smt")); // XML logger is sequential
      }
    }

    public static VccOptions ParseCommandLineArguments(MetadataHostEnvironment hostEnvironment, IEnumerable<string> arguments) {
      return OptionParser.ParseCommandLineArguments(hostEnvironment, arguments, true);
    }

    public static VccOptions ParseCommandLineArguments(MetadataHostEnvironment hostEnvironment, IEnumerable<string> arguments, bool oneOrMoreSourceFilesExpected) {
      OptionParser parser = new OptionParser(hostEnvironment);
      parser.ParseCommandLineArguments(arguments, oneOrMoreSourceFilesExpected);
      CheckOptions(hostEnvironment, parser.options);
      return parser.options;
    }

    public static VccOptions ParseCommandLineArguments(MetadataHostEnvironment hostEnvironment, IEnumerable<string> arguments, VccOptions template)
    {
      OptionParser parser = new OptionParser(hostEnvironment);
      parser.options.CopyFrom(template);
      parser.ParseCommandLineArguments(arguments, false);
      CheckOptions(hostEnvironment, parser.options);
      return parser.options;
    }

    private bool TryParseNamedBoolean(string arg, string longName, string shortName, ref bool flag)
    {
      bool? res = this.ParseNamedBoolean(arg, longName, shortName);
      if (res != null) {
        flag = res.Value;
        return true;
      } else {
        return false;
      }
    }

    private bool TryParseNamedInteger(string arg, string longName, string shortName, ref int flag)
    {
      int tmp;
      string value = this.ParseNamedArgument(arg, longName, shortName);
      if (value != null && Int32.TryParse(value, out tmp)) {
        flag = tmp;
        return true;
      } else {
        return false;
      }
    }

    private bool TryParseNamedDouble(string arg, string longName, string shortName, ref double flag)
    {
      double tmp;
      string value = this.ParseNamedArgument(arg, longName, shortName);
      if (value != null && double.TryParse(value, out tmp)) {
        flag = tmp;
        return true;
      } else {
        return false;
      }
    }

    protected override bool ParseCompilerOption(string arg)
    {
      int n = arg.Length;
      if (n <= 1) return false;
      char ch = arg[0];
      if (ch != '/' && ch != '-') return false;
      this.options.HandledOptions.Add(arg);
      ch = arg[1];
      switch (ch)
      {          
        case 'a':
          bool? aggressivePruning = this.ParseNamedBoolean(arg, "aggressivepruning", "a");
          if (aggressivePruning != null) {
            this.options.AggressivePruning = aggressivePruning.Value;
            return true;
          }
          return false;
        case 'b':
          if (this.ParseName(arg, "batch", "batch")) {
            this.options.RunInBatchMode = true;
            return true;
          }
          if (this.ParseName(arg, "bvd", "bvd")) {
            this.options.PrintCEVModel = true;
            this.options.SaveModelForBvd = true;
            return true;
          }

          List<string> /*?*/ boogieOptions = this.ParseNamedArgumentList(arg, "boogie", "b");
          if (boogieOptions == null || boogieOptions.Count == 0) return false;
          this.options.BoogieOptions.AddRange(boogieOptions);
          return true;
        case 'c':
          string /*?*/ clPath = this.ParseNamedArgument(arg, "clpath", "clpath");
          if (clPath != null) {
            this.options.ClPath = clPath;
            return true;
          }
          string filename = this.ParseNamedArgument(arg, "cevprint", "cev");
          if (filename != null) {
            this.options.PrintCEVModel = true;
            this.options.BoogieOptions.Add("/mv:" + filename);
            return true;
          }
          return false;
        case 'd':
          if (this.ParseName(arg, "debug", "dbg")) {
            this.options.DebugOnWarningOrError = true;
            return true;
          }
          bool? dump = this.ParseNamedBoolean(arg, "dumpsource", "d");
          if (dump != null) {
            this.options.PipeOperations.Add("dump after end");
            return true;
          }
          dump = this.ParseNamedBoolean(arg, "dumpsource0", "d0");
          if (dump != null) {
            this.options.PipeOperations.Add("dump before begin");
            return true;
          }

          if (this.ParseName(arg, "determinize", "det")) {
            this.options.DeterminizeOutput = true;
            return true;
          }

          string expansionStr = this.ParseNamedArgument(arg, "defexpansion", "dexp");
          int expansionLev;
          if (expansionStr != null && int.TryParse(expansionStr, out expansionLev)) {
            this.options.DefExpansionLevel = expansionLev;
            return true;
          }

          return
            this.TryParseNamedBoolean(arg, "dumpboogie", "db", ref this.options.DumpBoogie) ||
            this.TryParseNamedInteger(arg, "dumptriggers", "dt", ref this.options.DumpTriggers);

        case 'f':
          var functions = this.ParseNamedArgumentList(arg, "functions", "f");
          if (functions == null || functions.Count == 0) return false;
          this.options.Functions.AddRange(functions);
          return true;

        case 'F':
          var functionExactMatch = this.ParseNamedArgumentList(arg, "functions", "f");
          if (functionExactMatch == null || functionExactMatch.Count == 0) return false;
          this.options.FunctionsWithExactName.AddRange(functionExactMatch);
          return true;

        case 'h':
          if (this.ParseName(arg, "help", "help")) {
            this.options.DisplayCommandLineHelp = true;
            return true;
          }
          List<string> /*?*/ hiddenWarnings = this.ParseNamedArgumentList(arg, "hide", "h");
          if (hiddenWarnings == null || hiddenWarnings.Count == 0) return false;
          foreach (string w in hiddenWarnings) {
            long tmp;
            if (!long.TryParse(w, out tmp)) return false;
            if (!this.options.DisabledWarnings.ContainsKey(tmp)) {
              this.options.DisabledWarnings.Add(tmp, true);
            }
          }
          return true;

        case 'i':
          if (this.ParseName(arg, "inspector", "i")) {
            this.options.RunInspector = true;
            return true;
          }

          string iiFileName = this.ParseNamedArgument(arg, "ignoreincludes", "ii");
          if (iiFileName != null)
          {
              this.options.IgnoreIncludes = iiFileName;
              return true;
          }

          if (this.ParseName(arg, "ignoreincludes", "ii"))
          {
              this.options.IgnoreIncludes = "";
              return true;
          }

          return false;

        case 'k':
          return this.TryParseNamedBoolean(arg, "keepppoutput", "keepppoutput", ref this.options.KeepPreprocessorFiles);

        case 'l':
          if (this.ParseName(arg, "launch", "launch")) {
            System.Diagnostics.Debugger.Launch();
            return true;
          }
          var loc = this.ParseNamedArgument(arg, "loc", "location");
          if (loc != null) {
            this.options.VerificationLocation = loc;
            return true;
          }

          break;

        case 'n':
          if (this.ParseName(arg, "nopreprocessor", "n")) {
            this.options.NoPreprocessor = true;
            return true;
          }
          if (this.ParseName(arg, "noverification", "nv")) {
            this.options.NoVerification = true;
            return true;
          }
          return false;
        case 'o':
          string /*?*/ path = this.ParseNamedArgument(arg, "out", "o");
          if (path != null) {
            this.options.OutputDir = path;
            return true;
          }
          if (this.ParseName(arg, "opsasfuncs", "oaf")) {
            this.options.OpsAsFunctions = true;
            return true;
          }
          return false;
        case 'p':
          int pointerSize = 0;
          if (this.TryParseNamedInteger(arg, "pointersize", "ps", ref pointerSize) &&
              (pointerSize == 32 || pointerSize == 64)) {
            this.options.PointerSize = pointerSize;
            return true;
          }

          List<string> /*?*/ pipeOptions = this.ParseNamedArgumentList(arg, "pipe", "pipe");
          if (pipeOptions != null && pipeOptions.Count > 0) {
            this.options.PipeOperations.AddRange(pipeOptions);
            return true;
          }

          string prelude = this.ParseNamedArgument(arg, "prelude", "prelude");
          if (prelude != null) {
            this.options.PreludePath = prelude;
            return true;
          }

          List<string> /*?*/ preprocessorOptions = this.ParseNamedArgumentList(arg, "preprocessor", "p");
          if (preprocessorOptions != null && preprocessorOptions.Count > 0) {
            //i-sebaf: If IncludeDir Contains Spaces like "Program Files" than a quote is required.
            for (int i = 0; i < preprocessorOptions.Count; i++) {
              if (preprocessorOptions[i].Contains(" ")) {
                preprocessorOptions[i] = preprocessorOptions[i].Insert(2, "\"") + "\"";
              }
            }
            this.options.PreprocessorOptions.AddRange(preprocessorOptions);
            return true;
          }

          {
            int end = arg.IndexOf(':');
            int semi = end;
            if (end < 0) end = arg.Length;
            string option = arg.Substring(1, end - 1).ToLower(System.Globalization.CultureInfo.InvariantCulture);
            string plugin = option.Substring(1);
            List<string> args;
            if (!this.options.PluginOptions.TryGetValue(plugin, out args)) {
              args = new List<string>();
              this.options.PluginOptions[plugin] = args;
            }
            if (semi > 0) {
              List<string> /*?*/ pluginOptions = this.ParseNamedArgumentList(arg, option, option);
              if (pluginOptions == null)
                args.Add("");
              else
                args.AddRange(pluginOptions);
            }
            else
            {
              args.Add("");
            }
            return true;
          }

        case 's':
          if (this.ParseName(arg, "suite", "s"))
          {
            this.options.RunTestSuite = true;
            this.options.NoPreprocessor = true;
            return true;
          }
          else if (this.ParseName(arg, "stats", "st"))
          {
            this.options.TimeStats = true;
            return true;
          }
          else if (this.ParseName(arg, "smoke", "sm"))
          {
            this.options.BoogieOptions.Add("/smoke");
            return true;
          }
          else
          {
            if (this.TryParseNamedDouble(arg, "suitemt", "smt", ref this.options.RunTestSuiteMultiThreaded))
              return true;
            if (this.ParseName(arg, "suitemt", "smt"))
            {
              this.options.RunTestSuiteMultiThreaded = 0.0;
              return true;
            }
          }
          return false;
        case 't':
          bool? detailedTimes = this.ParseNamedBoolean(arg, "time", "time");
          if (detailedTimes != null) {
            this.options.DetailedTimes = detailedTimes.Value;
            return true;
          }
          bool? translateToBpl = this.ParseNamedBoolean(arg, "translate", "t");
          if (translateToBpl != null) {
            this.options.TranslateToBPL = translateToBpl.Value;
            return true;
          }
          ushort termLevel;
          string termLevelStr = this.ParseNamedArgument(arg, "termination", "term");
          if (termLevelStr != null && ushort.TryParse(termLevelStr, out termLevel)) {
            this.options.TerminationLevel = termLevel;
            return true;
          }
          return false;
        case 'u':
          string lineStr = this.ParseNamedArgument(arg, "uptoline", "uptoline");
          uint lineNo;
          if (lineStr != null && UInt32.TryParse(lineStr, out lineNo)) {
            this.options.VerifyUpToLine = lineNo;
            return true;
          }
          return false;
        case 'v':
          if (this.ParseName(arg, "version", "version")) {
            this.options.DisplayVersion = true;
            return true;
          }

          return false;

        case 'w':
          int warnLevel = -1;
          if (this.TryParseNamedInteger(arg, "warn", "w", ref warnLevel) && warnLevel >= 0 && warnLevel <= 2) {
            this.options.WarningLevel = warnLevel;
            return true;
          }
          bool? wx = this.ParseNamedBoolean(arg, "warningsaserrors", "wx");
          if (wx != null) {
            this.options.WarningsAsErrors = wx.Value;
            return true;
          }
          var wopts = this.ParseNamedArgumentList(arg, "weight", "weight");
          if (wopts != null && wopts.Count != 0) {
            this.options.WeightOptions.AddRange(wopts);
            return true;
          }
          return false;
        case 'x':
          string xmlLogFile = this.ParseNamedArgument(arg, "xml", "xml");
          if (xmlLogFile != null) {
            this.options.XmlLogFile = xmlLogFile;
            return true;
          }
         
          return false;
        case 'y':
          if (this.ParseName(arg, "yarra", "yarra")) {
            this.options.YarraMode = true;
            return true;
          }
          return false;
        case 'z':
          List<string> /*?*/ z3Options = this.ParseNamedArgumentList(arg, "z3", "z");
          if (z3Options == null || z3Options.Count == 0) return false;
          this.options.Z3Options.AddRange(z3Options);
          return true;
        case '?':
          this.options.DisplayCommandLineHelp = true;
          return true;
        default:
          break;
      }
      return false;
    }

    protected override bool DirectoryIsOk(string path, string pattern, string extension)
    {
      if (!this.options.RunTestSuite) return false;
      
      string fixPath = path;
      if (pattern != "")
      {
          if (!fixPath.EndsWith("\\")) fixPath += "\\";
          fixPath += pattern;
      }
      if (extension != "" && !fixPath.EndsWith(extension))
      {
          // Note: doesn't hit, normally extension already included
          fixPath += extension;
      }
      this.options.FileNames.Add(fixPath);
      return true;
    }
  }
}
