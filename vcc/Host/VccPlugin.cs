using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Boogie.AbstractInterpretation;

namespace Microsoft.Research.Vcc
{
  public abstract class VCGenPlugin
  {
    public abstract string Name { get; }
    public abstract VC.ConditionGeneration.Outcome VerifyImpl(TransHelper.TransEnv env, VC.VCGen vcgen, Implementation impl, Program prog, VerifierCallback reporter);
    public abstract void UseCommandLineOptions(List<string> opts);
  }

  class VccFunctionVerifier : FunctionVerifier
  {
    readonly Microsoft.FSharp.Collections.FSharpList<CAST.Top> currentDecls;
    readonly VccPlugin parent;
    readonly TransHelper.TransEnv env;
    Boogie.Program currentBoogie;
    bool mustRegenerateBoogie = true;
    VC.VCGen vcgen;
    bool errorMode;
    int modelCount;
    readonly List<string> options = new List<string>();
    readonly string[] standardBoogieOptions = new[] { 
      // report up to 10 errors
      "/errorLimit:10", 
      // use the monomorphic type encoding
      "/typeEncoding:m",
      // this defaults to 100 and causes Boogie to kill the prover after it is done, but has exceeded 100M; we instead use the /memory: switch to Z3
      "/proverMemoryLimit:0",
      // print prover warnings to stdout
      "/proverWarnings:1",
      // skip AI (inference of variable ranges mostly)
      //"/noinfer",  
      "/liveVariableAnalysis:0",
      "/prover:SMTLib",
      "/z3opt:/memory:300",
      "/z3opt:CASE_SPLIT=5",
      "/z3opt:QI_EAGER_THRESHOLD=1000",
    };
        
    internal VccFunctionVerifier(VccPlugin parent, Microsoft.FSharp.Collections.FSharpList<CAST.Top> currentDecls, TransHelper.TransEnv env)
      : base(env, currentDecls)
    {
      this.currentDecls = currentDecls;
      this.parent = parent;
      this.env = env;
      if (!this.InitBoogie()) this.env.Error(Token.NoToken, 1000, "Boogie initialization failed.");
    }

    public override Microsoft.FSharp.Collections.FSharpList<Tuple<string,string>> FunctionsToVerify()
    {
      return this.FindAllFunctions(currentDecls);
    }

    public override void Close()
    {
      base.Close();
      CloseVcGen();
    }

    private static string/*?*/ GetStringAttrValue(Implementation impl, string attrName) {
      return impl.FindStringAttribute(attrName) ?? impl.Proc.FindStringAttribute(attrName);
    }

    private static string/*?*/ GetExtraFunctionOptions(Implementation impl) {
      return GetStringAttrValue(impl, "vcc_extra_options");
    }

    private static bool IsBvLemmaCheck(Implementation impl)
    {
      return GetStringAttrValue(impl, "vcc_bv_lemma_check") != null;
    }

    private static bool HasSkipSmokeAttr(Implementation impl)
    {
      return GetStringAttrValue(impl, "vcc_skip_smoke") != null;
    }

    private static bool ReParseBoogieOptions(List<string> options, bool runningFromCommandLine)
    {
      var clo = new CommandLineOptions();
      if (clo.Parse(options.ToArray())) {
        clo.RunningBoogieFromCommandLine = runningFromCommandLine;
        CommandLineOptions.Install(clo);
        return true;
      }

      return false;
    }

    private bool InitBoogie()
    {
      options.AddRange(standardBoogieOptions);
      options.AddRange(parent.options.BoogieOptions);

      if (parent.options.RunInspector)
        options.Add(PathHelper.InspectorOption);

      if (parent.BvdModelFileName != null) {
        options.Add("/mv:" + parent.BvdModelFileName);
      }

      foreach (string z3option in parent.options.Z3Options) {
        if (z3option.StartsWith("-") || z3option.StartsWith("/") || z3option.Contains("="))
          options.Add("/z3opt:" + z3option);
        else {
          Logger.Instance.Error("Z3 option '{0}' is syntactically invalid.", z3option);
          return false;
        }
      }

      return ReParseBoogieOptions(options, parent.options.RunningFromCommandLine);
    }

    private bool HasIsolateProofAttribute(string funcName) {
      foreach (var decl in currentDecls) {
        if (decl.IsFunctionDecl && ((Microsoft.Research.Vcc.CAST.Top.FunctionDecl)decl).Item.Name == funcName) {
          foreach (var attr in ((CAST.Top.FunctionDecl)decl).Item.CustomAttr) {
            if (attr.IsVccAttr && ((CAST.CustomAttr.VccAttr)attr).Item1 == CAST.AttrIsolateProof) 
              return true;            
          }
        }
      }

      return false;
    }

    public override VerificationResult Verify(string funcName)
    {
      double start = VccCommandLineHost.GetTime();

      // Match replacement in Boogie names
      string sanitizedFuncName = funcName.Replace('\\', '#');

      bool restartProver = false;
      bool isolateProof = HasIsolateProofAttribute(funcName);

      if (isolateProof) { CloseVcGen(); }

      if (parent.options.AggressivePruning || isolateProof) {
        restartProver = true;
        // this needs to be done before pruning; otherwise call cycles might get hidden
        Termination.checkCallCycles(env, currentDecls);
        var decls = TransUtil.pruneBy(env, funcName, currentDecls);
        var boogieDecls = Translator.translate(funcName, env, () => VccCommandLineHost.StandardPrelude(parent.options), decls);
        if (!env.ShouldContinue) return VerificationResult.UserError;
        currentBoogie = PrepareBoogie(boogieDecls);
        mustRegenerateBoogie = true;
      } else {
        if (mustRegenerateBoogie || currentBoogie == null) {
          var boogieDecls = Translator.translate(null, env, () => VccCommandLineHost.StandardPrelude(parent.options), currentDecls);
          if (!env.ShouldContinue) return VerificationResult.UserError;
          currentBoogie = PrepareBoogie(boogieDecls);
          mustRegenerateBoogie = false;
        }
      }

      Implementation impl = null;
      foreach (Declaration decl in currentBoogie.TopLevelDeclarations) {
        impl = decl as Implementation;
        if (impl != null && impl.Name == sanitizedFuncName) break;
        impl = null;
      }
      if (impl == null) {
        Logger.Instance.Error("cannot find function: {0}", funcName);
        return VerificationResult.UserError;
      }

      if (this.errorMode || !env.ShouldContinue) return VerificationResult.UserError;

      if (impl.SkipVerification) return VerificationResult.Skipped;

      Logger.Instance.LogMethodStart(funcName);

      string logPath = CommandLineOptions.Clo.SimplifyLogFilePath;
      if (logPath != null)
        logPath = logPath.Replace("@VCCFILE@", TestRunner.currentTestcaseName);
      if (logPath != null && logPath.Contains("@VCCFUNC@")) {
        logPath = logPath.Replace("@VCCFUNC@", funcName.Replace("$", "_").Replace("^", "_"));
        CloseVcGen();
      }

      string extraFunctionOptions = null;
      bool isBvLemmaCheck = IsBvLemmaCheck(impl);
      bool skipSmoke = HasSkipSmokeAttr(impl);
      if ((parent.options.RunInBatchMode && (extraFunctionOptions = GetExtraFunctionOptions(impl)) != null) || isBvLemmaCheck || skipSmoke) {
        CloseVcGen();
        extraFunctionOptions = extraFunctionOptions ?? ""; // this prevents parsing errors in case of bv_lemma checks and will also cause the VcGen to be closed later
        VccOptions extraCommandLineOptions = OptionParser.ParseCommandLineArguments(VccCommandLineHost.dummyHostEnvironment, extraFunctionOptions.Split(' ', '\t'), false);
        List<string> effectiveOptions = new List<string>(extraCommandLineOptions.BoogieOptions);
        effectiveOptions.AddRange(extraCommandLineOptions.Z3Options.Select(z3option => "/z3opt:" + z3option));
        effectiveOptions.AddRange(options);
        if (isBvLemmaCheck) {
          effectiveOptions.Add("/proverOpt:OPTIMIZE_FOR_BV=true");
          effectiveOptions.RemoveAll(opt => opt == "/z3opt:CASE_SPLIT");
          effectiveOptions.Add("/z3opt:CASE_SPLIT=1");
        } 

        if (skipSmoke) {
          effectiveOptions.RemoveAll(opt => opt == "/smoke");
        }

        if (restartProver) {
          effectiveOptions.Add("/restartProver");
        }

        if (!ReParseBoogieOptions(effectiveOptions, parent.options.RunningFromCommandLine)) {
          Logger.Instance.Error("Error parsing extra options '{0}' for function '{1}'", extraFunctionOptions, impl.Name);
          return VerificationResult.UserError;
        }
        try {
          parent.swBoogie.Start();
          vcgen = new VC.VCGen(currentBoogie, logPath, CommandLineOptions.Clo.SimplifyLogFileAppend);
        } finally {
          parent.swBoogie.Stop();
        }
      } else if (vcgen == null) {
        // run with default options
        ReParseBoogieOptions(options, parent.options.RunningFromCommandLine);
        try {
          parent.swBoogie.Start();
          vcgen = new VC.VCGen(currentBoogie, logPath, CommandLineOptions.Clo.SimplifyLogFileAppend);
        } finally {
          parent.swBoogie.Stop();
        }
      }

      var reporter = new ErrorReporter(parent.options, impl.Proc.Name, impl.Proc.tok, start, VccCommandLineHost.ErrorHandler);

      try {
        parent.swVcOpt.Start();
      } finally {
        parent.swVcOpt.Stop();
      }


      VC.ConditionGeneration.Outcome outcome;
      string extraInfo = null;
      try {
        parent.swVerifyImpl.Start();
        VCGenPlugin plugin = parent.plugin;
        outcome = plugin != null ? plugin.VerifyImpl(env, vcgen, impl, currentBoogie, reporter) : vcgen.VerifyImplementation(impl, currentBoogie, reporter);
      } catch (UnexpectedProverOutputException exc) {
        outcome = VC.ConditionGeneration.Outcome.OutOfMemory;
        extraInfo = "caused an exception \"" + exc.Message + "\"";
      } finally {
        parent.swVerifyImpl.Stop();
      }

      if (extraFunctionOptions != null) {
        CloseVcGen();
      }

      reporter.PrintSummary(outcome, extraInfo);

      modelCount += reporter.modelCount;

      switch (outcome) {
        case VC.ConditionGeneration.Outcome.Correct: return VerificationResult.Succeeded;
        case VC.ConditionGeneration.Outcome.Errors: return VerificationResult.Failed;
        case VC.ConditionGeneration.Outcome.Inconclusive: return VerificationResult.Inconclusive;
        case VC.ConditionGeneration.Outcome.OutOfMemory: return VerificationResult.Crashed;
        case VC.ConditionGeneration.Outcome.TimedOut: return VerificationResult.Crashed;
        default: return VerificationResult.Crashed;
      }
    }

    private void CloseVcGen()
    {
      if (vcgen != null) {
        try {
          parent.swBoogie.Start();
          vcgen.Close();
        } finally {
          parent.swBoogie.Stop();
        }
        vcgen = null;
      }
    }

    public override void DumpInternalsToFile(string fn, bool generate) {

      Boogie.Program boogieToDump;

      if (generate) {
        var boogieDecls = Translator.translate(null, env, () => VccCommandLineHost.StandardPrelude(parent.options), currentDecls);
        boogieToDump = PrepareBoogie(boogieDecls);
      } else {
        boogieToDump = currentBoogie;
      }

      fn = Path.ChangeExtension(fn, (bplFileCounter++) + ".bpl");
      if (parent.options.OutputDir != null) {
        fn = Path.Combine(parent.options.OutputDir, Path.GetFileName(fn));
      }

      CommandLineOptions.Install(new CommandLineOptions());
      using (TokenTextWriter writer = new TokenTextWriter(fn))
        boogieToDump.Emit(writer);
    }

    long bplFileCounter;

    private Program PrepareBoogie(Microsoft.FSharp.Collections.FSharpList<BoogieAST.Decl> boogieDecls)
    {
      var boogieProgram = parent.GetBoogieProgram(boogieDecls);
      CloseVcGen();
      CommandLineOptions.Clo.Parse(standardBoogieOptions);
      IErrorSink errorSink = new BoogieErrorSink(parent.options.NoPreprocessor);

      int numErrors;

      try {
        parent.swBoogieResolve.Start();
        numErrors = boogieProgram.Resolve(errorSink);
      } finally {
        parent.swBoogieResolve.Stop();
      }
      if (numErrors == 0) {
        try {
          parent.swBoogieTypecheck.Start();
          numErrors = boogieProgram.Typecheck(errorSink);
        } finally {
          parent.swBoogieTypecheck.Stop();
        }
      }
      if (numErrors == 0) {
        try {
          parent.swBoogieAI.Start();
          AbstractInterpretation.RunAbstractInterpretation(boogieProgram);
        } finally {
          parent.swBoogieAI.Stop();
        }
      }

      if (Boogie.CommandLineOptions.Clo.ExpandLambdas && numErrors == 0) {
        Boogie.LambdaHelper.ExpandLambdas(boogieProgram);
      }

      if (numErrors != 0) {
        VccCommandLineHost.IncreaseErrorCount();
        if (!parent.options.RunTestSuite) {
          Logger.Instance.Error("attempting to dump BPL to buggy.bpl");
          var filename = "buggy.bpl";
          if (parent.options.OutputDir != null)
          {
            filename = Path.Combine(parent.options.OutputDir, filename);
          }

          CommandLineOptions.Install(new CommandLineOptions());
          using(TokenTextWriter writer = new TokenTextWriter(filename))
            boogieProgram.Emit(writer);
        }
        errorMode = true;
      } 

      return boogieProgram;

    }
  }
    
  internal class VccPlugin : Plugin
  {
    internal VccOptions options;
    internal string BvdModelFileName;
    internal VCGenPlugin plugin;

    readonly Stopwatch swBoogieAST = new Stopwatch("Boogie AST");
    internal Stopwatch swBoogie = new Stopwatch("Boogie");
    internal Stopwatch swBoogieAI = new Stopwatch("Boogie AI");
    internal Stopwatch swBoogieResolve = new Stopwatch("Boogie Resolve");
    internal Stopwatch swBoogieTypecheck = new Stopwatch("Boogie Typecheck");
    internal Stopwatch swVcOpt = new Stopwatch("VC Optimizer");
    internal Stopwatch swVerifyImpl = new Stopwatch("Boogie Verify Impl.");
    readonly Stopwatch swSaveBPL = new Stopwatch("Boogie Save BPL");

    public VccPlugin(VCGenPlugin plugin)
    {
      this.plugin = plugin;
    }

    private void RegisterStopwatches()
    {
      this.RegisterStopwatch(swBoogie);
      this.RegisterStopwatch(swBoogieAST);
      this.RegisterStopwatch(swBoogieAI);
      this.RegisterStopwatch(swBoogieResolve);
      this.RegisterStopwatch(swBoogieTypecheck);
      this.RegisterStopwatch(swVcOpt);
      this.RegisterStopwatch(swVerifyImpl);
      this.RegisterStopwatch(swSaveBPL);
    }

    public override string Help()
    {
      return "";
    }

    public override string Name()
    {
      return "Vcc";
    }

    public override void UseCommandLineOptions(List<string> p1)
    {
      if (plugin != null)
        plugin.UseCommandLineOptions(p1);
    }

    public override void UseOptions(Helper.Options opts)
    {
      options = ((VccOptionWrapper)opts).VccOptions;
    } 

    public override bool IsModular()
    {
      if (options.TranslateToBPL || options.NoVerification) return false;
      else return true;
    }

    public override void Verify(string fileName, TransHelper.TransEnv env, Microsoft.FSharp.Collections.FSharpList<CAST.Top> decls)
    {
      // this really only dumps the code to the .bpl file
      Init(env, fileName);
      decls = env.ApplyTransformers(decls);
      if (options.NoVerification) return;

      if (env.ShouldContinue) {
        if (env.Options.AggressivePruning && env.Options.Functions.Count() > 0) {
          decls = TransUtil.pruneBy(env, env.Options.Functions.First(), decls);
        }

        var boogieDecls = Translator.translate(null, env, () => VccCommandLineHost.StandardPrelude(options), decls);
        var p = TranslateToBoogie(boogieDecls);
        if (env.ShouldContinue) {
          try {
            swSaveBPL.Start();
            CommandLineOptions.Install(new CommandLineOptions());
            using (var writer = new TokenTextWriter(AddOutputDirIfRequested(Path.ChangeExtension(fileName, ".bpl")))) {
              p.Emit(writer);
            }
          } finally {
            swSaveBPL.Stop();
          }
        }
      }
    }

    private Program TranslateToBoogie(Microsoft.FSharp.Collections.FSharpList<BoogieAST.Decl> boogieDecls)
    {
      try {
        swBoogieAST.Start();
        return BoogieAST.trProgram(boogieDecls);
      } finally {
        swBoogieAST.Stop();
      }
    }

    private void Init(TransHelper.TransEnv env, string filename)
    {
      RegisterStopwatches();
      foreach (var s in env.Stopwatches)
        this.RegisterStopwatch(s);

      Transformers.init(env);
      Transformers.processPipeOptions(env);
      options = ((VccOptionWrapper)env.Options).VccOptions;
      this.BvdModelFileName = options.SaveModelForBvd ? AddOutputDirIfRequested(Path.ChangeExtension(filename, "model")) : null;
    }

    public override FunctionVerifier GetFunctionVerifier(string fileName, TransHelper.TransEnv env, Microsoft.FSharp.Collections.FSharpList<CAST.Top> decls)
    {
      Init(env, fileName);
      decls = env.ApplyTransformers(decls);
      return new VccFunctionVerifier(this, decls, env);
    }

    internal Boogie.Program GetBoogieProgram(Microsoft.FSharp.Collections.FSharpList<BoogieAST.Decl> boogieDecls)
    {
      var p = BoogieAST.trProgram(boogieDecls);
      try {
        swBoogie.Start();
        var pp = new Boogie.Program();
        pp.TopLevelDeclarations.AddRange(VccCommandLineHost.StandardPrelude(options).TopLevelDeclarations);
        pp.TopLevelDeclarations.AddRange(p.TopLevelDeclarations);
        return pp;
      } finally {
        swBoogie.Stop();
      }   
    }

    private string AddOutputDirIfRequested(string filePath)
    {
      return options.OutputDir == null ? filePath : Path.Combine(options.OutputDir, Path.GetFileName(filePath));
    }
  }


  internal class ErrorReporter : Microsoft.Boogie.VerifierCallback
  {
    bool outcomeReported;
    readonly string name;
    readonly double startTime;
    double prevTime;
    internal int modelCount;
    readonly VccOptions commandLineOptions;
    readonly List<string> proverWarnings;
    readonly VerificationErrorHandler errorHandler;
    readonly IToken tok;
    Microsoft.FSharp.Collections.FSharpSet<IdentifierExpr> unreachableMasters = new Microsoft.FSharp.Collections.FSharpSet<IdentifierExpr>(new List<IdentifierExpr>());
    Microsoft.FSharp.Collections.FSharpSet<IdentifierExpr> unreachableChildren;

    public ErrorReporter(VccOptions opts, string name, IToken tok, double startTime, VerificationErrorHandler errorHandler)
    {
      this.name = name;
      this.startTime = startTime;
      this.prevTime = VccCommandLineHost.GetTime();
      this.commandLineOptions = opts;
      this.proverWarnings = new List<string>();
      this.errorHandler = errorHandler;
      this.tok = tok;
    }

    public void PrintSummary(VC.ConditionGeneration.Outcome outcome, string addInfo = null)
    {
      if (!this.outcomeReported) {
        this.outcomeReported = true;
        this.errorHandler.ReportOutcomeMethodSummary(this.name, this.tok, outcome, addInfo, this.startTime, this.proverWarnings);
      }
    }

    public override void OnTimeout(string reason)
    {
      this.PrintSummary(VC.ConditionGeneration.Outcome.TimedOut, reason);
    }

    public override void OnCounterexample(Counterexample ce, string message)
    {
      this.modelCount++;
      this.PrintSummary(VC.ConditionGeneration.Outcome.Errors);
      this.errorHandler.ReportCounterexample(ce, message);
    }

    public override void OnOutOfMemory(string reason)
    {
      this.PrintSummary(VC.ConditionGeneration.Outcome.OutOfMemory);
    }

    public override void OnWarning(string msg) {
      this.proverWarnings.Add(msg);
    }

    public override void OnProgress(string phase, int step, int totalSteps, double progressEst)
    {
      if (phase == "done") return;

      if (double.IsNaN(progressEst)) return;

      if (commandLineOptions != null && commandLineOptions.TimeStats) {
        double now = VccCommandLineHost.GetTime();
        double length = now - this.prevTime;
        if (length < 0.5) return; // don't even bother reporting
        this.prevTime = now;

        string progressMsg;

        if (phase == "VCprove")
          progressMsg = String.Format("({0}/{1}/{2:0.00}%) ", step, totalSteps - step, progressEst * 100);
        else if (step != totalSteps || phase != "smoke")
          progressMsg = String.Format("({0}/{1}) ", step, totalSteps);
        else progressMsg = String.Format("({0})", step);

        Logger.Instance.LogProgress(name, phase, progressMsg);
      }
    }

    private void ReportUnreachable(IList<IToken> traceTokens)
    {
      if (traceTokens.Count == 0)
      {
        Logger.Instance.Warning("Found unreachable code, but cannot figure out where it is.");
          // TODO this won't be caught by the VS add-on
      }
      else
      {
        Logger.Instance.LogWithLocation(
          null,
          "found unreachable code, possible soundness violation, please check the axioms or add an explicit assert(false)",
          new Location(traceTokens[0].filename, traceTokens[0].line, traceTokens[0].col),
          LogKind.Warning,
          false);

        var prevFile = traceTokens[0].filename;
        var prevLine = traceTokens[0].line;
        var prevCol = traceTokens[0].col;

        for (int i = traceTokens.Count - 1; i > 0; i--)
        {
          if (traceTokens[i].col == prevCol && traceTokens[i].line == prevLine && traceTokens[i].filename == prevFile)
            continue;

          Logger.Instance.LogWithLocation(
            null,
            "trace to unreachable location",
            new Location(traceTokens[i].filename, traceTokens[i].line, traceTokens[i].col),
            LogKind.Warning,
            true);

          prevFile = traceTokens[i].filename;
          prevLine = traceTokens[i].line;
          prevCol = traceTokens[i].col;
        }
      }
    }

    private static bool HasRequiresFalse(Implementation impl)
    {
      foreach (Requires req in impl.Proc.Requires) {
        LiteralExpr f = req.Condition as LiteralExpr;
        if (f != null && f.IsFalse) return true;
      }

      return false;
    }

    private static bool HasAssertFalse(Block b)
    {
      foreach (var cmd in b.Cmds) {
        PredicateCmd pred = cmd as PredicateCmd;
        if (pred != null) {
          LiteralExpr f = pred.Expr as LiteralExpr;
          if (f != null && f.IsFalse) return true;            
        }
      }
      return false;
    }

    private static bool IsTokenWithoutLocation(IToken t)
    {
      return String.IsNullOrEmpty(t.filename) || t.filename == "<no file>";
    }

    public override void OnUnreachableCode(Implementation impl)
    {

      if (HasRequiresFalse(impl)) return;

      bool hasIFUnreachable = false;
      this.unreachableChildren = new Microsoft.FSharp.Collections.FSharpSet<IdentifierExpr>(new List<IdentifierExpr>());
      for (int i = impl.Blocks.Count - 1; i >= 0; i--)
      {
          Block b = impl.Blocks[i];
          if (HasAssertFalse(b))
          {
              foreach (var cmd in b.Cmds)
              {
                  PredicateCmd pred = cmd as PredicateCmd;
                  if (pred != null)
                  {
                      NAryExpr nary = pred.Expr as NAryExpr;
                      if (nary != null)
                      {
                          FunctionCall f = nary.Fun as FunctionCall;
                          if (f != null && f.Func.Name == "$expect_unreachable_master")
                          {
                              this.unreachableMasters = this.unreachableMasters.Add(f.Func.InParams.Last() as IdentifierExpr);
                              hasIFUnreachable = true;
                          }
                          else if (f != null && f.Func.Name == "$expect_unreachable_child")
                          {
                              this.unreachableChildren = this.unreachableChildren.Add(f.Func.InParams.Last() as IdentifierExpr);
                              hasIFUnreachable = true;
                          }
                      }
                  }
              }
          }
      }
      bool hasRealUnreachable = false;
      foreach (var id in this.unreachableChildren)
      {
          if (!unreachableMasters.Contains(id))
            hasRealUnreachable = true;
      }
      if (!hasRealUnreachable && hasIFUnreachable)
      {
          PrintSummary(VC.ConditionGeneration.Outcome.Correct);
          return;
      }

      var traceTokens = new List<IToken>();

      for (int i = impl.Blocks.Count - 1; i >= 0; i--) {
        Block b = impl.Blocks[i];
        foreach (var cmd in b.Cmds) {
          PredicateCmd pred = cmd as PredicateCmd;
          if (pred != null) {
            NAryExpr nary = pred.Expr as NAryExpr;
            if (nary != null) {
              FunctionCall f = nary.Fun as FunctionCall;
              if (f != null && f.Func.Name == "$expect_unreachable") return;   // Just restoring what existed. This is keeping some potentially easy to let through soundness warnings...
            }
          }
        }

        if (!IsTokenWithoutLocation(b.TransferCmd.tok))
          traceTokens.Add(b.TransferCmd.tok);
        else {
          for (int j = b.Cmds.Length - 1; j >= 0; j--)
          {
            if (!IsTokenWithoutLocation(b.Cmds[j].tok))
            {
              traceTokens.Add(b.Cmds[j].tok);
              break;
            }
          }
        }
      }

      PrintSummary(VC.ConditionGeneration.Outcome.Correct); // it is correct, but
      this.ReportUnreachable(traceTokens);
    }
  }
}
