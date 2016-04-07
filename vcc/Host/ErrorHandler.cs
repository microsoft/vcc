using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using Microsoft.Cci;

namespace Microsoft.Research.Vcc
{
  static class ExtensionMethods
  {
    public static Location ToLocation(this IToken tok)
    {
      return new Location(tok.filename, tok.line, tok.col);
    }
  }

  class CciErrorHandler
  {
    public CciErrorHandler() { }

    public CciErrorHandler(VccOptions commandLineOptions) {
      this.CommandLineOptions = commandLineOptions;
    }

    public VccOptions CommandLineOptions { get; set; }

    private bool WarningsAsErrors {
      get { return CommandLineOptions != null ? CommandLineOptions.WarningsAsErrors : false; }
    }

    private int WarningLevel {
      get { return CommandLineOptions != null ? CommandLineOptions.WarningLevel : 1; }
    }

    private bool WarningIsDisabled(long id) {
      if (CommandLineOptions == null) return false;
      return CommandLineOptions.DisabledWarnings.ContainsKey(id);
    }

    private bool DebugOnWarningOrError {
      get { return CommandLineOptions != null ? CommandLineOptions.DebugOnWarningOrError : false; }
    }
    
    public void HandleErrors(object sender, Microsoft.Cci.ErrorEventArgs args) {
      foreach (IErrorMessage error in args.Errors) {
        ISourceLocation/*?*/ sourceLocation = error.Location as ISourceLocation;
        if (sourceLocation == null) continue;
        if (this.DebugOnWarningOrError) System.Diagnostics.Debugger.Launch();
        bool isError = !error.IsWarning || WarningsAsErrors;
        if (!isError && GetWarningLevel(error.Code) > WarningLevel) continue;
        if (isError) VccCommandLineHost.IncreaseErrorCount();
        CompositeSourceDocument/*?*/ compositeDocument = sourceLocation.SourceDocument as CompositeSourceDocument;
        if (compositeDocument != null) {
          foreach (ISourceLocation sl in compositeDocument.GetFragmentLocationsFor(sourceLocation)) {
            sourceLocation = sl;
            break;
          }
        }
        IPrimarySourceLocation/*?*/ primarySourceLocation = sourceLocation as IPrimarySourceLocation;
        if (primarySourceLocation == null) {
          Logger.Instance.Error(error.Message);
          continue;
        }
        string docName = primarySourceLocation.SourceDocument.Location ?? primarySourceLocation.SourceDocument.Name.Value;
        int startLine = primarySourceLocation.StartLine;
        int startColumn = primarySourceLocation.StartColumn;
        IncludedSourceLocation/*?*/ includedSourceLocation = primarySourceLocation as IncludedSourceLocation;
        if (includedSourceLocation != null) {
          docName = includedSourceLocation.OriginalSourceDocumentName;
          if (docName != null) docName = docName.Replace("\\\\", "\\");
          startLine = includedSourceLocation.OriginalStartLine;
        }
        long id = error.IsWarning ? ErrorToId(error.Code) : error.Code;
        if (WarningIsDisabled(id)) return;

        Logger.Instance.LogWithLocation(String.Format("VC{0:0000}", id), error.Message, new Location(docName, startLine, startColumn), isError ? LogKind.Error : LogKind.Warning, false);

        string firstErrFile = docName;
        int firstErrLine = startLine;

        foreach (ILocation relatedLocation in error.RelatedLocations) {
          ISourceLocation/*?*/ sloc = relatedLocation as ISourceLocation;
          if (sloc != null) {
            compositeDocument = sloc.SourceDocument as CompositeSourceDocument;
            if (compositeDocument != null) {
              foreach (ISourceLocation sl in compositeDocument.GetFragmentLocationsFor(sloc)) {
                sloc = sl;
                break;
              }
            }
            primarySourceLocation = sloc as IPrimarySourceLocation;
            if (primarySourceLocation == null) continue;
            docName = primarySourceLocation.SourceDocument.Location ?? primarySourceLocation.SourceDocument.Name.Value;
            startLine = primarySourceLocation.StartLine;
            startColumn = primarySourceLocation.StartColumn;
            includedSourceLocation = primarySourceLocation as IncludedSourceLocation;
            if (includedSourceLocation != null) {
              docName = includedSourceLocation.OriginalSourceDocumentName;
              if (docName != null) docName = docName.Replace("\\\\", "\\");
              startLine = includedSourceLocation.OriginalStartLine;
            }
            if (docName != firstErrFile || firstErrLine != startLine) {
              Logger.Instance.LogWithLocation(
                null, 
                String.Format("(Location of symbol related to previous {0}.)", isError ? "error" : "warning"), 
                new Location(docName, startLine, startColumn),
                isError ? LogKind.Error : LogKind.Warning,
                true);
            }
          }
          //TODO: deal with non source locations
        }
      }
    }

    static long ErrorToId(long code) {
      switch ((Cci.Ast.Error)code) {
        case Cci.Ast.Error.ExpressionStatementHasNoSideEffect:
          return 9001;
      }

      switch ((Vcc.Error)code) {
        case Vcc.Error.DiscardedContractAtDefinition:
          return 9002;
        case Vcc.Error.SizeOfUnknown:
          return 9003;
      }

      return code;
    }

    private static int GetWarningLevel(long warningCode) {
      if (9300 <= warningCode && warningCode < 9400) return 0; // soundness warnings - cannot be suppressed
      else if (warningCode == (long)Error.PotentialPrecedenceErrorInLogicalExpression) return 2;
      else if (warningCode == (long)Cci.Ast.Error.PotentialUnintendRangeComparison) return 2;
      else return 1;
    }
  }

  class VerificationErrorHandler
  {
    /// <summary>
    /// Enumeration of error codes for verification errors
    /// </summary>
    public enum ErrorCode : long
    {
      AssertionFailed = (long)Cci.Ast.Error.ToBeDefined + 1,
      PreconditionFailed,
      PostconditionFailed,
      RelatedInformation
    };

    public VerificationErrorHandler(VccOptions commandLineOptions) {
      this.commandLineOptions = commandLineOptions;
    }

    private readonly VccOptions commandLineOptions;
    //private readonly Dictionary<IToken, List<ErrorCode>> reportedVerificationErrors = new Dictionary<IToken, List<ErrorCode>>();
    //private readonly List<string> errors = new List<string>();

    public void ReportCounterexample(Counterexample ce, string message) {
      if (message != null) message = " (" + message + ")";
      else message = "";

      try {
        ReturnCounterexample/*?*/ rce = ce as ReturnCounterexample;
        if (rce != null) {
          IToken tok = rce.FailingReturn.tok;
          for (int i = rce.Trace.Length - 1; i >= 0; i--) {
            foreach (Cmd c in rce.Trace[i].Cmds) {
              AssertCmd assrt = c as AssertCmd;
              if (assrt != null) {
                NAryExpr nary = assrt.Expr as NAryExpr;
                if (nary != null) {
                  FunctionCall fcall = nary.Fun as FunctionCall;
                  if (fcall != null && fcall.FunctionName == "$position_marker") {
                    tok = assrt.tok;
                  }
                }
              }
            }
          }
          ReportOutcomePostconditionFailed(rce.FailingEnsures.tok, tok, message);
        }
        AssertCounterexample/*?*/ ace = ce as AssertCounterexample;
        if (ace != null) {
          ReportOutcomeAssertFailed(ace.FailingAssert.tok,
            (ace.FailingAssert is LoopInvMaintainedAssertCmd ? "Loop body invariant" :
           ace.FailingAssert is LoopInitAssertCmd ? "Loop entry invariant" : "Assertion"),
           message
            );
        }
        CallCounterexample/*?*/ cce = ce as CallCounterexample;
        if (cce != null)
          ReportOutcomePreconditionFailed(cce.FailingCall.tok, cce.FailingRequires, message);
      } finally {
        if (commandLineOptions != null && commandLineOptions.PrintCEVModel) {
          ce.PrintModel();
        }
      }
    }

    private bool ReportError(IToken tok, VerificationErrorHandler.ErrorCode code, string fmt, params string[] args)
    {
      Logger.Instance.LogWithLocation(
        ErrorCodeToString(code),
        Format(fmt, args),
        tok.ToLocation(),
        LogKind.Error,
        false
      );

      return true;
    }

    private static string Format(string fmt, string[] args)
    {
      if (args.Length == 0) return fmt;
      else return string.Format(fmt, args);
    }

    private void ReportRelated(IToken tok, string fmt, params string[] args) 
    {
      Logger.Instance.LogWithLocation(
        ErrorCodeToString(ErrorCode.RelatedInformation),
        "(related information) " + Format(fmt, args),
        tok.ToLocation(),
        LogKind.Error, true);
    }

    private void ReportOutcomePreconditionFailed(IToken callTok, Requires req, string addComment) {
      string/*?*/ comment = req.Comment;
      IToken reqTok = req.tok;
      if (comment != null) comment = ": " + comment; else comment = "";
      comment += addComment;

      // in case of testsuite, don't print the full paths to prelude
      // also skip line numbers as they change
      bool isPrelude = reqTok.filename.EndsWith(".bpl") || reqTok.filename.EndsWith(".bpl>");
      if (isPrelude && reqTok.line > 1) {
        string line = VccCommandLineHost.StandardPreludeLines[reqTok.line - 2];
        int idx = line.IndexOf("TOKEN:");
        if (idx > 0) {
          reqTok.val = line.Substring(idx + 7);
        } else {
          line = VccCommandLineHost.StandardPreludeLines[reqTok.line - 1];
          idx = line.IndexOf("requires");
          reqTok.val = idx >= 0 ? line.Substring(idx + 8) : line;
        }
      }
      if (commandLineOptions != null && commandLineOptions.RunTestSuite && isPrelude) {
        reqTok.filename = "Vcc3Prelude.bpl";
        reqTok.line = 0;
        reqTok.col = 0;
      }

      string reqMsg = reqTok.val;
      ErrorCode errNo = GetErrorNumber(ref reqMsg, ErrorCode.PreconditionFailed);

      if (IsStandaloneError(errNo)) {
        ReportError(callTok, errNo, "{0} (in call '{1}'){2}.", reqMsg, RemoveWhiteSpace(callTok.val), comment);
      } else {
        if (ReportError(callTok, errNo, "Call '{0}' did not verify{1}.", RemoveWhiteSpace(callTok.val), comment)) {
          ReportRelated(reqTok, "Precondition: '{0}'.", reqMsg);
          ReportAllRelated(reqTok);
        }
      }
    }

    private void ReportOutcomeAssertFailed(IToken assertTok, string kind, string comment) {
      string msg = assertTok.val;
      ErrorCode errNo = GetErrorNumber(ref msg, ErrorCode.AssertionFailed);
      if (IsStandaloneError(errNo))
        ReportError(assertTok, errNo, "{0}{1}.", msg, comment);
      else
        ReportError(assertTok, errNo, "{0}{2} '{1}' did not verify.", kind, msg, comment);
      ReportAllRelated(assertTok);
    }

    private void ReportAllRelated(IToken tok)
    {
      var btok = tok as BoogieToken.Token;

      while (btok != null && btok.Related != null) {
        ReportRelated(btok.Related.Value, ((IToken)btok.Related.Value).val + ".");
        btok = btok.Related.Value as BoogieToken.Token;
      }
    }

    private void ReportOutcomePostconditionFailed(IToken ensTok, IToken retTok, string comment) {
      string msg = ensTok.val;
      ErrorCode errNo = GetErrorNumber(ref msg, ErrorCode.PostconditionFailed);
      if (retTok.line == 0) retTok = ensTok;
      if (ensTok.line == 0) ensTok = retTok;

      if (IsStandaloneError(errNo))
        ReportError(retTok, errNo, "{0}{1}.", msg, comment);
      else {
        if (ReportError(retTok, errNo, "Post condition{0} '{1}' did not verify.", comment, msg) && retTok.line != 0) {
          ReportRelated(ensTok, "Location of post condition.");
          ReportAllRelated(ensTok);
        }
      }
    }

    public void ReportOutcomeMethodSummary(string methodName, IToken tok, VC.ConditionGeneration.Outcome outcome, string addInfo, double startTime, IEnumerable<string> proverWarnings)
    {
      if (outcome != VC.ConditionGeneration.Outcome.Correct) VccCommandLineHost.IncreaseErrorCount();
      Logger.Instance.LogMethodSummary(methodName, tok.ToLocation(), (Outcome)(int)outcome, addInfo, GetTime() - startTime);

      if (!commandLineOptions.RunTestSuite) {
        foreach (var proverWarning in proverWarnings) {
          Logger.Instance.Warning("Prover warning: {0}", proverWarning);
        }
      }
    }

    public static string RemoveWhiteSpace(string str) {
      return String.Join(" ", Array.FindAll(str.Split(new[] { '\n', '\r', '\t', ' ' }), s => !String.IsNullOrEmpty(s)));
    }

    private static ErrorCode GetErrorNumber(ref string msg, ErrorCode def) {
      msg = RemoveWhiteSpace(msg);
      if (msg.StartsWith("#VCCERR:")) {
        int i = 8;
        while (i < msg.Length && char.IsDigit(msg[i])) i++;
        int num = int.Parse(msg.Substring(8, i - 8));
        msg = msg.Substring(i + 1);
        return (ErrorCode)num;
      } else
        return def;
    }

    // 9000-9099 - warnings mapped in this file
    // 9100-9199 - warning generated in the translator
    // 9500-9599 - errors mapped in this file
    // 9600-9699 - errors generated in translator
    private static string ErrorCodeToString(ErrorCode errCode) {
      long id;
      switch (errCode) {
        case VerificationErrorHandler.ErrorCode.AssertionFailed:
          id = 9500; break;
        case VerificationErrorHandler.ErrorCode.PostconditionFailed:
          id = 9501; break;
        case VerificationErrorHandler.ErrorCode.PreconditionFailed:
          id = 9502; break;
        case VerificationErrorHandler.ErrorCode.RelatedInformation:
          id = 9599; break;
        default:
          id = (long)errCode; break;
      }
      return "VC" + id.ToString("0000");
    }

    private static bool IsStandaloneError(VerificationErrorHandler.ErrorCode num) {
      return (int)num >= 8000 && (int)num < 8500;
    }

    internal static double GetTime() {
      return System.Environment.TickCount / 1000.0;
    }
  }
}
