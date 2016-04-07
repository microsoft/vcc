using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Cci;

namespace Microsoft.Research.Vcc
{
  class TransEnv : Microsoft.Research.Vcc.TransHelper.TransEnv
  {

    private readonly VccOptions options;
    private readonly ISourceEditHost hostEnv;
    private bool errorReported;
    private bool oopsed;

    public TransEnv(ISourceEditHost hostEnv, VccOptions options) : base(new VccOptionWrapper(options))
    {
      this.options = options;
      this.hostEnv = hostEnv;
      this.hostEnv.Errors += ErrorHandler;
    }

    private void ErrorHandler(object sender, ErrorEventArgs e)
    {
      if (errorReported) return;
      foreach (var msg in e.Errors)
      {
        if (!msg.IsWarning)
        {
          this.errorReported = true;
          break;
        }
      }
    }

    public override int PointerSizeInBytes
    {
      get { return this.options.PointerSize/8; }
    }

    public override bool ErrorReported
    {
      get { return this.errorReported; }
    }

    public override bool ShouldDumpStack
    {
      get { return !this.ErrorReported || this.oopsed; }
    }

    public override void Error(Token tok, int code, string msg, FSharp.Core.FSharpOption<Token> related)
    {
      if (IsSome(related))
        hostEnv.ReportError(new TranslationMessage(VisitorHelper.LocationFromToken(tok), code, msg, false,
                                                   new[] {VisitorHelper.LocationFromToken(related.Value)}));
      else
        hostEnv.ReportError(new TranslationMessage(VisitorHelper.LocationFromToken(tok), code, msg, false));
    }

    public override void Oops(Token tok, string msg)
    {
      if (this.ErrorReported) return;
      this.oopsed = true;
      hostEnv.ReportError(new TranslationMessage(VisitorHelper.LocationFromToken(tok), 9600, "OOPS: " + msg, false));
    }

    public override void Warning(Token tok, int code, string msg, FSharp.Core.FSharpOption<Token> related)
    {
      if (tok.SuppressWarning(code)) return;

      if (IsSome(related))
        hostEnv.ReportError(new TranslationMessage(VisitorHelper.LocationFromToken(tok), code, msg, true,
                                                   new[] {VisitorHelper.LocationFromToken(related.Value)}));
      else
        hostEnv.ReportError(new TranslationMessage(VisitorHelper.LocationFromToken(tok), code, msg, true));
    }

    private static bool IsSome<T>(FSharp.Core.FSharpOption<T> opt)
    {
      return FSharp.Core.FSharpOption<T>.get_IsSome(opt);
    }
  }
}
