// PkgCmdID.cs
// MUST match PkgCmdID.h

namespace Microsoft.Research.Vcc.VSPackage
{
  static class PkgCmdIDList
  {
    public const uint cmdidVerifyActiveFile = 0x0102;
    public const uint cmdidVerifyActiveFileWithoutIncludes = 0x0103;
    public const uint cmdidCancel = 0x0105;
    public const uint cmdidContextVerifyActiveFile = 0x0106;
    public const uint cmdidContextVerifyActiveFileWithoutIncludes = 0x0107;
    public const uint cmdidContextCustomVerify = 0x0109;
    public const uint cmdidContextCancel = 0x0110;
    public const uint cmdidCustomVerify = 0x0111;
    public const uint cmdidReVerify = 0x0112;
    public const uint cmdidContextReVerify = 0x0113;
    public const uint cmdidContextVerifyThis = 0x0114;
    public const uint cmdidVerifyThis = 0x0115;
    public const uint cmdidOptions = 0x0116;
    public const uint cmdidShowErrorModel = 0x0117;

    public const uint cmdidVerifyMenu = 0x1021;
    public const uint cmdidContextMenuGroup = 0x1022;

    public const uint cmdidMathSymbolForall = 0x0220;
    public const uint cmdidMathSymbolExists = 0x0221;
    public const uint cmdidMathSymbolIn = 0x0222;
    public const uint cmdidMathSymbolUnion = 0x0223;
    public const uint cmdidMathSymbolIntersection = 0x0224;
    public const uint cmdidMathSymbolLambda = 0x0225;
  };
}