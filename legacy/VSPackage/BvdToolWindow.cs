namespace Microsoft.Research.Vcc.VSPackage
{
  using System;
  using System.Runtime.InteropServices;
  using Microsoft.VisualStudio.Shell;

  [Guid(GuidList.GuidBvdWindowPersistanceString)]
  internal sealed class BvdToolWindow : ToolWindowPane
  {
    private static readonly Lazy<Microsoft.Boogie.ModelViewer.Main> bvdInstance = new Lazy<Microsoft.Boogie.ModelViewer.Main>(() => new Microsoft.Boogie.ModelViewer.Main(new string[] {}, true));

    public BvdToolWindow()
      : base(null)
    {
      this.Caption = "Boogie Verification Debugger";
      this.BitmapResourceID = 301;
      this.BitmapIndex = 10;
    }

    public override System.Windows.Forms.IWin32Window Window
    {
      get { return bvdInstance.Value; }
    }

    public static Microsoft.Boogie.ModelViewer.Main BVD
    {
      get { return bvdInstance.Value; }
    }
  }
}
