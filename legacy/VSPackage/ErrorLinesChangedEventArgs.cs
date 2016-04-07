using System;

namespace Microsoft.Research.Vcc.VSPackage
{
  class ErrorLinesChangedEventArgs : EventArgs
  {
    private readonly string fileName;

    public ErrorLinesChangedEventArgs(string fileName)
    {
      this.fileName = fileName;
    }

    public string FileName
    {
      get { return this.fileName; }
    }
  }
}
