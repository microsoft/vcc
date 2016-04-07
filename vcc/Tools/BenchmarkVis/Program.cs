using System;
using System.Collections.Generic;
using System.Linq;
using System.Windows.Forms;

namespace BenchmarkVis
{
  static class Program
  {
    /// <summary>
    /// The main entry point for the application.
    /// </summary>
    [STAThread]
    static void Main()
    {
      Application.EnableVisualStyles();
      Application.SetCompatibleTextRenderingDefault(false);
      var m = new Main();
      m.ProcessArgs();
      Application.Run(m);
    }
  }
}
