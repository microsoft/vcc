//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Windows.Forms;

namespace Z3AxiomProfiler
{
    static class Program
    {
        static void parseErrorCommandLineArguments(string err)
        {
          System.Console.WriteLine("Aborting parsing command line arguments:\n" + err);
          printUsage();
          System.Environment.Exit(1);
        }

        static void printUsage()
        {
          System.Console.WriteLine("Usage: Z3AxiomProfiler [options] <prelude-file> <filename>");
          System.Console.WriteLine("       prelude-file       : VCC prelude file location");
          System.Console.WriteLine("       filename           : Boogie input file");
          System.Console.WriteLine("       options ");
          System.Console.WriteLine("          /f:<function>   : Function name");
          System.Console.WriteLine("          /t:<seconds>    : Verification timeout");
          System.Console.WriteLine("          /l:<file>       : Log file to process");
          System.Console.WriteLine("          /s              : Skip conflicts/decisions (conserves memory)");
          System.Console.WriteLine("          /v1             : Start Z3 v1 (default)");
          System.Console.WriteLine("          /v2             : Start Z3 v2");
          System.Environment.Exit(0);
        }

        private static void InitConfig(Z3AxiomProfiler z3vis, string[] args) {
            string error_msg;
            if ( !z3vis.parseCommandLineArguments(args, out error_msg))
            {
                parseErrorCommandLineArguments(error_msg);
            }
        }

      /*

        [System.Runtime.InteropServices.DllImport("kernel32.dll")]
        static extern bool AttachConsole(int dwProcessId);
        private const int ATTACH_PARENT_PROCESS = -1;


        [System.Runtime.InteropServices.DllImport("kernel32.dll")]
        public static extern bool AllocConsole();

        [System.Runtime.InteropServices.DllImport("kernel32.dll")]
        public static extern bool FreeConsole();
       */
      
        /// <summary>
        /// The main entry point for the application.
        /// </summary>
        [STAThread]
        static void Main(string[] args)
        {
          //AllocConsole();
          //Console.OpenStandardOutput();
          //Console.OpenStandardError();
          //AttachConsole(ATTACH_PARENT_PROCESS);

          Application.EnableVisualStyles();
          Application.SetCompatibleTextRenderingDefault(false);
          Z3AxiomProfiler f = new Z3AxiomProfiler();
          InitConfig(f,args);
          f.Show();
          Application.Run(f);
        }

    }
}
