//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Text;
using System.Linq;

namespace Microsoft.Research.Vcc
{
  class CCompilerHelper
  {
    public static IEnumerable<StreamReader> Preprocess(VccOptions commandLineOptions, out bool hasErrors) {
      hasErrors = false;
      if (commandLineOptions.NoPreprocessor) {
        return commandLineOptions.FileNames.Select(s => new StreamReader(s));
      }
      string savedCurentDir = Directory.GetCurrentDirectory();
      var preprocessedFiles = new List<StreamReader>();
      try {
        foreach (string fileName in commandLineOptions.FileNames) {
          Directory.SetCurrentDirectory(Path.GetDirectoryName(fileName));
          var ppStream = RunPreprocessor(fileName, commandLineOptions);
          if (ppStream == null) {
            hasErrors = true;
            break;
          } else {
            preprocessedFiles.Add(ppStream);
          }
        }
      } catch (Exception e) {
        Logger.Instance.Error("Error while running preprocessor: " + e.Message);
        hasErrors = true;
      } finally {
        Directory.SetCurrentDirectory(savedCurentDir);
      }

      return preprocessedFiles;
    }

    private static string GenerateClArgs(string fileName, VccOptions commandLineOptions) {
      StringBuilder args = new StringBuilder();
      args.Append("/nologo /TC /u /E /DVERIFY /D_WIN32");
      // VCC doesn't like /D_PREFAST_ with VS2010
      args.Append(" /D_USE_DECLSPECS_FOR_SAL /DSAL_NO_ATTRIBUTE_DECLARATIONS"); // TODO revisit these
      if (commandLineOptions.PointerSize == 64) args.Append(" /D_WIN64");

      foreach (string ppOption in commandLineOptions.PreprocessorOptions) {
        args.Append(' ');
        args.Append(ppOption);
      }
      string/*?*/ vccHeaders = PathHelper.GetVccHeaderDir(true);
      if (vccHeaders != null) {
        args.Append(" /I");
        args.Append(vccHeaders);
      }
      args.Append(" \"").Append(fileName).Append('\"');

      return args.ToString();
    }

    private static bool ProcessOutputAndReturnTrueIfErrorsAreFound(string fileName, StringBuilder ppOutput) {
      bool hasErrors = false;
      if (ppOutput.Length > 0) {
        ppOutput = ppOutput.Replace(Path.GetFileName(fileName) + "\r\n", "");
        var str = ppOutput.ToString();
        if (str.Contains(": error C") || str.Contains(": fatal error C")) {
          Logger.Instance.Error(str);
          hasErrors = true;
        } else {
          if (str.Length > 0)
          Logger.Instance.Log(str);
        }
      }
      return hasErrors;
    }

    private static StreamReader RunPreprocessor(string fileName, VccOptions commandLineOptions) {
      string args = GenerateClArgs(fileName, commandLineOptions);
      string outExtension = ".i";
      string outFileName = Path.ChangeExtension(fileName, outExtension);
      if (commandLineOptions.OutputDir != null) {
        outFileName = Path.Combine(commandLineOptions.OutputDir, Path.GetFileName(outFileName));
      }
      return StartClProcessAndReturnOutput(fileName, args, outFileName, commandLineOptions);
    }

    private static StreamReader StartClProcessAndReturnOutput(string fileName, string arguments, string outFileName, VccOptions commandLineOptions) {

      StringBuilder errors = new StringBuilder();
      ProcessStartInfo info = ConfigureStartInfoForClVersion11Or10Or9(commandLineOptions);
      info.Arguments = arguments;
      info.CreateNoWindow = true;
      info.RedirectStandardOutput = true;
      info.RedirectStandardError = true;
      info.UseShellExecute = false;
      info.StandardOutputEncoding = Encoding.UTF8;

      StreamWriter outFile = null;
      MemoryStream tmpOut = null;

      if (commandLineOptions.KeepPreprocessorFiles)
        outFile = new StreamWriter(outFileName, false, Encoding.UTF8);
      else
        outFile = new StreamWriter(tmpOut = new MemoryStream());

      try {
        using (Process process = Process.Start(info)) {
          process.OutputDataReceived += delegate(object sender, DataReceivedEventArgs args)
          {
            if (args.Data != null) outFile.WriteLine(args.Data);
          };

          process.ErrorDataReceived += delegate(object sender, DataReceivedEventArgs args)
          {
            if (args.Data != null) errors.AppendLine(args.Data);
          };

          process.BeginErrorReadLine();
          process.BeginOutputReadLine();
          process.WaitForExit();
        }
      } finally {
        if (tmpOut == null) outFile.Close();
        else outFile.Flush();
      }

      if (ProcessOutputAndReturnTrueIfErrorsAreFound(fileName, errors))
        return null;

      if (tmpOut == null)
        return new StreamReader(outFileName);
      else {
        tmpOut.Seek(0, SeekOrigin.Begin);
        return new StreamReader(tmpOut);
      }
    }
    

    /// <summary>
    /// Determine the install location of cl.exe via the environment variables VS100COMNTOOLS or
    /// VS90COMNTOOLS and setup the start info to invoke the found instance of cl, unless an explicit 
    /// location has been given as command line option.
    /// </summary>
    private static ProcessStartInfo ConfigureStartInfoForClVersion11Or10Or9(VccOptions commandLineOptions) {
      var envPath = Environment.GetEnvironmentVariable("PATH");
      var envInclude = Environment.GetEnvironmentVariable("INCLUDE");
      if (envPath != "") envPath = envPath + ";";
      if (envInclude != "") envInclude = envInclude + ";";

      if (!String.IsNullOrEmpty(commandLineOptions.ClPath))
      {
        ProcessStartInfo result = new ProcessStartInfo("\"" + commandLineOptions.ClPath + "\"");

        try {
          FileInfo clPath = new FileInfo(commandLineOptions.ClPath);
          result.EnvironmentVariables["path"] = envPath
            + Path.Combine(clPath.Directory.Parent.Parent.FullName, @"Common7\IDE") + ";"
            + Path.Combine(clPath.Directory.Parent.Parent.Parent.FullName, @"Common7\IDE");

          result.EnvironmentVariables["include"] = envInclude 
            + Path.Combine(clPath.Directory.Parent.Parent.FullName, @"VC\INCLUDE") + ";"
            + Path.Combine(clPath.Directory.Parent.Parent.Parent.FullName, @"VC\INCLUDE");

        } catch (Exception) { } // we only do a best effort to set the path
        return result;
      } else {
        string VSCOMNTOOLS = Environment.GetEnvironmentVariable("VS110COMNTOOLS");
        if (VSCOMNTOOLS == null) VSCOMNTOOLS = Environment.GetEnvironmentVariable("VS100COMNTOOLS");
        if (VSCOMNTOOLS == null) VSCOMNTOOLS = Environment.GetEnvironmentVariable("VS90COMNTOOLS");
        if (VSCOMNTOOLS == null) throw new FileNotFoundException();
        string vsDir = new DirectoryInfo(VSCOMNTOOLS).Parent.Parent.FullName;
        ProcessStartInfo info = new ProcessStartInfo(Path.Combine(vsDir, @"vc\bin\cl.exe"));
        info.EnvironmentVariables["path"] = envPath + Path.Combine(vsDir, @"Common7\IDE");
        info.EnvironmentVariables["include"] = envInclude + Path.Combine(vsDir, @"VC\INCLUDE");
        return info;
      }
    }
  }
}
