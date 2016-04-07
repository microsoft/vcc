//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Threading;
using Z3AxiomProfiler.QuantifierModel;

namespace Z3AxiomProfiler
{

  public class ParameterConfiguration
  {
    public FileInfo preludeBplFileInfo = null;
    public FileInfo codeBplFileInfo = null;
    public string boogieOptions = "";
    public string z3Options = "";
    public int timeout = 0;
    public string functionName = "";
    public string z3LogFile = "";
    public string z3InputFile = null;
    public bool skipDecisions = false;
    public int checkToConsider = 1;


    static public ParameterConfiguration loadParameterConfigurationFromSettings()
    {
      ParameterConfiguration config = new ParameterConfiguration();

      string preludeBplFile = Properties.Settings.Default.PreludeBplFile;
      string codeBplFile = Properties.Settings.Default.CodeBplFile;

      config.preludeBplFileInfo = (preludeBplFile.Length > 0) ? new FileInfo(preludeBplFile) : null;
      config.codeBplFileInfo = (codeBplFile.Length > 0) ? new FileInfo(codeBplFile) : null;
      config.boogieOptions = Properties.Settings.Default.BoogieOptions;
      config.z3Options = Properties.Settings.Default.Z3Options;
      config.functionName = Properties.Settings.Default.FunctionName;
      config.timeout = Properties.Settings.Default.Timeout;
      config.z3LogFile = Properties.Settings.Default.LogFile;
      config.z3InputFile = Properties.Settings.Default.Z3InputFile;

      return config;
    }

    static public bool saveParameterConfigurationToSettings(ParameterConfiguration config)
    {
      try
      {
        Properties.Settings.Default.PreludeBplFile = config.preludeBplFileInfo.FullName;
        Properties.Settings.Default.CodeBplFile = config.codeBplFileInfo.FullName;
        Properties.Settings.Default.BoogieOptions = config.boogieOptions;
        Properties.Settings.Default.Z3Options = config.z3Options;
        Properties.Settings.Default.FunctionName = config.functionName;
        Properties.Settings.Default.Timeout = config.timeout;
        Properties.Settings.Default.LogFile = config.z3LogFile;
        Properties.Settings.Default.Z3InputFile = config.z3InputFile;

        Properties.Settings.Default.Save();
        return true;
      }
      catch
      {
        return false;
      }
    }

  }

  public delegate void loaderProgressUpdater(int perc, int a);

  public class Loader
  {
    private string workingDirectory;
    private Process currentProcess;

    private bool isCancelled = false;

    public event loaderProgressUpdater statusUpdate;

    private ParameterConfiguration config;
    public string z3OutputFile;
    private LogProcessor processor;

    public enum LoaderTask { LoaderTaskBoogie, LoaderTaskZ3, LoaderTaskParse };
    private LoaderTask task;

    public Loader(ParameterConfiguration config, LoaderTask task)
    {
      List<FileInfo> filelist = null;

      this.config = config;
      this.task = task;

      if (task == LoaderTask.LoaderTaskBoogie) {
        if ((config.preludeBplFileInfo == null) || (!config.preludeBplFileInfo.Exists)) {
          throw new Exception("Cannot load VCC prelude file.");
        }
        if ((config.codeBplFileInfo == null) || (!config.codeBplFileInfo.Exists)) {
          throw new Exception("Cannot load Boogie specification.");
        }
        filelist = new List<FileInfo> { config.preludeBplFileInfo, config.codeBplFileInfo };
      } else {
        filelist = new List<FileInfo>();
        if (config.preludeBplFileInfo != null) {
          if (!config.preludeBplFileInfo.Exists)
            throw new Exception("Cannot load VCC prelude file.");
          filelist.Add(config.preludeBplFileInfo);

        }

        if (config.codeBplFileInfo != null) {
          if (!config.codeBplFileInfo.Exists)
            throw new Exception("Cannot load Boogie specification.");
          filelist.Add(config.codeBplFileInfo);

        }
      }
      processor = new LogProcessor(filelist, config.skipDecisions, config.checkToConsider);
    }

    public void Cancel()
    {
      isCancelled = true; 
      if (currentProcess != null)
      {
        currentProcess.Kill();
      }
    }

    public void Load()
    {
      try {
        if (config.codeBplFileInfo == null && config.z3LogFile != null)
          workingDirectory = new FileInfo(config.z3LogFile).DirectoryName;
        else
          workingDirectory = config.codeBplFileInfo.DirectoryName;
        statusUpdate(0, 0);

        if (task == LoaderTask.LoaderTaskBoogie)
        {
          taskExecuteBoogieAndZ3();
        }
        else if (task == LoaderTask.LoaderTaskZ3)
        {
          taskExecuteZ3();
        }
        else if (task == LoaderTask.LoaderTaskParse)
        {
          taskLoadZ3LogFile(config.z3LogFile);
        }

        statusUpdate(1000, 3);
        Thread.Sleep(250);
      } catch (Exception e) {
        Console.WriteLine(e);
        throw;
      }
    }

    void taskLoadZ3LogFile(string logFile)
    {
      statusUpdate(0, 2);

      FileInfo fi = new FileInfo(logFile);
      long curPos = 0;
      int lineNo = 0;
      int oldperc = 0;
      processor.model.LogFileName = logFile;
      using (var rd = File.OpenText(logFile))
      {
        string l;
        while ((l = rd.ReadLine()) != null)
        {
          processor.ParseSingleLine(l);
          if (l != null)
            curPos += l.Length + 2;
          if (fi.Length != 0)
          {
            lineNo++;
            int perc = (int)(curPos * 999 / fi.Length);
            if (oldperc != perc)
            {
              statusUpdate(perc, 2);
              oldperc = perc;
            }
          }
        }
        processor.ComputeCost();
      }
      statusUpdate(1000, 2);
    }

    void taskExecuteZ3()
    {
      statusUpdate(0, 1);

      // Step 1: create Z3 input by running boogie for a very short period
      string proverLog = config.z3InputFile;
      string z3Log = Path.ChangeExtension(proverLog, "z3log");
      int timeout = (config.timeout >= 0) ? config.timeout : 0;
      step2RunZ3(proverLog, z3Log, timeout, config.z3Options);
      statusUpdate(0, 2);
    }

    void taskExecuteBoogieAndZ3()
    {
      // Step 1: produce Z3 log output + load it

      int timeout = (config.timeout >= 0) ? config.timeout : 0;
      step1RunBoogie(config.preludeBplFileInfo, config.codeBplFileInfo, config.functionName, timeout, config.boogieOptions);

      statusUpdate(0, 1); 
    }

    void step1RunBoogie(FileInfo preludeBplFile, FileInfo codeBplFile, string functionName, int timeOut, string boogieOptions)
    {
      string bplFilesString = String.Format("\"{0}\" \"{1}\"", (preludeBplFile == null) ? "" : preludeBplFile.FullName, codeBplFile);
      boogieOptions = boogieOptions ?? "";
      string z3Log = Path.ChangeExtension(config.codeBplFileInfo.FullName, "z3log");
      string arguments = String.Format(" {0} {1} /proc:{2} /z3opt:TRACE=true /z3opt:TRACE_FILE_NAME=\"'{3}'\" /z3opt:/T:{4}", 
                        bplFilesString, boogieOptions, functionName, z3Log.Replace("\\", "\\\\"), timeOut);
      Process process = createLoaderProcess("boogie.exe", arguments);
      if(isCancelled)
        return;
      process.Start();
      string output = process.StandardOutput.ReadToEnd();
      string error = process.StandardError.ReadToEnd();
      process.WaitForExit();

      if (process.ExitCode != 0)
      {
        throw new Exception(String.Format("Boogie exited with error code {0}. Aborting generation process.\n{1} {2}", process.ExitCode, output, error));
      }

      currentProcess = null;

      taskLoadZ3LogFile(z3Log);
    }

    void step2RunZ3(string proverLog, string outputFile, int timeOut, string z3options)
    {
      z3options = z3options ?? "";
      z3options = "NNF_SK_HACK=true QI_EAGER_THRESHOLD=10000 PHASE_SELECTION=0 RESTART_STRATEGY=0 RESTART_FACTOR=1.5 " + z3options;
      string z3Log = outputFile;
      string arguments = String.Format("\"{0}\" {1} TRACE=true TRACE_FILE_NAME=\"'{2}'\" /T:{3}", proverLog, z3options, z3Log.Replace("\\", "\\\\"), timeOut);
      Process process = createLoaderProcess("z3.exe", arguments);
     
      if (isCancelled)
        return;
      process.Start();

      string output = process.StandardOutput.ReadToEnd();
      string error = process.StandardError.ReadToEnd();
      
      process.WaitForExit();

      if (process.ExitCode != 0)
      {
        if ((process.ExitCode == 102) && (timeOut != 0))
        {
          // This exit code is produced on a timeout of Z3.
          // Additionally we requested a timeout from Z3. So there is no need
          // to throw an exception, since this is expected.
        }
        else
        {
          throw new Exception(String.Format("Z3 exited with error code {0}. Aborting generation process.\n{1} {2}", process.ExitCode, output, error));
        }
      }
      
      currentProcess = null;
      taskLoadZ3LogFile(z3Log);
    }

    Process createLoaderProcess(string executable, string arguments)
    {
      ProcessStartInfo startInfo = new ProcessStartInfo();
      startInfo.WorkingDirectory = workingDirectory;
      startInfo.FileName = executable;
      startInfo.ErrorDialog = false;

      startInfo.Arguments = arguments;
      startInfo.UseShellExecute = false;
      startInfo.CreateNoWindow = true;
      startInfo.RedirectStandardOutput = true;
      startInfo.RedirectStandardError = true;

      Process process = new Process();
      process.StartInfo = startInfo;
      currentProcess = process;
      return process;
    }

    public Model GetModel()
    {
      return processor.model;
    }
  }
}
