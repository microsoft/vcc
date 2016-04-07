//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading;
using Microsoft.Cci;

namespace Microsoft.Research.Vcc
{
  class TestRunner
  {
    /// <summary>
    /// Suffix used for generating names of temporary files (.c and .i) 
    /// used during run of test suites.
    /// </summary>
    const string vccSplitSuffix = "__vcc_split__";

    public static int RunTestSuite(VccOptions commandLineOptions) {
      return commandLineOptions.FileNames.Count(fileName => !RunTestSuite(fileName, commandLineOptions));
    }

    private static int NumThreads(double arg) {
        if (arg < 0) {
          return 1;
        }

        if (arg < 0.001) {
          return System.Environment.ProcessorCount;
        }

        if (arg < 2) {
          int result = (int) (System.Environment.ProcessorCount * arg);
          if (result < 1) result = 1;
          return result;
        } else {
          return (int) arg;
        }
    }

    static bool firstFile = true;
    static bool RunTestSuite(string fileName, VccOptions commandLineOptions)
    {
      if (File.Exists(fileName))
      {
        return TestRunner.RunTestSuite(new FileInfo(fileName), commandLineOptions);
      }

      string baseDir;
      string fileSpec;

      if (Directory.Exists(fileName)) {
        baseDir = fileName;
        fileSpec = "*";
      } else {

        baseDir = Path.GetDirectoryName(fileName);
        if (string.IsNullOrEmpty(baseDir)) baseDir = ".";
        fileSpec = Path.GetFileName(fileName);
        if (string.IsNullOrEmpty(fileSpec)) fileSpec = "*";
      }

      int errorCount = 0;
      int threads = NumThreads(commandLineOptions.RunTestSuiteMultiThreaded);
      TestRunnerMT trmt = threads > 1 ? new TestRunnerMT(threads, commandLineOptions) : null;

      foreach (FileInfo fi in new DirectoryInfo(baseDir).GetFiles(fileSpec, SearchOption.TopDirectoryOnly))
      {
        if (fi.Name.StartsWith(".")) continue;
        if (fi.Name.Contains(vccSplitSuffix)) continue;
        if (fi.Extension != ".c" && fi.Extension != "")
          continue;

        if (trmt != null) trmt.Queue(fi);
        else
        {
          if (!TestRunner.RunTestSuite(fi, commandLineOptions))
            errorCount++;
        }
      }

      if (trmt != null)
      {
        if (firstFile)
        {
          firstFile = false;
          if (File.Exists("testsuite.log"))
            File.Delete("testsuite.log");
        }
        errorCount += trmt.Run();
      }

      foreach (DirectoryInfo di in new DirectoryInfo(baseDir).GetDirectories(fileSpec, SearchOption.TopDirectoryOnly))
      {
        if (di.Name.StartsWith(".")) continue;
        RunTestSuite(di.FullName, commandLineOptions);
      }

      if (errorCount != 0)
      {
        Logger.Instance.NewLine();
        Logger.Instance.Error("*** {0} error(s) ***", errorCount);
        Logger.Instance.NewLine();
        return false;
      }

      return true;
    }

    public static string currentTestcaseName;

    static bool RunTestSuite(FileInfo testFile, VccOptions commandLineOptions) {
      using (var reader = new StreamReader(testFile.Open(FileMode.Open, FileAccess.Read)))
        return RunTestSuite(testFile.DirectoryName, testFile.Name, reader, commandLineOptions);
    }

    static bool RunTestSuite(string directoryName, string suiteName, StreamReader instream, VccOptions commandLineOptions) {
      var startTime = DateTime.UtcNow;
      System.Diagnostics.Debug.Listeners.Remove("Default");
      var errorHandler = new CciErrorHandler(commandLineOptions);
      StringBuilder source = null;
      StringBuilder expectedOutput = null;
      StringBuilder actualOutput = null;
        int errors = 0;
      int testCaseCount = 0;
      var WhiteSpaceChars = " \r\n\t".ToCharArray();

      try {
        int line = 1;

        while (!instream.EndOfStream) {
          var l = instream.ReadLine(); // strips Unix or Dos line ending
          line++;

          source = new StringBuilder();
            List<string> compilerParameters;
            if (l.StartsWith("`") || l.StartsWith("//`")) {
            string optionString = l.Substring(l.IndexOf('`') + 1);
            compilerParameters = optionString.Split(WhiteSpaceChars, StringSplitOptions.RemoveEmptyEntries).ToList();
          } else {
            compilerParameters = new List<string>();
            source.Append(l);
            source.Append("\r\n");
          }

          while (!instream.EndOfStream) {
            l = instream.ReadLine();
            line++;
            if (l == "`" || l == "/*`")
              break;
            source.Append(l);
            source.Append("\r\n");
          }

          if (instream.EndOfStream) {
            Logger.Instance.Error("The last test case in the suite has not been provided with expected output");
            errors++;
            break;
          }
          
          int errLine = line;
          expectedOutput = new StringBuilder();
          while (!instream.EndOfStream) {
            l = instream.ReadLine();
            line++;
            if (l == "`" || l == "`*/")
              break;
            expectedOutput.Append(l);
            expectedOutput.Append("\r\n");
          }

          if (l != "`" && l != "`*/") {
            Logger.Instance.Error("The last test case in the suite has been provided with incomplete expected output");
            errors++;
            break;
          }

          actualOutput = new StringBuilder();
          TextWriter savedOut = Console.Out;
          Console.SetOut(new StringWriter(actualOutput));
          System.Diagnostics.TextWriterTraceListener myWriter = new System.Diagnostics.TextWriterTraceListener(System.Console.Out);
          System.Diagnostics.Debug.Listeners.Add(myWriter);

          ++testCaseCount;
          string suiteNameWithoutExt = Path.GetFileNameWithoutExtension(suiteName);
          string fileNameWithoutExt;

          if (commandLineOptions.OutputDir != null)
          {
              fileNameWithoutExt = commandLineOptions.OutputDir;
          }
          else
          {
              fileNameWithoutExt = directoryName;
          }

          fileNameWithoutExt += Path.DirectorySeparatorChar + suiteNameWithoutExt + vccSplitSuffix + testCaseCount + "_" + System.Diagnostics.Process.GetCurrentProcess().Id;
          currentTestcaseName = Path.GetFileName(string.Format("{0}.{1:00}", suiteNameWithoutExt, testCaseCount));

          try {
            int returnCode = RunTest(errorHandler, suiteNameWithoutExt, fileNameWithoutExt, source.ToString(), commandLineOptions, compilerParameters);
            if (returnCode < 0)
              actualOutput.Append("Non zero return code: " + returnCode);
          } catch (System.Reflection.TargetInvocationException e) {
            actualOutput.Append(e.InnerException);
          } catch (Exception e) {
            actualOutput.Append(e);
          } 

          Logger.Instance.ResetReportedErrors();
          Console.SetOut(savedOut);
          System.Diagnostics.Debug.Listeners.Remove(myWriter);
          Regex rx = new Regex(@"[a-zA-Z]:\\.*?\\(.*)" + vccSplitSuffix + @"[0-9_]*.c\(");
          string actualOutputRepl = rx.Replace(actualOutput.ToString(), "testcase(");
          actualOutputRepl = actualOutputRepl.Trim();

          var expected = expectedOutput.ToString().Trim();
          if (!expected.Equals(actualOutputRepl)) {
            ReportError(suiteName, source, expected, actualOutputRepl, errLine, errors++ == 0);
          }

        }
        instream.Close();
        var runtime = DateTime.UtcNow.Subtract(startTime).TotalSeconds;
        if (errors == 0)
          Logger.Instance.Log("{0} passed [{1:0.00}]", suiteName, runtime);
        else {
          Logger.Instance.NewLine();
          Logger.Instance.Error("{0} had {1} failure(s) [{2:0.00}]", suiteName, errors, runtime);
        }
      } catch {
        var expected = expectedOutput == null ? "<none>" : expectedOutput.ToString().Trim();
        ReportError(suiteName, source, expected, actualOutput.ToString(), -1, true);
      }
      return errors == 0;
    }

    private static void ReportError(string suiteName, StringBuilder source, string expectedOutput, string actualOutput, int errLine, bool printBanner)
    {
      if (printBanner) {
        Logger.Instance.NewLine();
        Logger.Instance.Error("----------------------------- " + suiteName + " failed -----------------------------");
      }
      Logger.Instance.NewLine();
      if (errLine > 0)
        Logger.Instance.Log("*** source({0}):", errLine);
      else
        Logger.Instance.Log("*** source:");
      if (source != null) {
        Logger.Instance.Log(source.ToString());
        Logger.Instance.NewLine();
      }
      Logger.Instance.Log("*** actual output:");
      Logger.Instance.Log(actualOutput);
      Logger.Instance.Log("***");
      Logger.Instance.NewLine();
      Logger.Instance.Log("*** expected output:");
      Logger.Instance.Log(expectedOutput);
      Logger.Instance.Log("***");
      Logger.Instance.NewLine();
    }

    private static int RunTest(CciErrorHandler errorHandler, string suiteName, string fileNameWithoutExt,
                               string test, VccOptions commandLineOptions, List<string> compilerParameters) {

      VccCommandLineHost.ResetErrorCount();
      string fileNameC = fileNameWithoutExt + ".c";
      string fileNameI = fileNameWithoutExt + ".i";

      StreamWriter tempStreamWriter = new StreamWriter(fileNameC);
      tempStreamWriter.Write(test);
      tempStreamWriter.Close();

      VccOptions options = new VccOptions();
      options.CopyFrom(commandLineOptions);

      if (compilerParameters != null)
        options = OptionParser.ParseCommandLineArguments(VccCommandLineHost.dummyHostEnvironment, compilerParameters, options);

      options.NoPreprocessor = false;
      options.CheckedArithmetic = true;
      options.RunTestSuite = true;
      options.FileNames = new List<string> { fileNameC };

      HostEnvironment hostEnvironment = new HostEnvironment(options.PointerSize);
      hostEnvironment.Errors += errorHandler.HandleErrors;

      bool errorsInPreprocessor;
      var f = CCompilerHelper.Preprocess(options, out errorsInPreprocessor);
      if (errorsInPreprocessor) return -1;
      var st = f.First();
      test = st.ReadToEnd();
      st.Close();
      File.Delete(fileNameC);
      // if (!options.KeepPreprocessorFiles) File.Delete(fileNameI);

      IName name = hostEnvironment.NameTable.GetNameFor(suiteName);
      List<IAssemblyReference> assemblyReferences = new List<IAssemblyReference>();
      List<IModuleReference> moduleReferences = new List<IModuleReference>();
      assemblyReferences.Add(hostEnvironment.LoadAssembly(hostEnvironment.CoreAssemblySymbolicIdentity));
      assemblyReferences.Add(hostEnvironment.LoadAssembly(hostEnvironment.VccRuntimeAssemblyIdentity));
      VccAssembly/*?*/ assem = null;    
      if (hostEnvironment.previousDocument == null || compilerParameters == null ||
          !compilerParameters.Contains("/incremental"))
      {
        List<VccSourceDocument> programSources = new List<VccSourceDocument>(1);
        assem = new VccAssembly(name, "", hostEnvironment, options, assemblyReferences, moduleReferences, programSources);
        var helper = new VccCompilationHelper(assem.Compilation);
        programSources.Add(hostEnvironment.previousDocument = new VccSourceDocument(helper, name, name.ToString(), test));
      }
      VccCommandLineHost.ResetStartTime();
      return VccCommandLineHost.Felt2Cast2Plugin("testcase", options, hostEnvironment, assem);
    }

    class TestRunnerMT
    {
      readonly VccOptions commandLineOptions;
      readonly int threadCount;
      readonly Queue<FileInfo> queue = new Queue<FileInfo>();
      readonly object lkQueue = new object();
      readonly object lkOutput = new object();
      long maxBytesPerProcess;
      int errorCount;
      int runningThreadCount;
      int totalTestCount;
      int failedTestCount;
      int passedTestCount;
      StreamWriter globalLogFile;

      public TestRunnerMT(int threadCount, VccOptions commandLineOptions) {
        this.threadCount = threadCount;
        this.commandLineOptions = commandLineOptions;
      }

      public void Queue(FileInfo job) {
        this.queue.Enqueue(job);
      }

      private System.Diagnostics.ProcessStartInfo VccStartInfo(IEnumerable<FileInfo> jobs) {
        System.Diagnostics.ProcessStartInfo result = new System.Diagnostics.ProcessStartInfo ();
        foreach (var arg in this.commandLineOptions.HandledOptions) {
          var opt = arg.Substring(1);
          if (opt.StartsWith("smt") || opt.StartsWith("suitemt")) continue;
          result.Arguments += " " + arg;
        }
        foreach (var job in jobs) { result.Arguments += " \"" + job.FullName + "\""; }        
        result.CreateNoWindow = true;
        result.FileName = typeof(TestRunnerMT).Assembly.Location;
        result.UseShellExecute = false;
        result.RedirectStandardError = true;
        result.RedirectStandardOutput = true;
        return result;
      }

      class Runner
      {
        private static readonly Regex TestPassed = new Regex("^\\S+ passed \\[.*\\]$");
        private static readonly Regex TestFailed = new Regex("--- \\S+ failed ---");
        private readonly List<string> stdout = new List<string>();
        private readonly List<string> stderr = new List<string>();
        private readonly TestRunnerMT parent;
        private int needFlush;
        private readonly object dataLock = new object();

        public Runner(TestRunnerMT p)
        {
          parent = p;
        }

        private void Flush()
        {
          if (needFlush == 0) return;
          lock (parent.globalLogFile) {
            foreach (var v in stderr)
              parent.globalLogFile.WriteLine(v);
            foreach (var v in stdout)
              parent.globalLogFile.WriteLine(v);
            stderr.Clear();
            stdout.Clear();
            parent.globalLogFile.Flush();
            needFlush = 0;
          }
        }

        private void GotStdout(object sender, System.Diagnostics.DataReceivedEventArgs data)
        {
          var line = data.Data;

          if (String.IsNullOrEmpty(data.Data)) return;

          lock (dataLock) {
            if (TestPassed.IsMatch(line)) {
              Flush();
              Interlocked.Increment(ref parent.passedTestCount);
            } else if (TestFailed.IsMatch(line)) {
              Flush();
              Interlocked.Increment(ref parent.failedTestCount);
              needFlush++;
              lock (parent.lkOutput)
                Logger.Instance.Log(line);
            }
            stdout.Add(line);
          }
        }

        private void GotStderr(object sender, System.Diagnostics.DataReceivedEventArgs data)
        {
          var line = data.Data;
          if (String.IsNullOrEmpty(line)) return;
          lock (dataLock) {
            stderr.Add(line);
            needFlush++;
          }
        }

        public void Run(IEnumerable<FileInfo> jobs)
        {
          using (var vccProc = System.Diagnostics.Process.Start(parent.VccStartInfo(jobs))) {
            vccProc.PriorityClass = System.Diagnostics.ProcessPriorityClass.AboveNormal;
            vccProc.OutputDataReceived += this.GotStdout;
            vccProc.ErrorDataReceived += this.GotStderr;

            vccProc.BeginOutputReadLine();
            vccProc.BeginErrorReadLine();
            vccProc.WaitForExit();

            needFlush++;
            Flush();

            if (vccProc.ExitCode != 0) System.Threading.Interlocked.Increment(ref parent.errorCount);
          }
        }
      }

      private void RunJobSequence(IEnumerable<FileInfo> jobs) {
        new Runner(this).Run(jobs);
      }

      private void RunJobs() {
        System.Threading.Interlocked.Increment(ref this.runningThreadCount);
        while (true) {
          var jobSequence = new List<FileInfo>();
          long totalSize = 0;
          lock (lkQueue) {
            while (queue.Count > 0) {
              var job = queue.Peek();
              if (jobSequence.Count > 0 && totalSize + job.Length > maxBytesPerProcess)
                break;
              if (jobSequence.Count > 50)
                break;
              queue.Dequeue();
              totalSize += job.Length;
              jobSequence.Add(job);
            }
          }
          if (jobSequence.Count == 0) break;
          RunJobSequence(jobSequence);
        }
      }

      private void Report(string app)
      {
        lock(lkOutput)
          System.Console.Write("Passed {0}, failed {1}, total {2}{3}", this.passedTestCount, this.failedTestCount, this.totalTestCount, app);
      }

      private void Reporter()
      {
        while (true) {
          Report("\r");
          Thread.Sleep(500);
        }
      }

      private void SpawnRunAndJoin() {
        List<System.Threading.Thread> threads = new List<System.Threading.Thread>(this.threadCount);
        for (int i = 0; i < this.threadCount; i++) {
          System.Threading.Thread thread = new System.Threading.Thread(RunJobs);
          thread.Start();
          threads.Add(thread);
        }

        // wait for all threads to come up becaue attempting to join them before will raise an exception
        while (this.runningThreadCount < this.threadCount) System.Threading.Thread.Sleep(50);

        var reporter = new Thread(Reporter);
        reporter.Start();

        for (int i = 0; i < this.threadCount; i++)
          threads[i].Join();

        reporter.Abort();
        reporter.Join();

        Report("\r\n");
      }

      public int Run() {
        errorCount = 0;
        runningThreadCount = 0;
        long totalBytes = 0;
        foreach (var job in queue) {
          totalBytes += job.Length;
        }
        totalTestCount = queue.Count;
        maxBytesPerProcess = totalBytes / this.threadCount;
        if (maxBytesPerProcess > 10000)
          maxBytesPerProcess /= 4;
        using (globalLogFile = new StreamWriter("testsuite.log", true)) {
          SpawnRunAndJoin();
        }
        return errorCount;
      }
    }
  }
}
