//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using Microsoft.Boogie;
using Microsoft.Cci;

namespace Microsoft.Research.Vcc
{

  public class VccCommandLineHost
  {
    const string StandardPreludePath = "Vcc3Prelude.bpl";

    /// <summary>
    /// The main entry point for the application.
    /// </summary>
    [STAThread]
    public static int Main(string[] args)
    {
      swTotal.Start();

      // reference symbol from Z3 so it gets copied
#pragma warning disable 168
      var y = new Microsoft.Boogie.SMTLib.Factory();
#pragma warning restore 168

      Logger.Instance.Register(ConsoleLogger.Instance);

      try
      {

          startTime = GetTime();
          cciErrorHandler = new CciErrorHandler();
          dummyHostEnvironment.Errors += cciErrorHandler.HandleErrors;
          var commandLineOptions = OptionParser.ParseCommandLineArguments(dummyHostEnvironment, args);
          commandLineOptions.RunningFromCommandLine = true;
          cciErrorHandler.CommandLineOptions = commandLineOptions;
          verificationErrorHandler = new VerificationErrorHandler(commandLineOptions);

          if (commandLineOptions.DisplayCommandLineHelp)
          {
              DisplayCommandLineHelp();
              return 0;
          }

          if (commandLineOptions.DisplayVersion)
          {
              DisplayVersion();
              return 0;
          }

          if (errorCount > 0 || fileErrorCount > 0)
          {
              Console.Error.WriteLine("Exiting with 1 - error parsing arguments.");
              return 1;
          }

          if (commandLineOptions.RunTestSuite) {
            Logger.Instance.Unregister(ConsoleLogger.Instance);
            Logger.Instance.Register(new ConsoleLoggerForTestRun());
          } 
          
          if (!String.IsNullOrEmpty(commandLineOptions.XmlLogFile)) {
              Stream xmlStream = File.Open(commandLineOptions.XmlLogFile, FileMode.Create, FileAccess.Write);
              Logger.Instance.Register(new XmlLogger(xmlStream));
          }

          if ((currentPlugin = InitializePlugin(commandLineOptions)) == null)
          {
              Logger.Instance.Log("Exiting with 2 - error initializing plugin.");
              return 2;
          }

          if (commandLineOptions.RunTestSuite)
              errorCount = TestRunner.RunTestSuite(commandLineOptions);
          else
              RunPlugin(commandLineOptions);

          swTotal.Stop();

          DumpTimes(commandLineOptions);

          int retVal = 0;

          if (errorCount > 0)
          {
              Logger.Instance.Error("Exiting with 3 ({0} error(s).)", errorCount);
              retVal = 3;
          }

          return retVal;
      }
      finally
      {
          Logger.Instance.Dispose();
      }              
    }

    internal static VerificationErrorHandler ErrorHandler
    {
      get { return verificationErrorHandler; }
    }

    static VerificationErrorHandler verificationErrorHandler;
    static CciErrorHandler cciErrorHandler;
    static PluginManager pluginManager;

    private static void PrintPluginMessage(object sender, string message)
    {
      Logger.Instance.Log(message);
    }

    static readonly Stopwatch swVisitor = new Stopwatch("FELT Visitor");
    static readonly Stopwatch swPlugin = new Stopwatch("Total Plugin");
    static readonly Stopwatch swPrelude = new Stopwatch("Prelude");
    static readonly Stopwatch swTotal = new Stopwatch("Total");

    private static Plugin InitializePlugin(VccOptions commandLineOptions)
    {
      try
      {
        string pluginName = null;
        Plugin selectedPlugin = null;
        VCGenPlugin vcgenPlugin = null;

        if (commandLineOptions.PluginOptions.Count != 0 || commandLineOptions.DisplayCommandLineHelp)
        {
          pluginManager = new PluginManager(commandLineOptions);
          string pluginDir = PathHelper.PluginDir;
          if (pluginDir != null) pluginManager.AddPluginDirectory(pluginDir);
          pluginManager.Discover();
          foreach (var opt in commandLineOptions.PluginOptions.Keys)
          {
            if (opt == "dir") continue;
            if (pluginName == null)
            {
              pluginName = opt;
            }
            else
            {
              Logger.Instance.Error("More than one plugin requested ('{0}' and '{1}').", pluginName, opt);
              return null;
            }
          }

          if (pluginName != null)
          {
            foreach (var plugin in pluginManager.Plugins)
            {
              if (string.Compare(pluginName, plugin.Name(), true) == 0)
              {
                if (selectedPlugin != null)
                {
                  Logger.Instance.Error("More than one plugin matches '{0}'.", pluginName);
                  return null;
                }
                selectedPlugin = plugin;
              }
            }
            if (selectedPlugin == null)
            {
              foreach (var plugin in pluginManager.VCGenPlugins)
              {
                if (string.Compare(pluginName, plugin.Name, true) == 0)
                {
                  if (vcgenPlugin != null)
                  {
                    Logger.Instance.Error("More than one VCGEN plugin matches '{0}'.", pluginName);
                    return null;
                  }
                  vcgenPlugin = plugin;
                }
              }

              if (vcgenPlugin == null)
              {
                Logger.Instance.Error("Plugin '{0}' not found.", pluginName);
                return null;
              }
            }
          }
        }

        if (selectedPlugin == null) selectedPlugin = new VccPlugin(vcgenPlugin); // the default

        selectedPlugin.RegisterStopwatch(swTotal);
        selectedPlugin.RegisterStopwatch(swVisitor);
        selectedPlugin.RegisterStopwatch(swPlugin);
        selectedPlugin.RegisterStopwatch(swPrelude);
        selectedPlugin.MessageHandler.AddHandler(PrintPluginMessage);

        try
        {
          swPlugin.Start();
          selectedPlugin.UseOptions(new VccOptionWrapper(commandLineOptions));
          if (pluginName != null)
            selectedPlugin.UseCommandLineOptions(commandLineOptions.PluginOptions[pluginName]);
        }
        finally
        {
          swPlugin.Stop();
        }

        return selectedPlugin;

      }
      catch (System.Reflection.ReflectionTypeLoadException e)
      {
        foreach (Exception ex in e.LoaderExceptions)
        {
          Logger.Instance.Error(ex.Message);
          Logger.Instance.Error(ex.StackTrace);
        }
      }
      return null;
    }

    private static double startTime;
    internal static HostEnvironment dummyHostEnvironment = new HostEnvironment(64);

    private static void DisplayCommandLineHelp()
    {
      System.Resources.ResourceManager rm = new System.Resources.ResourceManager("Microsoft.Research.Vcc.Host.ErrorMessages", typeof(VccCommandLineHost).Assembly);
// ReSharper disable ResourceItemNotResolved
      Console.Out.WriteLine(rm.GetString("Usage"));
// ReSharper restore ResourceItemNotResolved
      if (pluginManager != null && pluginManager.Plugins != null)
      {
        foreach (var plugin in pluginManager.Plugins)
        {
          Console.WriteLine();
          Console.WriteLine("--------------------------- Plugin: {0} ---------------------------", plugin.Name());
          Console.WriteLine();
          Console.WriteLine(plugin.Help());
          Console.WriteLine();
        }
      }
    }

    private static string GetZ3Version()
    {
      ProcessStartInfo z3Psi = new ProcessStartInfo("z3.exe", "/version") { CreateNoWindow = true, UseShellExecute = false, RedirectStandardOutput = true };
      try
      {
        using (Process z3Proc = Process.Start(z3Psi))
        {
          z3Proc.WaitForExit();
          var z3VersionString = z3Proc.StandardOutput.ReadToEnd();
          Regex regex = new Regex("(?<major>\\d+)\\s+(?<minor>\\d+)\\s+(?<build>\\d+)\\s+(?<revision>\\d+)");
          var match = regex.Match(z3VersionString);
          if (match.Success)
          {
            return String.Format("{0}.{1}.{2}.{3}", match.Groups["major"].Value, match.Groups["minor"].Value, match.Groups["build"].Value, match.Groups["revision"].Value);
          }
          return z3VersionString;
        }
      }
      catch (Exception)
      {
        return "unknow";
      }
    }

    private static void DisplayVersion() 
    {
      string vccVersionString = System.Diagnostics.FileVersionInfo.GetVersionInfo(System.Reflection.Assembly.GetExecutingAssembly().Location).FileVersion;
      string boogieVersionString = System.Diagnostics.FileVersionInfo.GetVersionInfo(typeof(Boogie.Parser).Assembly.Location).FileVersion;
      string z3VersionString = GetZ3Version();

      System.Resources.ResourceManager rm = new System.Resources.ResourceManager("Microsoft.Research.Vcc.Host.ErrorMessages", typeof(VccCommandLineHost).Assembly);
// ReSharper disable AssignNullToNotNullAttribute
// ReSharper disable ResourceItemNotResolved
      Logger.Instance.Log(rm.GetString("Version"), vccVersionString, boogieVersionString, z3VersionString);
// ReSharper restore ResourceItemNotResolved
// ReSharper restore AssignNullToNotNullAttribute
    }

    static int fileErrorCount;
    static int errorCount;

    public static void IncreaseErrorCount(bool isFileSpecific = true)
    {
      if (isFileSpecific) { fileErrorCount++; } else { errorCount++; }
    }

    public static void ResetErrorCount()
    {
      fileErrorCount = errorCount = 0;
    }

    static void RunPlugin(VccOptions commandLineOptions)
    {
      bool errorsInPreprocessor;

      var processedFiles = CCompilerHelper.Preprocess(commandLineOptions, out errorsInPreprocessor);
      if (errorsInPreprocessor) 
      {
          errorCount++;
          return;
      }
      using (var fnEnum = commandLineOptions.FileNames.GetEnumerator())
      using (var ppEnum = processedFiles.GetEnumerator())
        while (fnEnum.MoveNext() && ppEnum.MoveNext())
          RunPlugin(fnEnum.Current, ppEnum.Current, commandLineOptions);

      if (fileErrorCount > 0) errorCount++;
    }

    private static Plugin currentPlugin;
    private static void RunPlugin(string fileName, StreamReader instream, VccOptions commandLineOptions)
    {
      HostEnvironment hostEnvironment = new HostEnvironment(commandLineOptions.PointerSize);
      hostEnvironment.Errors += new CciErrorHandler(commandLineOptions).HandleErrors;
      IName assemName = hostEnvironment.NameTable.GetNameFor(Path.GetFileNameWithoutExtension(fileName));
      IName docName = hostEnvironment.NameTable.GetNameFor(Path.GetFileName(fileName));
      List<IAssemblyReference> assemblyReferences = new List<IAssemblyReference>();
      List<IModuleReference> moduleReferences = new List<IModuleReference>();
      assemblyReferences.Add(hostEnvironment.LoadAssembly(hostEnvironment.CoreAssemblySymbolicIdentity));
      assemblyReferences.Add(hostEnvironment.LoadAssembly(hostEnvironment.VccRuntimeAssemblyIdentity));
      List<VccSourceDocument> programSources = new List<VccSourceDocument>(1);
      VccAssembly assem = new VccAssembly(assemName, Path.GetFullPath(fileName), hostEnvironment, commandLineOptions, assemblyReferences, moduleReferences, programSources);
      VccCompilationHelper helper = new VccCompilationHelper(assem.Compilation);
      programSources.Add(new VccSourceDocument(helper, docName, Path.GetFullPath(fileName), instream));
      if (0 != Felt2Cast2Plugin(fileName, commandLineOptions, hostEnvironment, assem)) 
      {
          fileErrorCount++;
      }
    }

    private static string FunctionOrTypeRoot(string name)
    {
      name = name.Replace(':', '#');
      int pos = name.IndexOf('#');
      if (pos <= 0) return name;
      return name.Substring(0, pos);
    }

    public static void ResetStartTime()
    {
      startTime = GetTime();
    }

    internal static string FindMemberNameByLocation(string fileLoc, VccAssembly assem)
    {
      var colonPos = fileLoc.LastIndexOf(':');
      if (colonPos == -1 || colonPos == 0 || colonPos == fileLoc.Length - 1)
      {
        Logger.Instance.Error("invalid source location '{0}' .", fileLoc);
        errorCount++;
        return null;
      }

      var fileName = fileLoc.Substring(0, colonPos);
      uint fileLine;

      if (!uint.TryParse(fileLoc.Substring(colonPos + 1), out fileLine))
      {
        Logger.Instance.Error("invalid source location line '{0}' .", fileLoc.Substring(colonPos + 1));
        errorCount++;
        return null;
      }

      var fullPath = Path.GetFullPath(fileName);

      foreach (var member in ((IAssembly)assem).NamespaceRoot.Members)
      {
        var ploc = new VisitorHelper.DeferredToken(member.Locations).GetToken() as IOriginalDocumentLocation;
        if (ploc != null && 
          fullPath.Equals(Path.GetFullPath(ploc.OriginalDocumentLocation), StringComparison.OrdinalIgnoreCase) &&
          ploc.StartLine <= fileLine &&
          ploc.EndLine >= fileLine)
        {
          return member.Name.Value;
        }
      }

      Logger.Instance.Error( "could not find source item with location '{0}'", fileLoc);
      errorCount++;
      return null;
    }

    internal static int Felt2Cast2Plugin(string fileName, VccOptions commandLineOptions, HostEnvironment hostEnvironment, VccAssembly assem)
    {
      try
      {

        TransHelper.TransEnv helperenv;
        FSharp.Collections.FSharpList<CAST.Top> res;

        try
        {
          swVisitor.Start();
          helperenv = new TransEnv(hostEnvironment, commandLineOptions);
          var visitor = new Microsoft.Research.Vcc.Visitor(assem.Compilation.ContractProvider, helperenv);

          if (commandLineOptions.VerificationLocation != null)
          {
            var memberAtLoc = FindMemberNameByLocation(commandLineOptions.VerificationLocation, assem);
            if (memberAtLoc != null)
            {
              commandLineOptions.Functions.Add(memberAtLoc);
            }
          }

          try
          {
            if (commandLineOptions.AggressivePruning && (commandLineOptions.Functions.Count > 0 || commandLineOptions.FunctionsWithExactName.Count > 0))
            {
              var pruningRoots = new List<string>();
              pruningRoots.AddRange(commandLineOptions.Functions.ConvertAll(FunctionOrTypeRoot));
              pruningRoots.AddRange(commandLineOptions.FunctionsWithExactName.ConvertAll(FunctionOrTypeRoot));
              visitor.VisitOnly(assem, pruningRoots);
            }
            else
              ((ICodeVisitor)visitor).Visit(assem);
          }
          catch 
          {
            if (helperenv.ShouldDumpStack) throw;
            return 0;
          }

          res = visitor.GetResult();
        }
        finally
        {
          swVisitor.Stop();
        }

        if (fileErrorCount > 0) return fileErrorCount;

        try
        {
          swPlugin.Start();
          if (currentPlugin.IsModular())
          {
            var fv = currentPlugin.GetFunctionVerifier(fileName, helperenv, res);
            if (helperenv.ShouldContinue && fileErrorCount == 0)
              VerifyFunctions(commandLineOptions, fileName, assem.Name.ToString(), fv);
          }
          else
          {
            currentPlugin.Verify(fileName, helperenv, res);
          }
        }
        finally
        {
          errorCount += fileErrorCount;
          fileErrorCount = 0;
          swPlugin.Stop();
        }

        return 0;

      }
      catch (ProverDiedException e)
      {
        // we might want to do something else for this one
        Logger.Instance.NewLine();
        Logger.Instance.Error(e.Message);
      }
      catch (UnexpectedProverOutputException e)
      {
        Logger.Instance.NewLine();
        Logger.Instance.Error(e.Message);
      }
      catch (Exception e)
      {
        Logger.Instance.NewLine();
        Logger.Instance.Error(e.Message);
      }

      return -2;
    }

    private static void VerifyFunctions(VccOptions commandLineOptions, string fileName, string baseName, FunctionVerifier fver)
    {
      double beforeBoogie = GetTime();
      int numErrors = 0;
      double beforeMethods = GetTime();
      bool checkSpecificFunctions = commandLineOptions.ExplicitTargetsGiven;
      List<string> foundFunctionSpecifiers = new List<string>();

      if (commandLineOptions.DumpBoogie)
      {
        fver.DumpInternalsToFile(baseName, true);
      }

      foreach (var func in fver.FunctionsToVerify())
      {

        if (checkSpecificFunctions)
        {
          // check if this function has been requested either specifically or by prefix
          bool checkThisFunction = false;
          if (commandLineOptions.FunctionsWithExactName.Contains(func.Item2))
          {
            checkThisFunction = true;
            foundFunctionSpecifiers.Add(func.Item2);
          }
          if (!checkThisFunction)
          {
            foreach (var fn in commandLineOptions.Functions)
            {
              var normalized = fn.Replace(':', '#');
              if (func.Item2.StartsWith(normalized) &&
                   (normalized.Length == func.Item2.Length || func.Item2[normalized.Length] == '#'))
              {
                checkThisFunction = true;
                foundFunctionSpecifiers.Add(fn);
                break;
              }
            }
          }
          if (!checkThisFunction) continue;
        }
        else if (commandLineOptions.IgnoreIncludes != null)
        {
          bool fileFound = false;
          if (commandLineOptions.IgnoreIncludes == "")
          {
            if (commandLineOptions.FileNames.Any(file => String.Equals(file, func.Item1, StringComparison.OrdinalIgnoreCase)))
            {
              fileFound = true;
            }
          } else if (String.Equals(Path.GetFullPath(commandLineOptions.IgnoreIncludes), func.Item1, StringComparison.OrdinalIgnoreCase))
          {
            fileFound = true;
          }

          if (!fileFound) continue;
        }

        var outcome = fver.Verify(func.Item2);
        //verificationErrorHandler.FlushErrors();

        if (commandLineOptions.DumpBoogie) {
          fver.DumpInternalsToFile(baseName, false);
        }
       
        if (outcome == VerificationResult.Succeeded || outcome == VerificationResult.Skipped) { } else { numErrors++; }
      }

      if (checkSpecificFunctions)
      {
        List<string> functionSpecifiers = new List<string>();
        functionSpecifiers.AddRange(commandLineOptions.Functions);
        functionSpecifiers.AddRange(commandLineOptions.FunctionsWithExactName);
        // some functions have not been encountered; warn about those
        foreach (var fn in functionSpecifiers)
        {
          if (!foundFunctionSpecifiers.Contains(fn))
          {
            Logger.Instance.Error("'{0}' did not match any function.", fn);
            errorCount++;
          }
        }
      }

      fver.Close();
      double now = GetTime();

      var timerInfo =
        commandLineOptions.TimeStats ?
          new[] {
            Tuple.Create("total", now - startTime),
            Tuple.Create("compiler", beforeBoogie - startTime),
            Tuple.Create("boogie", beforeMethods - beforeBoogie),
            Tuple.Create("verification", now - beforeMethods)
        }
        : null;

        Logger.Instance.LogFileSummary(fileName, numErrors, timerInfo);
    }

    private static void DumpTimes(VccOptions commandLineOptions)
    {
      if (commandLineOptions.DetailedTimes)
      {
        foreach (var s in currentPlugin.Stopwatches)
        {
          Logger.Instance.Log(s.Display());
        }
      }
    }

    internal static Program StandardPrelude(VccOptions options)
    {
        // For now Boogie does not support reusing the prelude.

        //if (standardPrelude == null)
        //  standardPrelude = GetStandardPrelude();
        //return standardPrelude;

        try
        {
          swPrelude.Start();
          return GetStandardPrelude(options);
        }
        finally
        {
          swPrelude.Stop();
        }
    }

    public static string preludePath = "";
    // [Once]

    public static IList<String> StandardPreludeLines
    {
      get { return standardPreludeLines.AsReadOnly(); }
    }

    static List<String> standardPreludeLines;

    private static Program GetStandardPrelude(VccOptions options)
    {
      string _preludePath = string.IsNullOrEmpty(options.PreludePath) ? PathHelper.PreludePath(StandardPreludePath) : options.PreludePath;
      if (standardPreludeLines == null)
      {
        var lines = File.ReadAllLines(_preludePath, Encoding.UTF8);
        standardPreludeLines = new List<string>(lines);
      }

      Program prelude;
      int _errorCount = Boogie.Parser.Parse(_preludePath, new List<string>(), out prelude);
      if (prelude == null || _errorCount > 0)
      {
        Logger.Instance.Error("There were errors parsing Vcc3Prelude.bpl.");
        return new Program();
      }
      else
      {
        return prelude;
      }
    }

    internal static double GetTime()
    {
      return System.Environment.TickCount / 1000.0;
    }
  }

  class BoogieErrorSink : IErrorSink
  {

    public BoogieErrorSink(bool noPreprocessor)
    {
      this.noPreprocessor = noPreprocessor;
    }

    readonly bool noPreprocessor;

    public void Error(IToken tok, string msg)
    {
      Logger.Instance.LogWithLocation(null, msg, new Location(tok.filename, tok.line, noPreprocessor ? -1 : tok.col), LogKind.Error, false);
    }
  }


  internal class HostEnvironment : SourceEditHostEnvironment
  {

    internal HostEnvironment(int pointerSizeInBits)
      : base(new NameTable(), new InternFactory(), (byte)(pointerSizeInBits / 8), null, false)
    {
      Debug.Assert(pointerSizeInBits == 32 || pointerSizeInBits == 64);
      this.peReader = new PeReader(this);
      string loc = typeof(object).Assembly.Location;
      System.Reflection.AssemblyName mscorlibName = new System.Reflection.AssemblyName(typeof(object).Assembly.FullName);
      var tempMscorlibIdentity = new AssemblyIdentity(this.NameTable.GetNameFor(mscorlibName.Name), "", mscorlibName.Version, mscorlibName.GetPublicKeyToken(), loc);
      this.RegisterAsLatest(this.peReader.OpenAssembly(BinaryDocument.GetBinaryDocumentForFile(tempMscorlibIdentity.Location, this), out this.mscorlibIdentity));
      loc = typeof(Microsoft.Research.Vcc.Runtime).Assembly.Location;
      System.Reflection.AssemblyName runtimeName = new System.Reflection.AssemblyName(typeof(Microsoft.Research.Vcc.Runtime).Assembly.FullName);
      var tempVccRuntimeAssemblyIdentity = new AssemblyIdentity(this.NameTable.GetNameFor(runtimeName.Name), "", runtimeName.Version, runtimeName.GetPublicKeyToken(), loc);
      this.RegisterAsLatest(this.peReader.OpenAssembly(BinaryDocument.GetBinaryDocumentForFile(tempVccRuntimeAssemblyIdentity.Location, this), out this.vccRuntimeAssemblyIdentity));
    }

    internal IUnit GetIncrementalUnit(string newText)
    {
      string[] lines = newText.Split('$');
      if (lines.Length != 4) return Dummy.Unit;
      string prefix = lines[0];
      string textToReplace = lines[1];
      string replacement = lines[2];
      IVccSourceDocument updatedDocument = this.previousDocument.GetUpdatedDocument(prefix.Length, textToReplace.Length, replacement);
      return updatedDocument.VccCompilationPart.Compilation.Result;
    }

    internal VccSourceDocument/*?*/ previousDocument;

    protected override AssemblyIdentity GetCoreAssemblySymbolicIdentity()
    {
      return this.mscorlibIdentity;
    }
    readonly AssemblyIdentity mscorlibIdentity;

    public AssemblyIdentity VccRuntimeAssemblyIdentity
    {
      get { return this.vccRuntimeAssemblyIdentity; }
    }
    readonly AssemblyIdentity vccRuntimeAssemblyIdentity;

    public override IUnit LoadUnitFrom(string location)
    {
      IUnit result = this.peReader.OpenModule(BinaryDocument.GetBinaryDocumentForFile(location, this));
      this.RegisterAsLatest(result);
      return result;
    }

    readonly Microsoft.Cci.PeReader peReader;

    public override void ReportErrors(Microsoft.Cci.ErrorEventArgs errorEventArguments)
    {
      this.SynchronousReportErrors(errorEventArguments);
    }
  }
}
