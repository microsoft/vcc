using System;
using System.Diagnostics;
using System.IO;
using System.Management;
using System.Text.RegularExpressions;
using System.Threading;
using System.Windows.Forms;
using Microsoft.Win32;
using System.Runtime.InteropServices;

namespace Microsoft.Research.Vcc.VSPackage
{
  /// <summary>
  ///     This class is used to start VCC.exe with the correct parameters and to get the results from VCC.exe
  /// </summary>
  internal static class VCCLauncher
  {

    [DllImport("user32.dll")]
    static extern IntPtr GetForegroundWindow(); 

    #region

    private static string GetVSCOMNTOOLS()
    {
      string Version = VSIntegration.DTE.Version;      //returns something like 8.0
      string CleanVersionTag = Version.Replace(".", "");
      string VSDir = Environment.GetEnvironmentVariable(String.Format("VS{0}COMNTOOLS", CleanVersionTag));
      return VSDir;
    }

    internal static string GetCLPath(string ActivePlatform)
    {
      string vsToolDir = GetVSCOMNTOOLS();
      if (!String.IsNullOrEmpty(vsToolDir)) {
          string CL = (ActivePlatform == "x64") ? "VC\\bin\\x86_amd64\\cl.exe" : "VC\\bin\\cl.exe";
          return vsToolDir.ToUpperInvariant().Replace("COMMON7\\TOOLS\\", CL);
      } else return null;
    }

    #endregion

    #region commands

    private static readonly Lazy<NotifyIcon> notifyIcon = new Lazy<NotifyIcon>(InstallNotifyIcon);

    private static NotifyIcon InstallNotifyIcon()
    {
      NotifyIcon ni = new NotifyIcon();
      ni.Icon = VSPackage.Resources.VccIcon;
      ni.Visible = true;
      ni.Text = "Vcc " + System.Diagnostics.FileVersionInfo.GetVersionInfo(typeof(VCCLauncher).Assembly.Location).FileVersion;
      return ni;
    }

    private static string GetArgumentsFromOptions(VccOptionPage options, bool respectCustomFlag)
    {
      string result = !respectCustomFlag || options.UseAdditionalCommandlineArguments ?
          options.AdditionalCommandlineArguments :
          string.Empty;

      if (options.ShowZ3Inspector)
      {
        result += " /i";
      }

      result += " /bvd";

      return result;
    }

    internal static void VerifyThis(string filename, string currentFile, int line, VccOptionPage options)
    {
      string addArguments = GetArgumentsFromOptions(options, true);
      addArguments += String.Format(" /loc:\"{0}\":{1} ", currentFile, line);
      LaunchVCC(String.Format("{0} \"{1}\"", addArguments, filename));
    }

    internal static void CustomVerify(string filename, VccOptionPage options)
    {
      using (var customVerifyForm = new CustomVerifyForm(GetArgumentsFromOptions(options, false)))
      {
        if (customVerifyForm.ShowDialog() == DialogResult.OK)
        {
          LaunchVCC(String.Format("{0} \"{1}\"", customVerifyForm.Arguments, filename));
        }
      }
    }

    internal static void VerifyFile(string filename, VccOptionPage options)
    {
      string addArguments = GetArgumentsFromOptions(options, true);
      LaunchVCC(String.Format("{0} \"{1}\"", addArguments, filename));
    }

    internal static void VerifyFileWithoutIncludes(string filename, string currentFile, VccOptionPage options)
    {
      string addArguments = GetArgumentsFromOptions(options, true);
      addArguments += " /ii:" + currentFile;
      LaunchVCC(String.Format("{0} \"{1}\"", addArguments, filename));
    }

    #endregion

    #region process handling

    /// <summary>
    ///     This string contains the Path of the Vcc-Executable.
    ///     User Input in Tools/Options/Vcc > Registry Entry > "vcc.exe"
    /// </summary>
    private static string VccPath
    {
      get
      {
        if (String.IsNullOrWhiteSpace(VSPackagePackage.Instance.OptionPage.VccExecutableFolder))
        {
          using (var key = Registry.LocalMachine.OpenSubKey(@"Software\Microsoft Research\Vcc", false))
          {
            if (key != null)
            {
              return key.GetValue("vccExecutablePath", "vcc.exe") as string;
            }
            else
            {
              return "vcc.exe";
            }
          }
        }
        else
        {
          return Path.Combine(VSPackagePackage.Instance.OptionPage.VccExecutableFolder, "vcc.exe");
        }
      }
    }

    private static Process vccProcess;

    internal static void LaunchVCC(string arguments)
    {
      var vccPath = VccPath;

      arguments += " ";
      arguments += VSIntegration.CurrentCompilerSettings.ToVccOptions();
      var clPath = GetCLPath(VSIntegration.CurrentPlatform);
      if (clPath != null) arguments += String.Format(" /clpath:\"{0}\"", clPath);

      VSIntegration.ClearErrorsAndMarkers();
      VSIntegration.UpdateStatus("Verifying...", true);

      //// Prepare VCC-Process, execute it and read its Output            
      ProcessStartInfo psi = new ProcessStartInfo(string.Format("\"{0}\"", vccPath), arguments)
                               {
                                 UseShellExecute = false,
                                 RedirectStandardOutput = true,
                                 RedirectStandardError = true,
                                 CreateNoWindow = true
                               };
      vccProcess = new Process { StartInfo = psi };

      //// Clear Verification Outputpane
      VSIntegration.ClearAndShowPane();
      VSIntegration.WriteToPane("=== VCC started. ===");
      //// Write Commandline-Command to Verification Outputpane
      VSIntegration.WriteToPane(string.Format("Command Line: \"{0}\" {1}\n", vccPath, arguments));
      //// Get notified when VCC sends Output or Error Data
      vccProcess.OutputDataReceived += vccProcess_OutputDataReceived;
      vccProcess.ErrorDataReceived += vccProcess_OutputDataReceived;
      //// Get notified when VCC-Process finishes.
      vccProcess.EnableRaisingEvents = true;
      vccProcess.Exited += vccProcess_Exited;

      //// Finally start the process
      try
      {
        vccProcess.Start();
        vccProcess.BeginOutputReadLine();
        vccProcess.BeginErrorReadLine();
        //// When the process was started, remember the cmdlinearguments
        VSPackagePackage.LastAction = arguments;
      }
      catch (Exception)
      {
        vccProcess = null;
        VSIntegration.WriteToPane("Executing\n" + vccPath + "\nfailed.\n"
            + "You can specify the folder in which the VCC executable is located in Tools/Options/Vcc.");
        VSIntegration.WriteToPane("=== Verification failed. ===");
        VSIntegration.UpdateStatus("Verification failed.", false);
      }
    }

    /// <summary>
    ///     Cancels the running VCC Process, if it exists
    /// </summary>
    internal static void Cancel()
    {
      if (VCCRunning)
      {
        int vccProcess_Id = vccProcess.Id;
        try
        {
          vccProcess.Kill();
        }//try
        catch
        {
          VSIntegration.WriteToPane("Canceling VCC failed.");
        }//catch

        foreach (Process subProcess in Process.GetProcesses())
        {
          if (GetParentProcess(subProcess.Id) == vccProcess_Id)
          {
            try
            {
              subProcess.Kill();
            }
            catch
            {
              VSIntegration.WriteToPane("Canceling a subprocess of VCC failed.");
            }
          }//if
        }//foreach
      }//if
    }//method

    private static int GetParentProcess(int Id)
    {
      int parentPid = 0;
      using (ManagementObject mo = new ManagementObject("win32_process.handle='" + Id + "'"))
      {

        try
        {
          mo.Get();
          parentPid = Convert.ToInt32(mo["ParentProcessId"]);
        }
        catch { }
      }
      return parentPid;
    }

    #endregion

    #region process observation

    //// This is set to true, when Verification fails.
    private static readonly Regex VCCErrorRegEx =
        new Regex(@"(?<path>(.*?))\(((?<line>([0-9]+))|(?<line>([0-9]+)),(?<column>([0-9]+)))\)\s:\s(((error\s(.*?):)\s(?<errormessage>(.*)))|(?<errormessage>\(Location of symbol related to previous error.\)))");
    private static readonly Regex VCCWarningRegEx =
        new Regex(@"(?<path>(.*?))\(((?<line>([0-9]+))|(?<line>([0-9]+)),(?<column>([0-9]+)))\)\s:(\swarning\s(.*?):)\s(?<errormessage>(.*))");

    private static void vccProcess_Exited(object sender, EventArgs e)
    {
      if (vccProcess != null)
      {
        if (VSPackagePackage.Instance.OptionPage.ShowNotifications &&
            new IntPtr(VSIntegration.DTE.MainWindow.HWnd) != GetForegroundWindow())
        {
          if (vccProcess.ExitCode == 0)
          {
            notifyIcon.Value.ShowBalloonTip(4000, "Verification succeeded!", "Verification run completed successfully.", ToolTipIcon.Info);
          }
          else
          {
            notifyIcon.Value.ShowBalloonTip(4000, "Verification failed!", "Verification run completed with errors.", ToolTipIcon.Error);
          }
        }

        switch (vccProcess.ExitCode)
        {
          case -1:
            vccProcess.CancelOutputRead();
            vccProcess.CancelErrorRead();
            vccProcess = null;
            VSIntegration.WriteToPane("\n=== VCC was canceled. ===");
            VSIntegration.UpdateStatus("Verification canceled.", false);
            break;
          case 0:
            Thread.Sleep(1000);
            VSIntegration.WriteToPane("\n=== Verification succeeded. ===");
            VSIntegration.UpdateStatus("Verification succeeded.", false);
            break;
          case 2:
            Thread.Sleep(1000);
            VSIntegration.WriteToPane("Incorrect commandline arguments were used.");
            VSIntegration.WriteToPane("\n=== Verification failed. ===\n");
            VSIntegration.UpdateStatus("Verification failed.", false);
            break;
          case 1:
          case 3:
            Thread.Sleep(1000);
            VSIntegration.WriteToPane("\n=== Verification failed. ===");
            VSIntegration.UpdateStatus("Verification failed.", false);
            break;
          default:
            Thread.Sleep(1000);
            VSIntegration.WriteToPane("\n=== VCC finished with unknown exitcode. ===");
            VSIntegration.WriteToPane(vccProcess.ExitCode.ToString());
            break;
        }
      }
    }

    private static void vccProcess_OutputDataReceived(object sender, DataReceivedEventArgs e)
    {
      //// Write Output from VCC to Verification Outputpane
      if (e != null && e.Data != null)
      {
        VSIntegration.WriteToPane(e.Data);

        Match match;
        if ((match = VCCErrorRegEx.Match(e.Data)).Success)
        {
          //// Add error to error list
          VSIntegration.AddErrorToErrorList(
            match.Groups["path"].Value,
            match.Groups["errormessage"].Value,
            Int32.Parse(match.Groups["line"].Value),
            Microsoft.VisualStudio.Shell.TaskErrorCategory.Error);
        }
        else if ((match = VCCWarningRegEx.Match(e.Data)).Success)
        {
          //// Add warning to error list
          VSIntegration.AddErrorToErrorList(
            match.Groups["path"].Value,
            match.Groups["errormessage"].Value,
            Int32.Parse(match.Groups["line"].Value),
            Microsoft.VisualStudio.Shell.TaskErrorCategory.Warning);
        }
      }
    }

    internal static bool VCCRunning
    {
      get { return vccProcess != null && !vccProcess.HasExited; }
    }

    #endregion
  }
}
