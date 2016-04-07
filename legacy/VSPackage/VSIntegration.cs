using System;
using System.Diagnostics;
using System.Linq;
using EnvDTE;
using Microsoft.VisualStudio.Shell;
using Microsoft.VisualStudio.Shell.Interop;
using System.Windows.Forms;
using Microsoft.VisualStudio;
using Microsoft.VisualStudio.TextManager.Interop;
using System.Collections.Generic;

namespace Microsoft.Research.Vcc.VSPackage
{
  /// <summary>
  ///     This class handles interaction with Visual Studio
  /// </summary>
  internal static class VSIntegration
  {
    private static readonly Lazy<DTE> _dte = new Lazy<DTE>(() => (DTE)Package.GetGlobalService(typeof(DTE)));

    private static readonly Dictionary<string, List<Tuple<int, string>>> errorLines =
      new Dictionary<string, List<Tuple<int, string>>>(StringComparer.OrdinalIgnoreCase);

    private static readonly List<Tuple<string, int>> linesWithModels = new List<Tuple<string, int>>();

    /// <summary>
    ///     Returns an instance of the toplevel object for interaction with Visual Studio
    /// </summary>
    internal static DTE DTE
    {
      get { return _dte.Value; }
    }

    internal static void UpdateStatus(string text, bool animationOn)
    {
      DTE.StatusBar.Text = text;
      DTE.StatusBar.Animate(animationOn, vsStatusAnimation.vsStatusAnimationGeneral);
    }

    #region Outputpane

    private static readonly Lazy<IVsOutputWindowPane> _pane = new Lazy<IVsOutputWindowPane>(() =>
    {
      IVsOutputWindow outputwindow = (IVsOutputWindow)Package.GetGlobalService(typeof(SVsOutputWindow));
      Guid guidVerificationPane = new Guid("{1EE5916F-A3C7-403C-89D8-58C61285688F}");
      IVsOutputWindowPane result;

      outputwindow.CreatePane(ref guidVerificationPane, "Verification", 1, 1);
      outputwindow.GetPane(ref guidVerificationPane, out result);
      return result;
    }
    );

    /// <summary>
    ///     This object represents the Verification Outputpane.
    /// </summary>
    private static IVsOutputWindowPane VerificationOutputpane
    {
      get { return _pane.Value; }
    }

    internal static void ClearAndShowPane()
    {
      VerificationOutputpane.Clear();
      VerificationOutputpane.Activate();
    }

    internal static void WriteToPane(string message)
    {
      VerificationOutputpane.OutputString(message + "\n");
      VerificationOutputpane.FlushToTaskList();
    }

    #endregion

    #region document info

    internal static int CurrentLine
    {
      get
      {
        TextDocument textDocument = (TextDocument)DTE.ActiveDocument.Object(null);
        return textDocument.Selection.ActivePoint.Line;
      }
    }

    internal static int CurrentErrorModel
    {
      get { return Math.Max(linesWithModels.IndexOf(Tuple.Create(ActiveFileFullName.ToUpperInvariant(), CurrentLine)), 0); }
    }

    internal static bool CurrentLineHasError
    {
      get { return linesWithModels.Contains(Tuple.Create(ActiveFileFullName.ToUpperInvariant(), CurrentLine)); }
    }

    /// <summary>
    ///     Returns the name of the active document with path
    /// </summary>
    /// <returns>the name of the active document with path</returns>
    internal static string ActiveFileFullName
    {
      get { return DTE.ActiveDocument != null ? DTE.ActiveDocument.FullName : String.Empty; }
    }

    internal static string StartFileName
    {
      get
      {
        if (ActiveFileFullName.EndsWith(".h", StringComparison.OrdinalIgnoreCase) 
          && !String.IsNullOrWhiteSpace(VSPackagePackage.Instance.OptionPage.MasterFile)) {
          return VSPackagePackage.Instance.OptionPage.MasterFile;
        }

        return ActiveFileFullName;
      }
    }


    /// <summary>
    ///     Returns the name of the active document without path
    /// </summary>
    /// <returns>the name of the active document without path</returns>
    internal static string ActiveFileName
    {
      get { return DTE.ActiveDocument != null ? DTE.ActiveDocument.Name : String.Empty; }
    }

    /// <summary>
    ///     Returns wether the active document is in C or C++
    /// </summary>
    /// <returns>true, if active document is existent and in C or C++</returns>
    internal static bool IsCodeFile
    {
      get
      {
        if (DTE.ActiveDocument != null)
        {
          if (DTE.ActiveDocument.Language == "C/C++")
          {
            return true;
          }
        }

        return false;
      }
    }

    #endregion

    #region project settings

    internal static string CurrentPlatform
    {
      get
      {
        SelectedItem sitem = DTE.SelectedItems.Item(1);
        return sitem.ProjectItem.ConfigurationManager.ActiveConfiguration.PlatformName;
      }
    }

    internal static CompilerSettings CurrentCompilerSettings
    {
      get
      {
        SelectedItem sitem = DTE.SelectedItems.Item(1);
        return new CompilerSettings(sitem.ProjectItem);
      }
    }

    internal static Dictionary<string, List<Tuple<int, string>>> ErrorLines
    {
      get { return errorLines; }
    }

    public static event EventHandler<ErrorLinesChangedEventArgs> ErrorLinesChanged;


    #endregion

    #region document saving

    internal static bool DocumentsSavedCheck(VccOptionPage options) {
      if (DTE.Documents.Cast<Document>().All(document => document.Saved)) return true;

      if (options.SaveMode == SaveMode.Automatically) {
        DTE.Documents.SaveAll();
        return true;
      }
      
      if (MessageBox.Show(
        "There are unsaved changes. Press OK to save all documents and proceed with the verification.",
        "Unsaved Changes",
        MessageBoxButtons.OKCancel,
        MessageBoxIcon.Question,
        MessageBoxDefaultButton.Button1) == DialogResult.OK) {
          DTE.Documents.SaveAll();
          return true;
        }
      
      return false;
    }

    #endregion

    #region error list and markers

    private static readonly ErrorListProvider errorListProvider = new ErrorListProvider(VSPackagePackage.Instance);

    // this just helps with underlining just the code, no preceding whitespaces or comments
    // private static readonly Regex CodeLine = new Regex(@"(?<whitespaces>(\s*))(?<code>.*?)(?<comment>\s*(//|/\*).*)?$");

    internal static void ClearErrorsAndMarkers()
    {
      errorListProvider.Tasks.Clear();

      var fileNames = new List<string>(from entry in errorLines select entry.Key);
      errorLines.Clear();
      foreach (var fileName in fileNames)
      {
        OnErrorLinesChanged(fileName);
      }

      linesWithModels.Clear();
    }

    private static void OnErrorLinesChanged(string fileName)
    {
      EventHandler<ErrorLinesChangedEventArgs> temp = ErrorLinesChanged;
      if (temp != null)
      {
        temp(typeof(VSIntegration), new ErrorLinesChangedEventArgs(fileName));
      }
    }

    /// <summary>
    ///     Adds an entry to the error list
    /// </summary>
    /// <param name="document">Complete path of the document in which the error was found</param>
    /// <param name="text">Errormessage</param>
    /// <param name="line">the line, counting from one</param>
    /// <param name="category">is this an error or a warning?</param>
    internal static void AddErrorToErrorList(string document, string text, int line, TaskErrorCategory category)
    {
      var errorTask = new ErrorTask
                              {
                                ErrorCategory = category,
                                Document = document,
                                Text = text,
                                Line = line - 1,
                                Column = 0
                              };
      errorTask.Navigate += errorTask_Navigate;
      errorListProvider.Tasks.Add(errorTask);

      List<Tuple<int, string>> errorLinesInDocument;
      if (!ErrorLines.TryGetValue(document, out errorLinesInDocument))
      {
        errorLinesInDocument = new List<Tuple<int, string>>();
        ErrorLines.Add(document, errorLinesInDocument);
      }

      errorLinesInDocument.Add(Tuple.Create(line, text));
      if (!text.StartsWith("(related")) linesWithModels.Add(Tuple.Create(document.ToUpperInvariant(), line));
      OnErrorLinesChanged(document);
    }


    internal static void errorTask_Navigate(object sender, EventArgs e)
    {
      if (sender != null)
      {
        //// Open the document if necessary
        var errorTask = sender as ErrorTask;
        if (errorTask != null)
        {
          IVsUIShellOpenDocument uiShellOpenDocument =
            Package.GetGlobalService(typeof (IVsUIShellOpenDocument)) as IVsUIShellOpenDocument;
          if (uiShellOpenDocument == null)
          {
            return;
          }
          IVsWindowFrame windowFrame;
          VisualStudio.OLE.Interop.IServiceProvider serviceProvider;
          IVsUIHierarchy hierachy;
          uint itemid;
          Guid logicalView = VSConstants.LOGVIEWID_Code;
          uiShellOpenDocument.OpenDocumentViaProject(errorTask.Document,
                                                     ref logicalView,
                                                     out serviceProvider,
                                                     out hierachy,
                                                     out itemid,
                                                     out windowFrame);
          if (windowFrame == null)
          {
            return;
          }
          object docData;
          windowFrame.GetProperty((int) __VSFPROPID.VSFPROPID_DocData, out docData);

          //// Get the TextBuffer
          var buffer = docData as VsTextBuffer;
          if (buffer == null)
          {
            var bufferProvider = docData as IVsTextBufferProvider;
            if (bufferProvider != null)
            {
              IVsTextLines lines;
              bufferProvider.GetTextBuffer(out lines);
              buffer = lines as VsTextBuffer;
              if (buffer == null)
              {
                return;
              }
            }
          }

          //// Navigate to line
          var textManager = Package.GetGlobalService(typeof (VsTextManagerClass)) as IVsTextManager;
          if (textManager == null)
          {
            return;
          }
          textManager.NavigateToLineAndColumn(buffer,
                                              ref logicalView,
                                              errorTask.Line,
                                              errorTask.Column,
                                              errorTask.Line,
                                              errorTask.Column);
        }
      }
    }

    #endregion

    public static void InsertIntoCurrentDocument(string str)
    {
        var textDocument = DTE.ActiveDocument.Object(null) as TextDocument;
        if (textDocument != null)
        {
            textDocument.Selection.Insert(str);
        }
    }
  }
}