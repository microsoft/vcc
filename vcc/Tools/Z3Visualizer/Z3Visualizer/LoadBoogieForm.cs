//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.IO;
using System.Windows.Forms;

namespace Z3AxiomProfiler
{
  public partial class LoadBoogieForm : Form
  {

    readonly bool launchedFromAddin;
    readonly Control ctrl;

    delegate string LoadBlpParameterDelegate(string value, string textbox);

    public LoadBoogieForm(bool launchedFromAddin, Control ctrl)
    {
      this.launchedFromAddin = launchedFromAddin;
      this.ctrl = ctrl;
      InitializeComponent();
      buttonLoad.Focus();
    }

    private void buttonLoad_Click(object sender, EventArgs e)
    {
      this.DialogResult = DialogResult.OK;
      Close();
    }

    private void buttonCancel_Click(object sender, EventArgs e)
    {
      this.DialogResult = DialogResult.Cancel;
      Close();
    }

    public void reloadParameterConfiguration()
    {
      ParameterConfiguration config = ParameterConfiguration.loadParameterConfigurationFromSettings();
      setParameterConfiguration(config);
    }

    public void setParameterConfiguration(ParameterConfiguration config)
    {
      string allZ3Options = config.z3Options;
      preludeFileTextBox.Text = (config.preludeBplFileInfo == null) ? "" : config.preludeBplFileInfo.FullName;
      codeFileTextBox.Text = (config.codeBplFileInfo == null) ? "" : config.codeBplFileInfo.FullName;
      boogieOptionTextBox.Text = config.boogieOptions;
      functionTextBox.Text = config.functionName;
      timeoutTextBox.Text = config.timeout.ToString();
      if (allZ3Options.Contains("PROOF_MODE=2") && allZ3Options.Contains("DISPLAY_PROOF=true"))
      {
        rb_proofLogging.Checked = true;
        allZ3Options = allZ3Options.Replace("PROOF_MODE=2", "");
        allZ3Options = allZ3Options.Replace("DISPLAY_PROOF=true", "");
        allZ3Options = allZ3Options.Replace("  ", " ");
        allZ3Options = allZ3Options.Trim();
      }
      else
      {
        rb_proofLogging.Checked = false;
      }
      z3OptionsTextBox.Text = allZ3Options;
    }

    public ParameterConfiguration GetParameterConfiguration()
    {
      ParameterConfiguration config = ParameterConfiguration.loadParameterConfigurationFromSettings();
      string allZ3Options = z3OptionsTextBox.Text;
      if (File.Exists(preludeFileTextBox.Text))
      {
        config.preludeBplFileInfo = new FileInfo(preludeFileTextBox.Text);
      }
      if (File.Exists(codeFileTextBox.Text))
      {
        config.codeBplFileInfo = new FileInfo(codeFileTextBox.Text);
      }
      config.boogieOptions = boogieOptionTextBox.Text;
      if (rb_proofLogging.Checked)
      {
        allZ3Options += " PROOF_MODE=2 DISPLAY_PROOF=true";
      }
      config.z3Options = allZ3Options;
      config.functionName = functionTextBox.Text;
      Int32.TryParse(timeoutTextBox.Text, out config.timeout);
      config.z3LogFile = Path.ChangeExtension(config.codeBplFileInfo.FullName, "z3log");
      return config;
    }

    private void buttonSelectPrelude_Click(object sender, EventArgs e)
    {
      preludeFileTextBox.Text = loadBplFile("Load prelude BPL-file", preludeFileTextBox.Text);
    }

    private void buttonSelectCode_Click(object sender, EventArgs e)
    {
      codeFileTextBox.Text = loadBplFile("Load code BPL-file", codeFileTextBox.Text);
    }

    private string loadBplFile(string title, string filename) {

      if (launchedFromAddin && ctrl.InvokeRequired) {
        return ctrl.Invoke(new LoadBlpParameterDelegate(loadBplFile), title, filename) as string;       
      } else {
        FileDialog openFileDialog = new OpenFileDialog();
        openFileDialog.Title = title;
        if (File.Exists(filename)) {
          openFileDialog.FileName = filename;
        }
        openFileDialog.Filter = "BPL files (*.bpl) |*.bpl| All files (*.*) |*.*";
        if ((openFileDialog.ShowDialog() == DialogResult.OK) && File.Exists(openFileDialog.FileName)) {
          return openFileDialog.FileName;
        } else {
          return filename;
        }
      }
    }


    private void buttonDefault_Click(object sender, EventArgs e)
    {
      // Reset setting to default settings.
      reloadParameterConfiguration();

      Properties.Settings.Default.BoogieOptions = "/bv:z /trace";
      Properties.Settings.Default.Z3Options = "/rs:0";
      Properties.Settings.Default.Timeout = 10;

      boogieOptionTextBox.Text = Properties.Settings.Default.BoogieOptions;
      z3OptionsTextBox.Text = Properties.Settings.Default.Z3Options;
      timeoutTextBox.Text = Properties.Settings.Default.Timeout.ToString();
    }

    private void LoadParameterForm_Load(object sender, EventArgs e)
    {     
    }

    private void LoadParameterForm_Shown(object sender, EventArgs e)
    {
      buttonLoad.Focus();
    }
  }
}
