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
  public partial class LoadZ3Form : Form
  {

    readonly bool launchedFromAddin;
    readonly Control ctrl;

    delegate string LoadFileDelegate(string filename);

    public LoadZ3Form(bool launchedFromAddin, Control ctrl)
    {
      this.launchedFromAddin = launchedFromAddin;
      this.ctrl = ctrl;
      InitializeComponent();
      buttonLoad.Focus();
    }

    private void LoadZ3Form_Load(object sender, EventArgs e)
    {

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
      z3FilePath.Text = (config.z3InputFile == null) ? "" : config.z3InputFile;
      z3Timeout.Text = config.timeout.ToString();
      if ( allZ3Options.Contains("PROOF_MODE=2") && allZ3Options.Contains("DISPLAY_PROOF=true") ) {
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
      z3Options.Text = allZ3Options;
    }

    public ParameterConfiguration GetParameterConfiguration()
    {
      ParameterConfiguration config = ParameterConfiguration.loadParameterConfigurationFromSettings();
      string allZ3Options = z3Options.Text;
      config.z3InputFile = z3FilePath.Text;
      if (rb_proofLogging.Checked)
      {
        allZ3Options += " PROOF_MODE=2 DISPLAY_PROOF=true";
      }
      config.z3Options = allZ3Options;
      Int32.TryParse(z3Timeout.Text, out config.timeout);
      return config;
    }

    private string loadZ3File(string filename)
    {
      if (launchedFromAddin && ctrl.InvokeRequired)
      {
        return ctrl.Invoke(new LoadFileDelegate(loadZ3File), filename) as string;
      }
      else
      {
        FileDialog openFileDialog = new OpenFileDialog();
        openFileDialog.Title = "Open Z3 file";
        if (File.Exists(filename))
        {
          openFileDialog.FileName = filename;
        }
        openFileDialog.Filter = "Z3 files (*.z3;*.smt;*.sx;*.smp;*.simplif;*.dimacs) |*.z3;*.smt;*.sx;*.smp;*.simplif;*.dimacs| " +
                                "Z3 native files (*.z3) |*.z3| " +
                                "SMT-LIB files (*.smt) |*.smt| " +
                                "Simplify files (*.sx;*.smp;*.simplify) |*.sx;*.smp;*.simplify| " +
                                "DIMACS files (*.dimacs) |*.dimacs| " +
                                "All files (*.*) |*.*";
        if ((openFileDialog.ShowDialog() == DialogResult.OK) && File.Exists(openFileDialog.FileName))
        {
          return openFileDialog.FileName;
        }
        else
        {
          return filename;
        }
      }
    }

    private void buttonOpenZ3_Click(object sender, EventArgs e)
    {
      z3FilePath.Text = loadZ3File(z3FilePath.Text);
    }

    private void LoadZ3Form_Shown(object sender, EventArgs e)
    {
      buttonLoad.Focus();
    }
  }
}
