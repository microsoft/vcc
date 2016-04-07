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
  public partial class LoadZ3LogForm : Form
  {

    readonly bool launchedFromAddin;
    readonly Control ctrl;

    delegate string LoadLogFileDelegate(string filename);

    public LoadZ3LogForm(bool launchedFromAddin, Control ctrl)
    {
      this.launchedFromAddin = launchedFromAddin;
      this.ctrl = ctrl;
      InitializeComponent();
      buttonLoad.Focus();
    }

    private void LoadZ3LogForm_Load(object sender, EventArgs e)
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
      logFilePath.Text = (config.z3LogFile == null) ? "" : config.z3LogFile;
    }

    public ParameterConfiguration GetParameterConfiguration()
    {
      ParameterConfiguration config = ParameterConfiguration.loadParameterConfigurationFromSettings();
      config.z3LogFile = logFilePath.Text;
      return config;
    }

    private string loadZ3LogFile(string filename)
    {
      if (launchedFromAddin && ctrl.InvokeRequired)
      {
        return ctrl.Invoke(new LoadLogFileDelegate(loadZ3LogFile), filename) as string;
      }
      else
      {
        FileDialog openFileDialog = new OpenFileDialog();
        openFileDialog.Title = "Open Z3 Output File";
        if (File.Exists(filename))
        {
          openFileDialog.FileName = filename;
        }
        openFileDialog.Filter = "Z3 logfiles (*.z3log;*.log) |*.z3log;*.log| Z3 result model (*.model;*.vccmodel) |*.model;*.vccmodel| All files (*.*) |*.*";
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

    private void buttonOpenZ3Log_Click(object sender, EventArgs e)
    {
      logFilePath.Text = loadZ3LogFile(logFilePath.Text);
    }

    private void LoadZ3LogForm_Shown(object sender, EventArgs e)
    {
      buttonLoad.Focus();
    }

  }
}
