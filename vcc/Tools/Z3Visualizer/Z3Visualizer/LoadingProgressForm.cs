//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.ComponentModel;
using System.Windows.Forms;

namespace Z3AxiomProfiler
{
  public partial class LoadingProgressForm : Form
  {
    private Loader loader;
    
    public LoadingProgressForm(Loader loader)
    {
      this.loader = loader;
      InitializeComponent();
      runningZ3.Text = String.Format("Running Z3");
    }

    private void processLoaderOutput(string line)
    {
      //processor.ParseSingleLine(line);
    }

    private void LoadingProgressForm_Load(object sender, EventArgs e)
    {
      backgroundWorker1.RunWorkerAsync();
    }

    private void backgroundWorker1_DoWork(object sender, DoWorkEventArgs e)
    {
      loader.statusUpdate += this.loaderProgressChanged;
      //loader.lineOutput += this.processLoaderOutput;
      loader.Load();
      
    }

    private void backgroundWorker1_RunWorkerCompleted(object sender, RunWorkerCompletedEventArgs e)
    {
      Close();
    }

    private void button1_Click(object sender, EventArgs e)
    {
      backgroundWorker1.CancelAsync();
      loader.Cancel();
    }

    private void loaderProgressChanged(int perc, int a)
    {
      backgroundWorker1.ReportProgress(perc, a);

    }
    private void backgroundWorker1_ProgressChanged(object sender, ProgressChangedEventArgs e)
    {
      int a = (int)e.UserState;
      if (e.ProgressPercentage != 0) {
        progressBar1.Style = ProgressBarStyle.Blocks;
        int perc = e.ProgressPercentage;
        if (perc <= progressBar1.Maximum)
          progressBar1.Value = perc;
      }
      switch (a)
      {
        case 0:
          runningBoogie.Checked = false;
          runningZ3.Checked = false;
          runningParser.Checked = false;
          break;
        case 1:
          runningBoogie.Checked = true;
          runningZ3.Checked = false;
          runningParser.Checked = false;
          break;
        case 2:
          runningBoogie.Checked = true;
          runningZ3.Checked = true;
          runningParser.Checked = false;
          break;
        case 3:
          runningBoogie.Checked = true;
          runningZ3.Checked = true;
          runningParser.Checked = true;
          break;
      }
    }
  }
}
