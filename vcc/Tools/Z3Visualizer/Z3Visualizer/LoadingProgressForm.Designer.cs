namespace Z3AxiomProfiler
{
  partial class LoadingProgressForm
  {
    /// <summary>
    /// Required designer variable.
    /// </summary>
    private System.ComponentModel.IContainer components = null;

    /// <summary>
    /// Clean up any resources being used.
    /// </summary>
    /// <param name="disposing">true if managed resources should be disposed; otherwise, false.</param>
    protected override void Dispose(bool disposing)
    {
      if (disposing && (components != null))
      {
        components.Dispose();
      }
      base.Dispose(disposing);
    }

    #region Windows Form Designer generated code

    /// <summary>
    /// Required method for Designer support - do not modify
    /// the contents of this method with the code editor.
    /// </summary>
    private void InitializeComponent()
    {
      this.progressBar1 = new System.Windows.Forms.ProgressBar();
      this.runningBoogie = new System.Windows.Forms.CheckBox();
      this.runningZ3 = new System.Windows.Forms.CheckBox();
      this.button1 = new System.Windows.Forms.Button();
      this.backgroundWorker1 = new System.ComponentModel.BackgroundWorker();
      this.runningParser = new System.Windows.Forms.CheckBox();
      this.SuspendLayout();
      // 
      // progressBar1
      // 
      this.progressBar1.Anchor = ((System.Windows.Forms.AnchorStyles)(((System.Windows.Forms.AnchorStyles.Top | System.Windows.Forms.AnchorStyles.Left)
                  | System.Windows.Forms.AnchorStyles.Right)));
      this.progressBar1.Location = new System.Drawing.Point(12, 12);
      this.progressBar1.MarqueeAnimationSpeed = 10;
      this.progressBar1.Maximum = 1000;
      this.progressBar1.Name = "progressBar1";
      this.progressBar1.Size = new System.Drawing.Size(275, 17);
      this.progressBar1.Style = System.Windows.Forms.ProgressBarStyle.Marquee;
      this.progressBar1.TabIndex = 0;
      // 
      // runningBoogie
      // 
      this.runningBoogie.AutoCheck = false;
      this.runningBoogie.AutoSize = true;
      this.runningBoogie.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
      this.runningBoogie.Location = new System.Drawing.Point(12, 35);
      this.runningBoogie.Name = "runningBoogie";
      this.runningBoogie.Size = new System.Drawing.Size(102, 17);
      this.runningBoogie.TabIndex = 4;
      this.runningBoogie.Text = "Running Boogie";
      this.runningBoogie.TextAlign = System.Drawing.ContentAlignment.MiddleCenter;
      this.runningBoogie.UseVisualStyleBackColor = true;
      // 
      // runningZ3
      // 
      this.runningZ3.AutoCheck = false;
      this.runningZ3.AutoSize = true;
      this.runningZ3.Font = new System.Drawing.Font("Microsoft Sans Serif", 8.25F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
      this.runningZ3.Location = new System.Drawing.Point(12, 58);
      this.runningZ3.Name = "runningZ3";
      this.runningZ3.Size = new System.Drawing.Size(82, 17);
      this.runningZ3.TabIndex = 5;
      this.runningZ3.Text = "Running Z3";
      this.runningZ3.UseVisualStyleBackColor = true;
      // 
      // button1
      // 
      this.button1.Anchor = ((System.Windows.Forms.AnchorStyles)((System.Windows.Forms.AnchorStyles.Bottom | System.Windows.Forms.AnchorStyles.Right)));
      this.button1.Location = new System.Drawing.Point(212, 76);
      this.button1.Name = "button1";
      this.button1.Size = new System.Drawing.Size(75, 23);
      this.button1.TabIndex = 7;
      this.button1.Text = "Cancel";
      this.button1.UseVisualStyleBackColor = true;
      this.button1.Click += new System.EventHandler(this.button1_Click);
      // 
      // backgroundWorker1
      // 
      this.backgroundWorker1.WorkerReportsProgress = true;
      this.backgroundWorker1.WorkerSupportsCancellation = true;
      this.backgroundWorker1.DoWork += new System.ComponentModel.DoWorkEventHandler(this.backgroundWorker1_DoWork);
      this.backgroundWorker1.RunWorkerCompleted += new System.ComponentModel.RunWorkerCompletedEventHandler(this.backgroundWorker1_RunWorkerCompleted);
      this.backgroundWorker1.ProgressChanged += new System.ComponentModel.ProgressChangedEventHandler(this.backgroundWorker1_ProgressChanged);
      // 
      // runningParser
      // 
      this.runningParser.AutoSize = true;
      this.runningParser.Location = new System.Drawing.Point(12, 82);
      this.runningParser.Name = "runningParser";
      this.runningParser.Size = new System.Drawing.Size(110, 17);
      this.runningParser.TabIndex = 8;
      this.runningParser.Text = "Parsing Z3 output";
      this.runningParser.UseVisualStyleBackColor = true;
      // 
      // LoadingProgressForm
      // 
      this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
      this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
      this.ClientSize = new System.Drawing.Size(299, 111);
      this.ControlBox = false;
      this.Controls.Add(this.runningParser);
      this.Controls.Add(this.button1);
      this.Controls.Add(this.runningZ3);
      this.Controls.Add(this.runningBoogie);
      this.Controls.Add(this.progressBar1);
      this.FormBorderStyle = System.Windows.Forms.FormBorderStyle.FixedDialog;
      this.Name = "LoadingProgressForm";
      this.Text = "Processing...";
      this.Load += new System.EventHandler(this.LoadingProgressForm_Load);
      this.ResumeLayout(false);
      this.PerformLayout();

    }

    #endregion

    private System.Windows.Forms.ProgressBar progressBar1;
    private System.Windows.Forms.CheckBox runningBoogie;
    private System.Windows.Forms.CheckBox runningZ3;
    private System.Windows.Forms.Button button1;
    private System.ComponentModel.BackgroundWorker backgroundWorker1;
    private System.Windows.Forms.CheckBox runningParser;
  }
}