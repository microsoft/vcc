namespace Z3AxiomProfiler
{
  partial class LoadZ3LogForm
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
      this.label1 = new System.Windows.Forms.Label();
      this.logFilePath = new System.Windows.Forms.TextBox();
      this.buttonOpenZ3Log = new System.Windows.Forms.Button();
      this.buttonLoad = new System.Windows.Forms.Button();
      this.buttonCancel = new System.Windows.Forms.Button();
      this.SuspendLayout();
      // 
      // label1
      // 
      this.label1.AutoSize = true;
      this.label1.Location = new System.Drawing.Point(9, 9);
      this.label1.Name = "label1";
      this.label1.Size = new System.Drawing.Size(93, 13);
      this.label1.TabIndex = 0;
      this.label1.Text = "Path to Z3 log file:";
      // 
      // logFilePath
      // 
      this.logFilePath.Location = new System.Drawing.Point(12, 25);
      this.logFilePath.Name = "logFilePath";
      this.logFilePath.Size = new System.Drawing.Size(308, 20);
      this.logFilePath.TabIndex = 1;
      // 
      // buttonOpenZ3Log
      // 
      this.buttonOpenZ3Log.Location = new System.Drawing.Point(326, 25);
      this.buttonOpenZ3Log.Name = "buttonOpenZ3Log";
      this.buttonOpenZ3Log.Size = new System.Drawing.Size(28, 20);
      this.buttonOpenZ3Log.TabIndex = 2;
      this.buttonOpenZ3Log.Text = "...";
      this.buttonOpenZ3Log.UseVisualStyleBackColor = true;
      this.buttonOpenZ3Log.Click += new System.EventHandler(this.buttonOpenZ3Log_Click);
      // 
      // buttonLoad
      // 
      this.buttonLoad.Location = new System.Drawing.Point(197, 51);
      this.buttonLoad.Name = "buttonLoad";
      this.buttonLoad.Size = new System.Drawing.Size(75, 23);
      this.buttonLoad.TabIndex = 6;
      this.buttonLoad.Text = "Load";
      this.buttonLoad.UseVisualStyleBackColor = true;
      this.buttonLoad.Click += new System.EventHandler(this.buttonLoad_Click);
      // 
      // buttonCancel
      // 
      this.buttonCancel.Location = new System.Drawing.Point(279, 51);
      this.buttonCancel.Name = "buttonCancel";
      this.buttonCancel.Size = new System.Drawing.Size(75, 23);
      this.buttonCancel.TabIndex = 7;
      this.buttonCancel.Text = "Cancel";
      this.buttonCancel.UseVisualStyleBackColor = true;
      this.buttonCancel.Click += new System.EventHandler(this.buttonCancel_Click);
      // 
      // LoadZ3LogForm
      // 
      this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
      this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
      this.ClientSize = new System.Drawing.Size(361, 81);
      this.Controls.Add(this.buttonCancel);
      this.Controls.Add(this.buttonLoad);
      this.Controls.Add(this.buttonOpenZ3Log);
      this.Controls.Add(this.logFilePath);
      this.Controls.Add(this.label1);
      this.Name = "LoadZ3LogForm";
      this.Text = "Load Z3 Logfile";
      this.Load += new System.EventHandler(this.LoadZ3LogForm_Load);
      this.Shown += new System.EventHandler(this.LoadZ3LogForm_Shown);
      this.ResumeLayout(false);
      this.PerformLayout();

    }

    #endregion

    private System.Windows.Forms.Label label1;
    private System.Windows.Forms.TextBox logFilePath;
    private System.Windows.Forms.Button buttonOpenZ3Log;
    private System.Windows.Forms.Button buttonLoad;
    private System.Windows.Forms.Button buttonCancel;
  }
}