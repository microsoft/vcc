namespace Z3AxiomProfiler
{
  partial class LoadZ3Form
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
      this.buttonCancel = new System.Windows.Forms.Button();
      this.buttonLoad = new System.Windows.Forms.Button();
      this.buttonOpenZ3Log = new System.Windows.Forms.Button();
      this.z3FilePath = new System.Windows.Forms.TextBox();
      this.label1 = new System.Windows.Forms.Label();
      this.groupBox2 = new System.Windows.Forms.GroupBox();
      this.z3Timeout = new System.Windows.Forms.TextBox();
      this.label3 = new System.Windows.Forms.Label();
      this.rb_proofLogging = new System.Windows.Forms.CheckBox();
      this.z3Options = new System.Windows.Forms.TextBox();
      this.label2 = new System.Windows.Forms.Label();
      this.groupBox2.SuspendLayout();
      this.SuspendLayout();
      // 
      // buttonCancel
      // 
      this.buttonCancel.Location = new System.Drawing.Point(279, 184);
      this.buttonCancel.Name = "buttonCancel";
      this.buttonCancel.Size = new System.Drawing.Size(75, 23);
      this.buttonCancel.TabIndex = 14;
      this.buttonCancel.Text = "Cancel";
      this.buttonCancel.UseVisualStyleBackColor = true;
      this.buttonCancel.Click += new System.EventHandler(this.buttonCancel_Click);
      // 
      // buttonLoad
      // 
      this.buttonLoad.Location = new System.Drawing.Point(197, 184);
      this.buttonLoad.Name = "buttonLoad";
      this.buttonLoad.Size = new System.Drawing.Size(75, 23);
      this.buttonLoad.TabIndex = 13;
      this.buttonLoad.Text = "Load";
      this.buttonLoad.UseVisualStyleBackColor = true;
      this.buttonLoad.Click += new System.EventHandler(this.buttonLoad_Click);
      // 
      // buttonOpenZ3Log
      // 
      this.buttonOpenZ3Log.Location = new System.Drawing.Point(326, 26);
      this.buttonOpenZ3Log.Name = "buttonOpenZ3Log";
      this.buttonOpenZ3Log.Size = new System.Drawing.Size(28, 20);
      this.buttonOpenZ3Log.TabIndex = 12;
      this.buttonOpenZ3Log.Text = "...";
      this.buttonOpenZ3Log.UseVisualStyleBackColor = true;
      this.buttonOpenZ3Log.Click += new System.EventHandler(this.buttonOpenZ3_Click);
      // 
      // z3FilePath
      // 
      this.z3FilePath.Location = new System.Drawing.Point(12, 26);
      this.z3FilePath.Name = "z3FilePath";
      this.z3FilePath.Size = new System.Drawing.Size(308, 20);
      this.z3FilePath.TabIndex = 11;
      // 
      // label1
      // 
      this.label1.AutoSize = true;
      this.label1.Location = new System.Drawing.Point(9, 10);
      this.label1.Name = "label1";
      this.label1.Size = new System.Drawing.Size(102, 13);
      this.label1.TabIndex = 10;
      this.label1.Text = "Path to Z3 input file:";
      // 
      // groupBox2
      // 
      this.groupBox2.Controls.Add(this.z3Timeout);
      this.groupBox2.Controls.Add(this.label3);
      this.groupBox2.Controls.Add(this.rb_proofLogging);
      this.groupBox2.Controls.Add(this.z3Options);
      this.groupBox2.Controls.Add(this.label2);
      this.groupBox2.Location = new System.Drawing.Point(12, 52);
      this.groupBox2.Name = "groupBox2";
      this.groupBox2.Size = new System.Drawing.Size(341, 126);
      this.groupBox2.TabIndex = 15;
      this.groupBox2.TabStop = false;
      this.groupBox2.Text = "Z3 Options";
      // 
      // z3Timeout
      // 
      this.z3Timeout.Location = new System.Drawing.Point(6, 75);
      this.z3Timeout.Name = "z3Timeout";
      this.z3Timeout.Size = new System.Drawing.Size(329, 20);
      this.z3Timeout.TabIndex = 6;
      // 
      // label3
      // 
      this.label3.AutoSize = true;
      this.label3.Location = new System.Drawing.Point(6, 59);
      this.label3.Name = "label3";
      this.label3.Size = new System.Drawing.Size(97, 13);
      this.label3.TabIndex = 5;
      this.label3.Text = "Timeout (seconds):";
      // 
      // rb_proofLogging
      // 
      this.rb_proofLogging.AutoSize = true;
      this.rb_proofLogging.Location = new System.Drawing.Point(6, 101);
      this.rb_proofLogging.Name = "rb_proofLogging";
      this.rb_proofLogging.Size = new System.Drawing.Size(158, 17);
      this.rb_proofLogging.TabIndex = 2;
      this.rb_proofLogging.Text = "Enable Proof-Logging Mode";
      this.rb_proofLogging.UseVisualStyleBackColor = true;
      // 
      // z3Options
      // 
      this.z3Options.Location = new System.Drawing.Point(6, 32);
      this.z3Options.Name = "z3Options";
      this.z3Options.Size = new System.Drawing.Size(329, 20);
      this.z3Options.TabIndex = 1;
      // 
      // label2
      // 
      this.label2.AutoSize = true;
      this.label2.Location = new System.Drawing.Point(6, 16);
      this.label2.Name = "label2";
      this.label2.Size = new System.Drawing.Size(119, 13);
      this.label2.TabIndex = 0;
      this.label2.Text = "Command Line Options:";
      // 
      // LoadZ3Form
      // 
      this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
      this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
      this.ClientSize = new System.Drawing.Size(366, 216);
      this.Controls.Add(this.groupBox2);
      this.Controls.Add(this.buttonCancel);
      this.Controls.Add(this.buttonLoad);
      this.Controls.Add(this.buttonOpenZ3Log);
      this.Controls.Add(this.z3FilePath);
      this.Controls.Add(this.label1);
      this.Name = "LoadZ3Form";
      this.Text = "Profile Z3 Input";
      this.groupBox2.ResumeLayout(false);
      this.groupBox2.PerformLayout();
      this.ResumeLayout(false);
      this.PerformLayout();

    }

    #endregion

    private System.Windows.Forms.Button buttonCancel;
    private System.Windows.Forms.Button buttonLoad;
    private System.Windows.Forms.Button buttonOpenZ3Log;
    private System.Windows.Forms.TextBox z3FilePath;
    private System.Windows.Forms.Label label1;
    private System.Windows.Forms.GroupBox groupBox2;
    private System.Windows.Forms.CheckBox rb_proofLogging;
    private System.Windows.Forms.TextBox z3Options;
    private System.Windows.Forms.Label label2;
    private System.Windows.Forms.TextBox z3Timeout;
    private System.Windows.Forms.Label label3;
  }
}