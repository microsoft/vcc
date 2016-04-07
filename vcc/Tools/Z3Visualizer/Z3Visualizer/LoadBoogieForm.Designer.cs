namespace Z3AxiomProfiler
{
  partial class LoadBoogieForm
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
      this.preludeFileTextBox = new System.Windows.Forms.TextBox();
      this.preludeFileLabel = new System.Windows.Forms.Label();
      this.codeFileLabel = new System.Windows.Forms.Label();
      this.codeFileTextBox = new System.Windows.Forms.TextBox();
      this.boogieOptionLabel = new System.Windows.Forms.Label();
      this.boogieOptionTextBox = new System.Windows.Forms.TextBox();
      this.z3OptionsLabel = new System.Windows.Forms.Label();
      this.z3OptionsTextBox = new System.Windows.Forms.TextBox();
      this.buttonSelectPrelude = new System.Windows.Forms.Button();
      this.buttonSelectCode = new System.Windows.Forms.Button();
      this.buttonLoad = new System.Windows.Forms.Button();
      this.buttonCancel = new System.Windows.Forms.Button();
      this.functionLabel = new System.Windows.Forms.Label();
      this.functionTextBox = new System.Windows.Forms.TextBox();
      this.timeoutTextBox = new System.Windows.Forms.TextBox();
      this.timeoutLabel = new System.Windows.Forms.Label();
      this.buttonDefault = new System.Windows.Forms.Button();
      this.groupBox1 = new System.Windows.Forms.GroupBox();
      this.groupBox2 = new System.Windows.Forms.GroupBox();
      this.rb_proofLogging = new System.Windows.Forms.CheckBox();
      this.groupBox1.SuspendLayout();
      this.groupBox2.SuspendLayout();
      this.SuspendLayout();
      // 
      // preludeFileTextBox
      // 
      this.preludeFileTextBox.Location = new System.Drawing.Point(112, 23);
      this.preludeFileTextBox.Name = "preludeFileTextBox";
      this.preludeFileTextBox.Size = new System.Drawing.Size(373, 20);
      this.preludeFileTextBox.TabIndex = 0;
      // 
      // preludeFileLabel
      // 
      this.preludeFileLabel.AutoSize = true;
      this.preludeFileLabel.Location = new System.Drawing.Point(6, 26);
      this.preludeFileLabel.Name = "preludeFileLabel";
      this.preludeFileLabel.Size = new System.Drawing.Size(79, 13);
      this.preludeFileLabel.TabIndex = 1;
      this.preludeFileLabel.Text = "Prelude bpl-file:";
      // 
      // codeFileLabel
      // 
      this.codeFileLabel.AutoSize = true;
      this.codeFileLabel.Location = new System.Drawing.Point(6, 52);
      this.codeFileLabel.Name = "codeFileLabel";
      this.codeFileLabel.Size = new System.Drawing.Size(68, 13);
      this.codeFileLabel.TabIndex = 3;
      this.codeFileLabel.Text = "Code bpl-file:";
      // 
      // codeFileTextBox
      // 
      this.codeFileTextBox.Location = new System.Drawing.Point(112, 49);
      this.codeFileTextBox.Name = "codeFileTextBox";
      this.codeFileTextBox.Size = new System.Drawing.Size(373, 20);
      this.codeFileTextBox.TabIndex = 2;
      // 
      // boogieOptionLabel
      // 
      this.boogieOptionLabel.AutoSize = true;
      this.boogieOptionLabel.Location = new System.Drawing.Point(6, 81);
      this.boogieOptionLabel.Name = "boogieOptionLabel";
      this.boogieOptionLabel.Size = new System.Drawing.Size(80, 13);
      this.boogieOptionLabel.TabIndex = 5;
      this.boogieOptionLabel.Text = "Boogie options:";
      // 
      // boogieOptionTextBox
      // 
      this.boogieOptionTextBox.Location = new System.Drawing.Point(112, 78);
      this.boogieOptionTextBox.Name = "boogieOptionTextBox";
      this.boogieOptionTextBox.Size = new System.Drawing.Size(373, 20);
      this.boogieOptionTextBox.TabIndex = 4;
      // 
      // z3OptionsLabel
      // 
      this.z3OptionsLabel.AutoSize = true;
      this.z3OptionsLabel.Location = new System.Drawing.Point(6, 22);
      this.z3OptionsLabel.Name = "z3OptionsLabel";
      this.z3OptionsLabel.Size = new System.Drawing.Size(46, 13);
      this.z3OptionsLabel.TabIndex = 7;
      this.z3OptionsLabel.Text = "Options:";
      // 
      // z3OptionsTextBox
      // 
      this.z3OptionsTextBox.Location = new System.Drawing.Point(111, 19);
      this.z3OptionsTextBox.Name = "z3OptionsTextBox";
      this.z3OptionsTextBox.Size = new System.Drawing.Size(373, 20);
      this.z3OptionsTextBox.TabIndex = 6;
      // 
      // buttonSelectPrelude
      // 
      this.buttonSelectPrelude.Location = new System.Drawing.Point(491, 23);
      this.buttonSelectPrelude.Name = "buttonSelectPrelude";
      this.buttonSelectPrelude.Size = new System.Drawing.Size(40, 20);
      this.buttonSelectPrelude.TabIndex = 8;
      this.buttonSelectPrelude.Text = "...";
      this.buttonSelectPrelude.TextAlign = System.Drawing.ContentAlignment.TopCenter;
      this.buttonSelectPrelude.UseVisualStyleBackColor = true;
      this.buttonSelectPrelude.Click += new System.EventHandler(this.buttonSelectPrelude_Click);
      // 
      // buttonSelectCode
      // 
      this.buttonSelectCode.Location = new System.Drawing.Point(491, 49);
      this.buttonSelectCode.Name = "buttonSelectCode";
      this.buttonSelectCode.Size = new System.Drawing.Size(40, 20);
      this.buttonSelectCode.TabIndex = 9;
      this.buttonSelectCode.Text = "...";
      this.buttonSelectCode.TextAlign = System.Drawing.ContentAlignment.TopCenter;
      this.buttonSelectCode.UseVisualStyleBackColor = true;
      this.buttonSelectCode.Click += new System.EventHandler(this.buttonSelectCode_Click);
      // 
      // buttonLoad
      // 
      this.buttonLoad.Location = new System.Drawing.Point(317, 258);
      this.buttonLoad.Name = "buttonLoad";
      this.buttonLoad.Size = new System.Drawing.Size(75, 23);
      this.buttonLoad.TabIndex = 10;
      this.buttonLoad.Text = "Load";
      this.buttonLoad.UseVisualStyleBackColor = true;
      this.buttonLoad.Click += new System.EventHandler(this.buttonLoad_Click);
      // 
      // buttonCancel
      // 
      this.buttonCancel.Location = new System.Drawing.Point(479, 258);
      this.buttonCancel.Name = "buttonCancel";
      this.buttonCancel.Size = new System.Drawing.Size(75, 23);
      this.buttonCancel.TabIndex = 11;
      this.buttonCancel.Text = "Cancel";
      this.buttonCancel.UseVisualStyleBackColor = true;
      this.buttonCancel.Click += new System.EventHandler(this.buttonCancel_Click);
      // 
      // functionLabel
      // 
      this.functionLabel.AutoSize = true;
      this.functionLabel.Location = new System.Drawing.Point(6, 107);
      this.functionLabel.Name = "functionLabel";
      this.functionLabel.Size = new System.Drawing.Size(51, 13);
      this.functionLabel.TabIndex = 12;
      this.functionLabel.Text = "Function:";
      // 
      // functionTextBox
      // 
      this.functionTextBox.Location = new System.Drawing.Point(112, 104);
      this.functionTextBox.Name = "functionTextBox";
      this.functionTextBox.Size = new System.Drawing.Size(373, 20);
      this.functionTextBox.TabIndex = 13;
      // 
      // timeoutTextBox
      // 
      this.timeoutTextBox.Location = new System.Drawing.Point(111, 45);
      this.timeoutTextBox.Name = "timeoutTextBox";
      this.timeoutTextBox.Size = new System.Drawing.Size(54, 20);
      this.timeoutTextBox.TabIndex = 15;
      this.timeoutTextBox.TextAlign = System.Windows.Forms.HorizontalAlignment.Right;
      // 
      // timeoutLabel
      // 
      this.timeoutLabel.AutoSize = true;
      this.timeoutLabel.Location = new System.Drawing.Point(5, 48);
      this.timeoutLabel.Name = "timeoutLabel";
      this.timeoutLabel.Size = new System.Drawing.Size(97, 13);
      this.timeoutLabel.TabIndex = 14;
      this.timeoutLabel.Text = "Timeout (seconds):";
      // 
      // buttonDefault
      // 
      this.buttonDefault.Location = new System.Drawing.Point(398, 258);
      this.buttonDefault.Name = "buttonDefault";
      this.buttonDefault.Size = new System.Drawing.Size(75, 23);
      this.buttonDefault.TabIndex = 16;
      this.buttonDefault.Text = "Defaults";
      this.buttonDefault.UseVisualStyleBackColor = true;
      this.buttonDefault.Click += new System.EventHandler(this.buttonDefault_Click);
      // 
      // groupBox1
      // 
      this.groupBox1.Controls.Add(this.preludeFileLabel);
      this.groupBox1.Controls.Add(this.preludeFileTextBox);
      this.groupBox1.Controls.Add(this.buttonSelectPrelude);
      this.groupBox1.Controls.Add(this.codeFileLabel);
      this.groupBox1.Controls.Add(this.codeFileTextBox);
      this.groupBox1.Controls.Add(this.buttonSelectCode);
      this.groupBox1.Controls.Add(this.boogieOptionLabel);
      this.groupBox1.Controls.Add(this.functionLabel);
      this.groupBox1.Controls.Add(this.functionTextBox);
      this.groupBox1.Controls.Add(this.boogieOptionTextBox);
      this.groupBox1.Location = new System.Drawing.Point(12, 12);
      this.groupBox1.Name = "groupBox1";
      this.groupBox1.Size = new System.Drawing.Size(542, 137);
      this.groupBox1.TabIndex = 20;
      this.groupBox1.TabStop = false;
      this.groupBox1.Text = "Boogie Options";
      // 
      // groupBox2
      // 
      this.groupBox2.Controls.Add(this.rb_proofLogging);
      this.groupBox2.Controls.Add(this.z3OptionsLabel);
      this.groupBox2.Controls.Add(this.z3OptionsTextBox);
      this.groupBox2.Controls.Add(this.timeoutLabel);
      this.groupBox2.Controls.Add(this.timeoutTextBox);
      this.groupBox2.Location = new System.Drawing.Point(13, 156);
      this.groupBox2.Name = "groupBox2";
      this.groupBox2.Size = new System.Drawing.Size(541, 96);
      this.groupBox2.TabIndex = 21;
      this.groupBox2.TabStop = false;
      this.groupBox2.Text = "Z3 Options";
      // 
      // rb_proofLogging
      // 
      this.rb_proofLogging.AutoSize = true;
      this.rb_proofLogging.Location = new System.Drawing.Point(111, 71);
      this.rb_proofLogging.Name = "rb_proofLogging";
      this.rb_proofLogging.Size = new System.Drawing.Size(158, 17);
      this.rb_proofLogging.TabIndex = 21;
      this.rb_proofLogging.Text = "Enable Proof-Logging Mode";
      this.rb_proofLogging.UseVisualStyleBackColor = true;
      // 
      // LoadBoogieForm
      // 
      this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
      this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
      this.ClientSize = new System.Drawing.Size(566, 289);
      this.Controls.Add(this.groupBox2);
      this.Controls.Add(this.groupBox1);
      this.Controls.Add(this.buttonDefault);
      this.Controls.Add(this.buttonCancel);
      this.Controls.Add(this.buttonLoad);
      this.Name = "LoadBoogieForm";
      this.Text = "Profile Boogie Output for Z3";
      this.Load += new System.EventHandler(this.LoadParameterForm_Load);
      this.Shown += new System.EventHandler(this.LoadParameterForm_Shown);
      this.groupBox1.ResumeLayout(false);
      this.groupBox1.PerformLayout();
      this.groupBox2.ResumeLayout(false);
      this.groupBox2.PerformLayout();
      this.ResumeLayout(false);

    }

    #endregion

    private System.Windows.Forms.Label preludeFileLabel;
    private System.Windows.Forms.Label codeFileLabel;
    private System.Windows.Forms.Label boogieOptionLabel;
    private System.Windows.Forms.Label z3OptionsLabel;
    public System.Windows.Forms.Button buttonSelectPrelude;
    public System.Windows.Forms.Button buttonSelectCode;
    private System.Windows.Forms.Button buttonLoad;
    private System.Windows.Forms.Button buttonCancel;
    public System.Windows.Forms.TextBox boogieOptionTextBox;
    public System.Windows.Forms.TextBox preludeFileTextBox;
    public System.Windows.Forms.TextBox codeFileTextBox;
    public System.Windows.Forms.TextBox z3OptionsTextBox;
    private System.Windows.Forms.Label functionLabel;
    public System.Windows.Forms.TextBox functionTextBox;
    public System.Windows.Forms.TextBox timeoutTextBox;
    private System.Windows.Forms.Label timeoutLabel;
    private System.Windows.Forms.Button buttonDefault;
    private System.Windows.Forms.GroupBox groupBox1;
    private System.Windows.Forms.GroupBox groupBox2;
    private System.Windows.Forms.CheckBox rb_proofLogging;
  }
}