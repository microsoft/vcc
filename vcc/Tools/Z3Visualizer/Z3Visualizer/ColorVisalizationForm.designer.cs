namespace Z3AxiomProfiler
{
    partial class ColorVisalizationForm
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
          this.pictureBox1 = new System.Windows.Forms.PictureBox();
          this.panel1 = new System.Windows.Forms.Panel();
          this.panel2 = new System.Windows.Forms.Panel();
          this.quantifierLinkedText = new System.Windows.Forms.LinkLabel();
          this.boogieQuantifierText = new System.Windows.Forms.Label();
          this.colorBox = new System.Windows.Forms.PictureBox();
          this.fileToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
          this.toolStripSeparator3 = new System.Windows.Forms.ToolStripSeparator();
          this.saveBitmapAsToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
          this.toolStripSeparator2 = new System.Windows.Forms.ToolStripSeparator();
          this.closeToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
          this.helpToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
          this.legendToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
          this.toolStripSeparator1 = new System.Windows.Forms.ToolStripSeparator();
          this.menuStrip1 = new System.Windows.Forms.MenuStrip();
          ((System.ComponentModel.ISupportInitialize)(this.pictureBox1)).BeginInit();
          this.panel1.SuspendLayout();
          this.panel2.SuspendLayout();
          ((System.ComponentModel.ISupportInitialize)(this.colorBox)).BeginInit();
          this.menuStrip1.SuspendLayout();
          this.SuspendLayout();
          // 
          // pictureBox1
          // 
          this.pictureBox1.Location = new System.Drawing.Point(0, 0);
          this.pictureBox1.Name = "pictureBox1";
          this.pictureBox1.Size = new System.Drawing.Size(100, 50);
          this.pictureBox1.TabIndex = 0;
          this.pictureBox1.TabStop = false;
          this.pictureBox1.Click += new System.EventHandler(this.pictureBox1_Click);
          // 
          // panel1
          // 
          this.panel1.AutoScroll = true;
          this.panel1.Controls.Add(this.pictureBox1);
          this.panel1.Dock = System.Windows.Forms.DockStyle.Fill;
          this.panel1.Location = new System.Drawing.Point(0, 24);
          this.panel1.MinimumSize = new System.Drawing.Size(20, 20);
          this.panel1.Name = "panel1";
          this.panel1.Size = new System.Drawing.Size(882, 444);
          this.panel1.TabIndex = 3;
          // 
          // panel2
          // 
          this.panel2.BorderStyle = System.Windows.Forms.BorderStyle.FixedSingle;
          this.panel2.Controls.Add(this.quantifierLinkedText);
          this.panel2.Controls.Add(this.boogieQuantifierText);
          this.panel2.Controls.Add(this.colorBox);
          this.panel2.Dock = System.Windows.Forms.DockStyle.Bottom;
          this.panel2.Location = new System.Drawing.Point(0, 468);
          this.panel2.Name = "panel2";
          this.panel2.Size = new System.Drawing.Size(882, 80);
          this.panel2.TabIndex = 1;
          // 
          // quantifierLinkedText
          // 
          this.quantifierLinkedText.AutoSize = true;
          this.quantifierLinkedText.Location = new System.Drawing.Point(94, 58);
          this.quantifierLinkedText.Name = "quantifierLinkedText";
          this.quantifierLinkedText.Size = new System.Drawing.Size(0, 13);
          this.quantifierLinkedText.TabIndex = 2;
          // 
          // boogieQuantifierText
          // 
          this.boogieQuantifierText.AutoSize = true;
          this.boogieQuantifierText.Location = new System.Drawing.Point(94, 12);
          this.boogieQuantifierText.Name = "boogieQuantifierText";
          this.boogieQuantifierText.Size = new System.Drawing.Size(0, 13);
          this.boogieQuantifierText.TabIndex = 1;
          // 
          // colorBox
          // 
          this.colorBox.Location = new System.Drawing.Point(19, 12);
          this.colorBox.Name = "colorBox";
          this.colorBox.Size = new System.Drawing.Size(60, 60);
          this.colorBox.TabIndex = 0;
          this.colorBox.TabStop = false;
          // 
          // fileToolStripMenuItem
          // 
          this.fileToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.toolStripSeparator3,
            this.saveBitmapAsToolStripMenuItem,
            this.toolStripSeparator2,
            this.closeToolStripMenuItem});
          this.fileToolStripMenuItem.Name = "fileToolStripMenuItem";
          this.fileToolStripMenuItem.Size = new System.Drawing.Size(37, 20);
          this.fileToolStripMenuItem.Text = "File";
          // 
          // toolStripSeparator3
          // 
          this.toolStripSeparator3.Name = "toolStripSeparator3";
          this.toolStripSeparator3.Size = new System.Drawing.Size(161, 6);
          // 
          // saveBitmapAsToolStripMenuItem
          // 
          this.saveBitmapAsToolStripMenuItem.Name = "saveBitmapAsToolStripMenuItem";
          this.saveBitmapAsToolStripMenuItem.Size = new System.Drawing.Size(164, 22);
          this.saveBitmapAsToolStripMenuItem.Text = "Save Bitmap As...";
          this.saveBitmapAsToolStripMenuItem.Click += new System.EventHandler(this.saveBitmapAsToolStripMenuItem_Click);
          // 
          // toolStripSeparator2
          // 
          this.toolStripSeparator2.Name = "toolStripSeparator2";
          this.toolStripSeparator2.Size = new System.Drawing.Size(161, 6);
          // 
          // closeToolStripMenuItem
          // 
          this.closeToolStripMenuItem.Name = "closeToolStripMenuItem";
          this.closeToolStripMenuItem.Size = new System.Drawing.Size(164, 22);
          this.closeToolStripMenuItem.Text = "Close";
          this.closeToolStripMenuItem.Click += new System.EventHandler(this.closeToolStripMenuItem_Click);
          // 
          // helpToolStripMenuItem
          // 
          this.helpToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.legendToolStripMenuItem,
            this.toolStripSeparator1});
          this.helpToolStripMenuItem.Name = "helpToolStripMenuItem";
          this.helpToolStripMenuItem.Size = new System.Drawing.Size(44, 20);
          this.helpToolStripMenuItem.Text = "Help";
          // 
          // legendToolStripMenuItem
          // 
          this.legendToolStripMenuItem.Name = "legendToolStripMenuItem";
          this.legendToolStripMenuItem.Size = new System.Drawing.Size(113, 22);
          this.legendToolStripMenuItem.Text = "Legend";
          this.legendToolStripMenuItem.Click += new System.EventHandler(this.legendToolStripMenuItem_Click);
          // 
          // toolStripSeparator1
          // 
          this.toolStripSeparator1.Name = "toolStripSeparator1";
          this.toolStripSeparator1.Size = new System.Drawing.Size(110, 6);
          // 
          // menuStrip1
          // 
          this.menuStrip1.Items.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.fileToolStripMenuItem,
            this.helpToolStripMenuItem});
          this.menuStrip1.Location = new System.Drawing.Point(0, 0);
          this.menuStrip1.Name = "menuStrip1";
          this.menuStrip1.Size = new System.Drawing.Size(882, 24);
          this.menuStrip1.TabIndex = 2;
          this.menuStrip1.Text = "menuStrip1";
          // 
          // ColorVisalizationForm
          // 
          this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
          this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
          this.ClientSize = new System.Drawing.Size(882, 548);
          this.Controls.Add(this.panel1);
          this.Controls.Add(this.panel2);
          this.Controls.Add(this.menuStrip1);
          this.MinimumSize = new System.Drawing.Size(320, 240);
          this.Name = "ColorVisalizationForm";
          this.Text = "Z3 Visualizer";
          this.ResizeBegin += new System.EventHandler(this.ColorVisalizationForm_ResizeBegin);
          this.SizeChanged += new System.EventHandler(this.ColorVisalizationForm_SizeChanged);
          this.ResizeEnd += new System.EventHandler(this.ColorVisalizationForm_ResizeEnd);
          ((System.ComponentModel.ISupportInitialize)(this.pictureBox1)).EndInit();
          this.panel1.ResumeLayout(false);
          this.panel2.ResumeLayout(false);
          this.panel2.PerformLayout();
          ((System.ComponentModel.ISupportInitialize)(this.colorBox)).EndInit();
          this.menuStrip1.ResumeLayout(false);
          this.menuStrip1.PerformLayout();
          this.ResumeLayout(false);
          this.PerformLayout();

        }

        #endregion

        private System.Windows.Forms.PictureBox pictureBox1;
        private System.Windows.Forms.Panel panel1;
        private System.Windows.Forms.ToolStripMenuItem fileToolStripMenuItem;
        private System.Windows.Forms.ToolStripSeparator toolStripSeparator3;
        private System.Windows.Forms.ToolStripMenuItem saveBitmapAsToolStripMenuItem;
        private System.Windows.Forms.ToolStripSeparator toolStripSeparator2;
        private System.Windows.Forms.ToolStripMenuItem closeToolStripMenuItem;
        private System.Windows.Forms.ToolStripMenuItem helpToolStripMenuItem;
        private System.Windows.Forms.ToolStripMenuItem legendToolStripMenuItem;
        private System.Windows.Forms.ToolStripSeparator toolStripSeparator1;
        private System.Windows.Forms.MenuStrip menuStrip1;
        private System.Windows.Forms.Panel panel2;
        private System.Windows.Forms.PictureBox colorBox;
        public System.Windows.Forms.LinkLabel quantifierLinkedText;
        private System.Windows.Forms.Label boogieQuantifierText;

        //public System.EventHandler selectQuantifierHandler;

    }
}

