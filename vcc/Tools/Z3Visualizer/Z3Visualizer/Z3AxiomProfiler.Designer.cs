namespace Z3AxiomProfiler
{
    partial class Z3AxiomProfiler
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
          this.menuStrip1 = new System.Windows.Forms.MenuStrip();
          this.fileToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
          this.loadZ3TraceLogToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
          this.profileZ3TraceToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
          this.loadZ3FromBoogieToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
          this.searchToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
          this.toolStripSeparator2 = new System.Windows.Forms.ToolStripSeparator();
          this.colorVisualizationToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
          this.toolStripSeparator1 = new System.Windows.Forms.ToolStripSeparator();
          this.exitToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
          this.cSVToolStripMenuItem1 = new System.Windows.Forms.ToolStripMenuItem();
          this.allConflictsToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
          this.randomConflictsToolStripMenuItem1 = new System.Windows.Forms.ToolStripMenuItem();
          this.helpToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
          this.aboutToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
          this.helpToolStripMenuItem1 = new System.Windows.Forms.ToolStripMenuItem();
          this.splitContainer1 = new System.Windows.Forms.SplitContainer();
          this.z3AxiomTree = new System.Windows.Forms.TreeView();
          this.toolTipBox = new System.Windows.Forms.TextBox();
          this.searchTreeVisualizationToolStripMenuItem = new System.Windows.Forms.ToolStripMenuItem();
          this.menuStrip1.SuspendLayout();
          this.splitContainer1.Panel1.SuspendLayout();
          this.splitContainer1.Panel2.SuspendLayout();
          this.splitContainer1.SuspendLayout();
          this.SuspendLayout();
          // 
          // menuStrip1
          // 
          this.menuStrip1.Items.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.fileToolStripMenuItem,
            this.cSVToolStripMenuItem1,
            this.helpToolStripMenuItem});
          this.menuStrip1.Location = new System.Drawing.Point(0, 0);
          this.menuStrip1.Name = "menuStrip1";
          this.menuStrip1.Size = new System.Drawing.Size(741, 24);
          this.menuStrip1.TabIndex = 2;
          this.menuStrip1.Text = "menuStrip1";
          // 
          // fileToolStripMenuItem
          // 
          this.fileToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.loadZ3TraceLogToolStripMenuItem,
            this.profileZ3TraceToolStripMenuItem,
            this.loadZ3FromBoogieToolStripMenuItem,
            this.searchToolStripMenuItem,
            this.toolStripSeparator2,
            this.colorVisualizationToolStripMenuItem,
            this.searchTreeVisualizationToolStripMenuItem,
            this.toolStripSeparator1,
            this.exitToolStripMenuItem});
          this.fileToolStripMenuItem.Name = "fileToolStripMenuItem";
          this.fileToolStripMenuItem.Size = new System.Drawing.Size(37, 20);
          this.fileToolStripMenuItem.Text = "&File";
          // 
          // loadZ3TraceLogToolStripMenuItem
          // 
          this.loadZ3TraceLogToolStripMenuItem.Name = "loadZ3TraceLogToolStripMenuItem";
          this.loadZ3TraceLogToolStripMenuItem.Size = new System.Drawing.Size(268, 22);
          this.loadZ3TraceLogToolStripMenuItem.Text = "&Load Z3 Output File";
          this.loadZ3TraceLogToolStripMenuItem.Click += new System.EventHandler(this.LoadZ3Logfile_Click);
          // 
          // profileZ3TraceToolStripMenuItem
          // 
          this.profileZ3TraceToolStripMenuItem.Name = "profileZ3TraceToolStripMenuItem";
          this.profileZ3TraceToolStripMenuItem.Size = new System.Drawing.Size(268, 22);
          this.profileZ3TraceToolStripMenuItem.Text = "Profile Z3 Trace";
          this.profileZ3TraceToolStripMenuItem.Click += new System.EventHandler(this.LoadZ3_Click);
          // 
          // loadZ3FromBoogieToolStripMenuItem
          // 
          this.loadZ3FromBoogieToolStripMenuItem.Name = "loadZ3FromBoogieToolStripMenuItem";
          this.loadZ3FromBoogieToolStripMenuItem.Size = new System.Drawing.Size(268, 22);
          this.loadZ3FromBoogieToolStripMenuItem.Text = "Profile Z3 Trace for &Boogie Execution";
          this.loadZ3FromBoogieToolStripMenuItem.Click += new System.EventHandler(this.LoadBoogie_Click);
          // 
          // searchToolStripMenuItem
          // 
          this.searchToolStripMenuItem.Name = "searchToolStripMenuItem";
          this.searchToolStripMenuItem.Size = new System.Drawing.Size(268, 22);
          this.searchToolStripMenuItem.Text = "&Search";
          this.searchToolStripMenuItem.Click += new System.EventHandler(this.searchToolStripMenuItem_Click);
          // 
          // toolStripSeparator2
          // 
          this.toolStripSeparator2.Name = "toolStripSeparator2";
          this.toolStripSeparator2.Size = new System.Drawing.Size(265, 6);
          // 
          // colorVisualizationToolStripMenuItem
          // 
          this.colorVisualizationToolStripMenuItem.Name = "colorVisualizationToolStripMenuItem";
          this.colorVisualizationToolStripMenuItem.Size = new System.Drawing.Size(268, 22);
          this.colorVisualizationToolStripMenuItem.Text = "&Color Visualization";
          this.colorVisualizationToolStripMenuItem.Click += new System.EventHandler(this.colorVisualizationToolStripMenuItem_Click);
          // 
          // toolStripSeparator1
          // 
          this.toolStripSeparator1.Name = "toolStripSeparator1";
          this.toolStripSeparator1.Size = new System.Drawing.Size(265, 6);
          // 
          // exitToolStripMenuItem
          // 
          this.exitToolStripMenuItem.Name = "exitToolStripMenuItem";
          this.exitToolStripMenuItem.Size = new System.Drawing.Size(268, 22);
          this.exitToolStripMenuItem.Text = "&Exit";
          this.exitToolStripMenuItem.Click += new System.EventHandler(this.Exit_Click);
          // 
          // cSVToolStripMenuItem1
          // 
          this.cSVToolStripMenuItem1.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.allConflictsToolStripMenuItem,
            this.randomConflictsToolStripMenuItem1});
          this.cSVToolStripMenuItem1.Name = "cSVToolStripMenuItem1";
          this.cSVToolStripMenuItem1.Size = new System.Drawing.Size(40, 20);
          this.cSVToolStripMenuItem1.Text = "CS&V";
          // 
          // allConflictsToolStripMenuItem
          // 
          this.allConflictsToolStripMenuItem.Name = "allConflictsToolStripMenuItem";
          this.allConflictsToolStripMenuItem.Size = new System.Drawing.Size(191, 22);
          this.allConflictsToolStripMenuItem.Text = "&All conflicts";
          this.allConflictsToolStripMenuItem.Click += new System.EventHandler(this.allConflictsToolStripMenuItem_Click);
          // 
          // randomConflictsToolStripMenuItem1
          // 
          this.randomConflictsToolStripMenuItem1.Name = "randomConflictsToolStripMenuItem1";
          this.randomConflictsToolStripMenuItem1.Size = new System.Drawing.Size(191, 22);
          this.randomConflictsToolStripMenuItem1.Text = "1000 random conflicts";
          this.randomConflictsToolStripMenuItem1.Click += new System.EventHandler(this.randomConflictsToolStripMenuItem1_Click);
          // 
          // helpToolStripMenuItem
          // 
          this.helpToolStripMenuItem.DropDownItems.AddRange(new System.Windows.Forms.ToolStripItem[] {
            this.aboutToolStripMenuItem,
            this.helpToolStripMenuItem1});
          this.helpToolStripMenuItem.Name = "helpToolStripMenuItem";
          this.helpToolStripMenuItem.Size = new System.Drawing.Size(44, 20);
          this.helpToolStripMenuItem.Text = "&Help";
          // 
          // aboutToolStripMenuItem
          // 
          this.aboutToolStripMenuItem.Name = "aboutToolStripMenuItem";
          this.aboutToolStripMenuItem.Size = new System.Drawing.Size(107, 22);
          this.aboutToolStripMenuItem.Text = "&About";
          this.aboutToolStripMenuItem.Click += new System.EventHandler(this.aboutToolStripMenuItem_Click);
          // 
          // helpToolStripMenuItem1
          // 
          this.helpToolStripMenuItem1.Name = "helpToolStripMenuItem1";
          this.helpToolStripMenuItem1.Size = new System.Drawing.Size(107, 22);
          this.helpToolStripMenuItem1.Text = "&Help";
          this.helpToolStripMenuItem1.Click += new System.EventHandler(this.helpToolStripMenuItem1_Click);
          // 
          // splitContainer1
          // 
          this.splitContainer1.Dock = System.Windows.Forms.DockStyle.Fill;
          this.splitContainer1.Location = new System.Drawing.Point(0, 24);
          this.splitContainer1.Name = "splitContainer1";
          this.splitContainer1.Orientation = System.Windows.Forms.Orientation.Horizontal;
          // 
          // splitContainer1.Panel1
          // 
          this.splitContainer1.Panel1.Controls.Add(this.z3AxiomTree);
          // 
          // splitContainer1.Panel2
          // 
          this.splitContainer1.Panel2.Controls.Add(this.toolTipBox);
          this.splitContainer1.Size = new System.Drawing.Size(741, 672);
          this.splitContainer1.SplitterDistance = 599;
          this.splitContainer1.TabIndex = 3;
          // 
          // z3AxiomTree
          // 
          this.z3AxiomTree.Dock = System.Windows.Forms.DockStyle.Fill;
          this.z3AxiomTree.Font = new System.Drawing.Font("Consolas", 9F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(238)));
          this.z3AxiomTree.HideSelection = false;
          this.z3AxiomTree.Location = new System.Drawing.Point(0, 0);
          this.z3AxiomTree.Name = "z3AxiomTree";
          this.z3AxiomTree.Size = new System.Drawing.Size(741, 599);
          this.z3AxiomTree.TabIndex = 1;
          this.z3AxiomTree.BeforeExpand += new System.Windows.Forms.TreeViewCancelEventHandler(this.HandleExpand);
          this.z3AxiomTree.AfterSelect += new System.Windows.Forms.TreeViewEventHandler(this.SetTooltip);
          this.z3AxiomTree.KeyPress += new System.Windows.Forms.KeyPressEventHandler(this.z3AxiomTree_KeyPress);
          // 
          // toolTipBox
          // 
          this.toolTipBox.AcceptsReturn = true;
          this.toolTipBox.AcceptsTab = true;
          this.toolTipBox.Anchor = ((System.Windows.Forms.AnchorStyles)((((System.Windows.Forms.AnchorStyles.Top | System.Windows.Forms.AnchorStyles.Bottom)
                      | System.Windows.Forms.AnchorStyles.Left)
                      | System.Windows.Forms.AnchorStyles.Right)));
          this.toolTipBox.CausesValidation = false;
          this.toolTipBox.Font = new System.Drawing.Font("Consolas", 9F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(238)));
          this.toolTipBox.Location = new System.Drawing.Point(0, 0);
          this.toolTipBox.Multiline = true;
          this.toolTipBox.Name = "toolTipBox";
          this.toolTipBox.Size = new System.Drawing.Size(741, 68);
          this.toolTipBox.TabIndex = 0;
          // 
          // searchTreeVisualizationToolStripMenuItem
          // 
          this.searchTreeVisualizationToolStripMenuItem.Name = "searchTreeVisualizationToolStripMenuItem";
          this.searchTreeVisualizationToolStripMenuItem.Size = new System.Drawing.Size(268, 22);
          this.searchTreeVisualizationToolStripMenuItem.Text = "Search &Tree Visualization";
          this.searchTreeVisualizationToolStripMenuItem.Click += new System.EventHandler(this.searchTreeVisualizationToolStripMenuItem_Click);
          // 
          // Z3AxiomProfiler
          // 
          this.AutoScaleDimensions = new System.Drawing.SizeF(6F, 13F);
          this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
          this.ClientSize = new System.Drawing.Size(741, 696);
          this.Controls.Add(this.splitContainer1);
          this.Controls.Add(this.menuStrip1);
          this.Name = "Z3AxiomProfiler";
          this.Text = "Z3 Axiom Profiler";
          this.Load += new System.EventHandler(this.Z3AxiomProfiler_OnLoadEvent);
          this.KeyPress += new System.Windows.Forms.KeyPressEventHandler(this.Z3AxiomProfiler_KeyPress);
          this.menuStrip1.ResumeLayout(false);
          this.menuStrip1.PerformLayout();
          this.splitContainer1.Panel1.ResumeLayout(false);
          this.splitContainer1.Panel2.ResumeLayout(false);
          this.splitContainer1.Panel2.PerformLayout();
          this.splitContainer1.ResumeLayout(false);
          this.ResumeLayout(false);
          this.PerformLayout();

        }

        #endregion

        private System.Windows.Forms.MenuStrip menuStrip1;
        private System.Windows.Forms.ToolStripMenuItem fileToolStripMenuItem;
        private System.Windows.Forms.ToolStripMenuItem loadZ3FromBoogieToolStripMenuItem;
        private System.Windows.Forms.ToolStripSeparator toolStripSeparator1;
        private System.Windows.Forms.ToolStripMenuItem exitToolStripMenuItem;
        private System.Windows.Forms.ToolStripMenuItem helpToolStripMenuItem;
        private System.Windows.Forms.ToolStripMenuItem aboutToolStripMenuItem;
        private System.Windows.Forms.ToolStripMenuItem colorVisualizationToolStripMenuItem;
        private System.Windows.Forms.ToolStripSeparator toolStripSeparator2;
        private System.Windows.Forms.ToolStripMenuItem helpToolStripMenuItem1;
        private System.Windows.Forms.ToolStripMenuItem cSVToolStripMenuItem1;
        private System.Windows.Forms.ToolStripMenuItem allConflictsToolStripMenuItem;
        private System.Windows.Forms.ToolStripMenuItem randomConflictsToolStripMenuItem1;
        private System.Windows.Forms.ToolStripMenuItem loadZ3TraceLogToolStripMenuItem;
        private System.Windows.Forms.ToolStripMenuItem profileZ3TraceToolStripMenuItem;
        private System.Windows.Forms.SplitContainer splitContainer1;
        private System.Windows.Forms.TreeView z3AxiomTree;
        private System.Windows.Forms.TextBox toolTipBox;
        private System.Windows.Forms.ToolStripMenuItem searchToolStripMenuItem;
        private System.Windows.Forms.ToolStripMenuItem searchTreeVisualizationToolStripMenuItem;
    }
}

