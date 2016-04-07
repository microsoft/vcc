//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Drawing;
using System.Drawing.Imaging;
using System.Windows.Forms;
using Z3AxiomProfiler.QuantifierModel;

namespace Z3AxiomProfiler
{
    public partial class ColorVisalizationForm : Form
    {

        //Define the colors
        private readonly List<Color> colors = new List<Color> { 
                Color.Black, Color.Purple, Color.Blue, 
                Color.Green, Color.Red, Color.Orange, Color.Cyan, Color.DarkGray, Color.Yellow,
                Color.YellowGreen, Color.Silver, Color.Salmon, Color.LemonChiffon, Color.Fuchsia,
                Color.ForestGreen, Color.Beige
                };

        private readonly Control ctrl;

        private int ImageWidth = 0;
        private int ImageHeight = 0;

        readonly bool launchedFromAddin;

        public ColorVisalizationForm()
          : this(false, null)
        {
        }

        public ColorVisalizationForm(bool launchedFromAddin, Control ctrl)
        {
            InitializeComponent();
            this.ctrl = ctrl;
            this.launchedFromAddin = launchedFromAddin;
        }

        private void DisplayResults()
        {
            ImageWidth = this.panel1.Width;
            ImageHeight = quantifiers.Count / ImageWidth + 1;
            if (ImageHeight < this.panel1.Height)
            {
              // This image fits into the display area. Adjust the size to fit the widget.
              ImageHeight = this.panel1.Height;
            }
            else
            {
              // This image is too large for the display area.
              ImageWidth = this.panel1.Width - 20;
              ImageHeight = quantifiers.Count / ImageWidth + 1;
            }

            Bitmap bmp = new Bitmap(ImageWidth, ImageHeight);

            for (int i = 0; i < ImageWidth; i++)
            {
                for (int j = 0; j < ImageHeight; j++)
                {
                    int index = j * ImageWidth + i;
                    if (quantifiers.Count > index)
                    {
                        int colorIndex = quantifierColorSorting.IndexOf(quantifiers[index]);
                        if ((colorIndex >= 0) && (colorIndex < colors.Count))
                        {
                            Color myColor = colors[colorIndex];
                            bmp.SetPixel(i, j, myColor);
                        } else
                        {
                          bmp.SetPixel(i, j, Color.LightGray);
                        }
                    }
                    else
                    {
                        bmp.SetPixel(i, j, Color.WhiteSmoke);
                    }
                }
            }
            
            pictureBox1.Height = ImageHeight;
            pictureBox1.Width  = ImageWidth;
            pictureBox1.Image  = bmp;
        }

        private void closeToolStripMenuItem_Click(object sender, EventArgs e)
        {
            this.Close();
        }

        private void saveBitmapAsToolStripMenuItem_Click(object sender, EventArgs e)
        {

          if (launchedFromAddin && ctrl.InvokeRequired) {
            ctrl.Invoke(new EventHandler(saveBitmapAsToolStripMenuItem_Click), sender, e);
          } else {
            SaveFileDialog fileDialog = new SaveFileDialog();
            fileDialog.Filter = "JPEG file |*.jpg";
            if (fileDialog.ShowDialog() == DialogResult.OK) {
              this.pictureBox1.Image.Save(fileDialog.FileName, ImageFormat.Jpeg);
            }
          }
        }

        private void legendToolStripMenuItem_Click(object sender, EventArgs e)
        {
            /*if ((result == null) || (result.legend == null) || (result.legend.Count == 0))
                return;
            String legend = "";
            int index = 0;
            foreach (FormulaEntry f in result.legend)
            {
                if (colors.Count > index)
                {
                    legend += String.Format("({0}) ", colors[index].Name);
                }
                legend += String.Format("**{0}** [{1}] {2}\n", f.frequency, f.identifier, f.formula);
                index++;
            }
            MessageBox.Show(legend);
             * */
        }


        List<Quantifier> quantifiers;
        List<Quantifier> quantifierColorSorting;

        public void setQuantifiers(List<Quantifier> quantifiers, List<Quantifier> quantifierColorSorting)
        {
            this.quantifiers = quantifiers;
            this.quantifierColorSorting = quantifierColorSorting;
            DisplayResults();
        }

        private void pictureBox1_Click(object sender, EventArgs e)
        {
            Point click = ((MouseEventArgs)e).Location;
            if ((click.Y >= 0) && (click.Y < ImageHeight) &&
                (click.X >= 0) && (click.X < ImageWidth))
            {
              int index = click.Y * ImageWidth + click.X;
              
              if (index < quantifiers.Count)
              {
                Quantifier q = quantifiers[index];
                int colorIndex = quantifierColorSorting.IndexOf(q);
                if ((colorIndex >= 0) && (colorIndex < colors.Count))
                {
                  this.colorBox.BackColor = colors[colorIndex];
                  this.boogieQuantifierText.Text = q.Body;
                  this.quantifierLinkedText.Text = q.ToString();
                }
                else
                {
                  this.colorBox.BackColor = Color.White;
                  this.boogieQuantifierText.Text = "";
                  this.quantifierLinkedText.Text = "";
                }
              }
            }
        }

        private void ColorVisalizationForm_SizeChanged(object sender, EventArgs e)
        {
          DisplayResults();
        }

        private void ColorVisalizationForm_ResizeBegin(object sender, EventArgs e)
        {
          panel1.AutoScroll = false;
        }

        private void ColorVisalizationForm_ResizeEnd(object sender, EventArgs e)
        {
          panel1.AutoScroll = true;
        }

    }
}
