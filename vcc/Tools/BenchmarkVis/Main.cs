using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Windows.Forms;
using System.IO;

namespace BenchmarkVis
{
  public partial class Main : Form
  {
    internal List<DataSet> data = new List<DataSet>();
    internal DataSet LeftDS, RightDS;
    internal Dictionary<string, int> testcaseId = new Dictionary<string, int>();
    internal List<string> testcaseNames = new List<string>();

    int MinScale;
    int MaxScale;
    int IdUnderMouse = -1;

    public Main()
    {
      InitializeComponent();

      this.SetStyle(ControlStyles.DoubleBuffer |
                    ControlStyles.UserPaint |
                    ControlStyles.AllPaintingInWmPaint,
                    true);
      this.UpdateStyles();

    }

    private void DumpData(DataSet selDs)
    {
      using (var sw = new StreamWriter("data.csv", true)) {
        foreach (var ds in this.data) {
          if (selDs != null && selDs != ds) continue;
          sw.WriteLine("DATASET {0}", ds.LongName);
          for (int i = 0; i < testcaseNames.Count; ++i) {
            var dp = ds.GetDataPoint(i);
            if (dp != null) {
              sw.Write("{0};", testcaseNames[i]);
              var med = dp.Median;
              if (med == ds.TimeoutValue)
                med = -1;
              PrintIntCsv(sw, med);
              foreach (var v_ in dp.RawValues) {
                var v = v_;
                if (v == int.MaxValue)
                  v = -1;
                PrintIntCsv(sw, v);
              }
              sw.WriteLine();
            }
          }
        }
      }

      this.toolStripStatusLabel1.Text = string.Format("Dumped {0} to data.csv.", selDs == null ? "all" : selDs.Name);
    }

    private static void PrintIntCsv(StreamWriter sw, int v)
    {
      sw.Write("{0};", v);
    }

    private void SetCommonRadio(RadioButton r, DataSet s)
    {
      r.AutoSize = true;
      r.Anchor = ((System.Windows.Forms.AnchorStyles)((System.Windows.Forms.AnchorStyles.Top | System.Windows.Forms.AnchorStyles.Right)));
      r.CheckedChanged += s.CheckedChanged;
      r.KeyPress += Main_KeyPress;
    }

    private void AddDataSet(DataSet s)
    {
      data.Add(s);

      var y = data.Count() * 20;

      var tt = new ToolTip() { AutoPopDelay = 25000, InitialDelay = 500, ReshowDelay = 500, ShowAlways = true };

      s.Left = new RadioButton();
      SetCommonRadio(s.Left, s);
      this.groupBox1.Controls.Add(s.Left);
      s.Left.Text = s.Name;
      s.Left.Location = new System.Drawing.Point(6, y);
      s.Left.CheckAlign = ContentAlignment.MiddleLeft;
      tt.SetToolTip(s.Left, s.Name);

      s.Right = new RadioButton();
      SetCommonRadio(s.Right, s);
      this.groupBox2.Controls.Add(s.Right);
      s.Right.Text = "vs.";
      s.Right.Location = new System.Drawing.Point(4, y);
      s.Right.CheckAlign = ContentAlignment.MiddleRight;
      tt.SetToolTip(s.Right, s.Name);
    }

    private int GetTestcaseId(string name)
    {
      var l = name.LastIndexOf('/');
      if(l>0) {
        name = name.Substring(l + 1);
      }
      int ret;
      if (testcaseId.TryGetValue(name, out ret))
        return ret;
      ret = testcaseId.Count;
      testcaseId.Add(name, ret);
      testcaseNames.Add(name);
      return ret;
    }

    internal void ProcessArgs()
    {
      var a = System.Environment.GetCommandLineArgs();
      for (int i = 1; i < a.Length; ++i)
        using (var rd = File.OpenText(a[i]))
          ReadData(rd);
      if (data.Count >= 2) {
        data[0].Left.Checked = true;
        data[1].Right.Checked = true;
      }
    }

    private void ReadData(TextReader rd)
    {
      DataSet d = new DataSet();
      d.parent = this;
      var seps = new char[] { ' ', '\t', '\n', '\r' };
      string sx_dir = "";
      string id = "";
      string options = "";
      int testId = -1;
      bool replaced = false;
      bool seenUnsat = false;
      bool seenSat = false;
      int currentValue = int.MaxValue;

      for (; ; ) {
        var l = rd.ReadLine();
        if (l == null) break;
        var words = l.Split(seps).Where(s => s != "").ToArray();
        if (l.StartsWith("unsat") || l.Contains(": Valid")) seenUnsat = true;
        if (l.StartsWith("sat") || l.Contains(": Invalid")) seenSat = true;
        if (words.Length < 2) continue;
        switch (words[0]) {
          case "SX_DIR": sx_dir = words[1]; break;
          case "ID":
            id = words[1];
            foreach (var ds in this.data) {
              if (ds.Id == id) {
                d = ds;
                replaced = true;
                break;
              }
            }
            break;
          case "OPTIONS":
            options = l.Replace("OPTIONS ", "").Replace("\n", "").Replace("\r", "");
            break;
          case "FILE":
            if (testId != -1) {
              if (!seenUnsat || seenSat) currentValue = int.MaxValue;
              var dp = d.CreateDataPoint(testId);
              dp.AddValue(currentValue);
            }
            testId = GetTestcaseId(words[1]);
            currentValue = int.MaxValue;
            seenUnsat = false;
            seenSat = false;
            break;
          case "TIME":
            currentValue = (int)(double.Parse(words[1]) * 1000);
            break;
          case "time:": {
              double tmp;
              if (double.TryParse(words[1], out tmp)) {
                currentValue = (int)(tmp * 1000);
              } else {
                Console.WriteLine("wrong double: '{0}'", words[1]);
                System.Environment.Exit(1);
              }
              break;
            }
        }
      }

      if (!replaced) {
        d.Name = id.Replace("2010.","") + " " + sx_dir.Replace("sx-","") + " " + options.Replace("CASE_SPLIT","CS");
        d.LongName = id + " " + options + " " + sx_dir;
        d.Id = id;
        this.AddDataSet(d);
      }
    }

    private Point ScreenCoord(double x, double y)
    {
      if (x <= 0) x = 1;
      if (y <= 0) y = 1;
      double max = Math.Log10(MaxScale);
      return new Point((int)(Math.Log10(x)/max * panel1.Width),
                       (int)(panel1.Height - Math.Log10(y) / max * panel1.Height));
    }

    private void panel1_Paint(object sender, PaintEventArgs e)
    {
      var gfx = e.Graphics;
      var rect = gfx.ClipBounds;
      gfx.FillRectangle(Brushes.White, rect);

      if (LeftDS == null || RightDS == null) return;

      var len = Math.Min(LeftDS.Values.Count, RightDS.Values.Count);
      MinScale = int.MaxValue;
      MaxScale = int.MinValue;
      var sum1 = 0;
      var sum2 = 0;

      LeftDS.TimeoutValue = RightDS.TimeoutValue = 0;

      for (var i = 0; i < len; ++i) {
        var l = LeftDS.Values[i];
        var r = RightDS.Values[i];
        if (l != null && r != null) {
          MinScale = Math.Min(MinScale, Math.Min(l.Min, r.Min));
          MaxScale = Math.Max(MaxScale, Math.Max(l.Max, r.Max));
          sum1 += l.Avg;
          sum2 += r.Avg;
        }
      }

      if (MaxScale == int.MinValue) return;

      LeftDS.TimeoutValue = RightDS.TimeoutValue = MaxScale + MaxScale / 3;
      MaxScale += MaxScale ;

      Brush texts = new SolidBrush(Color.FromArgb(150, 150, 150));
      var font = groupBox1.Font;

      int scale = 10;
      bool to = false;
      while(true) {
        var p = ScreenCoord(scale, scale);
        gfx.DrawLine(Pens.LightGray, p.X, 0, p.X, panel1.Height);
        gfx.DrawLine(Pens.LightGray, 0, p.Y, panel1.Width, p.Y);
        var s = string.Format("{0:0.00}{1}", scale / 1000.0, to? " (timeout)": "");
        gfx.DrawString(s, font, texts, p.X, panel1.Height - 15);
        gfx.DrawString(s, font, texts, 3, p.Y + 2);

        scale *= 10;
        if (scale > LeftDS.TimeoutValue) {
          if (to) break;
          scale = LeftDS.TimeoutValue;
          to = true;
        }
      }

      gfx.DrawLine(Pens.LightGray, 0, panel1.Height, panel1.Width, 0);
      var half = ScreenCoord(1, 2);
      Pen pn = new Pen(Color.FromArgb(230, 230, 230));
      gfx.DrawLine(pn, half.X, half.Y, half.X + panel1.Width, half.Y - panel1.Height);
      half = ScreenCoord(2, 1);
      gfx.DrawLine(pn, half.X, half.Y, half.X + panel1.Width, half.Y - panel1.Height);

      gfx.DrawString(string.Format("{0} ({1:0.00})",
        LeftDS.LongName, sum1 / 1000.0), font, texts, 2, 2);

      {
        var str = string.Format("{0} ({1:0.00})",
          RightDS.LongName, sum2 / 1000.0);
        var sz = gfx.MeasureString(str, font);
        gfx.DrawString(str, font, texts, panel1.Width - sz.Width, panel1.Height - 30);
      }

      for (var i = 0; i < len; ++i) {
        var l = LeftDS.Values[i];
        var r = RightDS.Values[i];
        if (!IsVisible(i)) continue;
        var selected = i == IdUnderMouse;
        var ll = ScreenCoord(r.Min, l.Max);
        var rr = ScreenCoord(r.Max, l.Min);
        var r2 = new Rectangle(ll.X, ll.Y, rr.X - ll.X, rr.Y - ll.Y);
        if (selected) {
          foreach (var v in r.NormValues) {
            gfx.DrawLine(Pens.LightGray, ScreenCoord(v, l.Min), ScreenCoord(v, l.Max));
          }
          foreach (var v in l.NormValues) {
            gfx.DrawLine(Pens.LightGray, ScreenCoord(r.Min, v), ScreenCoord(r.Max, v));
          }
        }
        gfx.DrawRectangle(selected ? Pens.Crimson : Pens.LightPink, r2);
        var mid = ScreenCoord(r.Avg, l.Avg);
        r2 = new Rectangle(mid.X - 1, mid.Y - 1, 3, 3);
        gfx.FillRectangle(selected ? Brushes.Red : Brushes.Blue, r2);
      }

      foreach (var ds in data) {
        ds.Left.BackColor = Color.LightGray;
        ds.Right.BackColor = Color.LightGray;
      }

      if (sum1 < sum2) {
        //RightDS.Left.BackColor = Color.LightPink;
        LeftDS.Left.BackColor = Color.Lime;
      } else {
        //LeftDS.Left.BackColor = Color.LightPink;
        RightDS.Right.BackColor = Color.Lime;
      }

    }

    private void radioButton1_CheckedChanged(object sender, EventArgs e)
    {

    }

    internal void Flush()
    {
      panel1.Invalidate();
    }

    private void Main_Resize(object sender, EventArgs e)
    {
      Flush();
    }

    private bool IsVisible(int i)
    {
      var l = LeftDS.Values[i];
      var r = RightDS.Values[i];
      if (l != null && r != null) {
        return !viewOnly1sToolStripMenuItem.Checked ||
          l.Max > 1000 || r.Max > 1000;
      }
      return false;
    }

    private void pictureBox1_MouseMove(object sender, MouseEventArgs e)
    {
      if (LeftDS == null || RightDS == null) return;

      var len = Math.Min(LeftDS.Values.Count, RightDS.Values.Count);
      var minDist = int.MaxValue;
      int id = -1;
      for (var i = 0; i < len; ++i) {
        var l = LeftDS.Values[i];
        var r = RightDS.Values[i];
        if (!IsVisible(i)) continue;
        var p = ScreenCoord(r.Avg, l.Avg);
        var dist = Math.Abs(p.X - e.X) + Math.Abs(p.Y - e.Y);
        if (dist < minDist) {
          minDist = dist;
          id = i;
        }
      }

      if (minDist > 30)
        id = -1;
      if (IdUnderMouse != id) {
        IdUnderMouse = id;
        if (id >= 0) {
          toolStripStatusLabel1.Text = string.Format("{0} {1:0.00} {2:0.00}", testcaseNames[id], LeftDS.Values[id].Avg / 1000.0, RightDS.Values[id].Avg / 1000.0);
        } else {
          toolStripStatusLabel1.Text = "";
        }
        Flush();
      }
    }

    private void dumpDataTodatacsvToolStripMenuItem_Click_1(object sender, EventArgs e)
    {
      DumpData(null);
    }

    private void exitToolStripMenuItem_Click(object sender, EventArgs e)
    {
      this.Close();
    }

    private void DumpLeft()
    {
      if (LeftDS != null)
        DumpData(LeftDS);
    }

    private void Main_KeyPress(object sender, KeyPressEventArgs e)
    {
      if (e.KeyChar == 'd') {
        DumpLeft();
      }
    }

    private void dumpCurrentLeftTodatacsvToolStripMenuItem_Click(object sender, EventArgs e)
    {
      DumpLeft();
    }

    private void viewOnly1sToolStripMenuItem_Click(object sender, EventArgs e)
    {
      viewOnly1sToolStripMenuItem.Checked = !viewOnly1sToolStripMenuItem.Checked;
    }
  }

  class DataPoint
  {
    private List<int> values = new List<int>();
    public DataSet Parent;

    public IEnumerable<int> NormValues
    {
      get
      {
        foreach (var v in values) {
          if (v == int.MaxValue) yield return Parent.TimeoutValue;
          else yield return v;
        }
      }
    }

    public IEnumerable<int> RawValues
    {
      get
      {
        return values;
      }
    }

    public void AddValue(int i)
    {
      values.Add(i);
    }

    public int Min
    {
      get
      {
        var m = int.MaxValue;
        foreach (var v in values) {
          if (v < m) m = v;
        }
        return m;
      }
    }

    public int Max
    {
      get
      {
        var m = int.MinValue;
        foreach (var v in NormValues) {
          if (v > m) m = v;
        }
        return m;
      }
    }

    public int Avg
    {
        get { return Median; }
    }

    public int Average
    {
      get
      {
        if(values.Count == 0) return 0;
        var s = 0;
        foreach (var v in NormValues) {
          s += v;
        }
        return s / values.Count;
      }
    }

    public int Median
    {
        get
        {
            if (values.Count == 0) return 0;
            var arr = new List<int>();
            arr.AddRange(NormValues);
            arr.Sort();
            var n = arr.Count;
            if (n % 2 == 0)
                return (arr[n / 2] + arr[n / 2 - 1]) / 2;
            else
                return arr[n / 2];
        }
    }
  }

  class DataSet
  {
    public RadioButton Left, Right;
    public string Name;
    public string Id;
    public string LongName;
    public Main parent;
    public List<DataPoint> Values = new List<DataPoint>();
    public int TimeoutValue;

    public DataPoint GetDataPoint(int id)
    {
      if (Values.Count > id)
        return Values[id];
      return null;
    }

    public DataPoint CreateDataPoint(int id)
    {
      var res = GetDataPoint(id);
      if (res != null) return res;
      while (Values.Count <= id)
        Values.Add(null);
      Values[id] = new DataPoint();
      Values[id].Parent = this;
      return Values[id];
    }

    public void CheckedChanged(object sender, EventArgs e)
    {
      if (sender == Left) {
        if (Left.Checked) {
          parent.LeftDS = this;
          parent.Flush();
        }
      } else if (sender == Right) {
        if (Right.Checked) {
          parent.RightDS = this;
          parent.Flush();
        }
      }
    }
  }

}
