using System.Windows.Forms;

namespace Microsoft.Research.Vcc.VSPackage
{
  public partial class CustomVerifyForm : Form
  {
    public CustomVerifyForm(string text)
    {
      InitializeComponent();
      this.textBox1.Text = text;
    }

    public string Arguments
    {
      get { return this.textBox1.Text; }
    }
  }
}
