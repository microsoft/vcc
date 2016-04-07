using System.ComponentModel;
using Microsoft.VisualStudio.Shell;

namespace Microsoft.Research.Vcc.VSPackage
{
    public class VccOptionPage : DialogPage, INotifyPropertyChanged
    {
        private const string CmdLineCategory = "Additional Commandline Arguments";

        [Category(CmdLineCategory)]
        [DisplayName("Custom Arguments")]
        [Description("These additional commandline arguments for VCC will be used every time VCC is executed.")]
        public string AdditionalCommandlineArguments { get; set; }

        [Category(CmdLineCategory)]
        [DisplayName("Use Commandline Arguments")]
        [Description("Choose true to use the arguments you entered above, otherwise these arguments will be ignored.")]
        public bool UseAdditionalCommandlineArguments { get; set; }

        [Category("Include File Verification")]
        [Editor(typeof(System.Windows.Forms.Design.FileNameEditor), typeof(System.Drawing.Design.UITypeEditor))]
        [DisplayName("Start File for Include Files")]
        [Description("Use the specified file as command line argument when verifying .h files")]
        public string MasterFile { get; set; }

        [DisplayName("Show Z3 Inspector")]
        [Description("Choose true to launch the Z3 Inspector to view the progress of verification.")]
        public bool ShowZ3Inspector{ get; set; }

        [DisplayName("VCC Executable Folder")]
        [Editor(typeof(System.Windows.Forms.Design.FolderNameEditor),typeof(System.Drawing.Design.UITypeEditor))]
        [Description("The folder in which your vcc.exe is located - this is usually" +
                      " not necessary. Leave this empty to use the path written to the registry while installing" +
                      " VCC.")]
        public string VccExecutableFolder { get; set; }

        private bool dimAnnotations;

        [DisplayName("Dim Code Annotations")]
        [Description("Dim code annotations to visualize difference between implementation and annotation")]
        public bool DimAnnotations {
          get { 
            return this.dimAnnotations; }
          set {
            if (this.dimAnnotations != value) {
              this.dimAnnotations = value;
              this.NotifyProperyChanged("DimAnnotations");
            }
          }
        }

        [DisplayName("Show Notifications")]
        [Description("Show notifications when a verfication run completes and Visual Studion is no longer the foreground window.")]
        public bool ShowNotifications { get; set; }

        [DisplayName("Save Files")]
        [Description("VCC can ask you to save unsaved changes when you start a verification, or save changed files automatically.")]
        public SaveMode SaveMode { get; set; }

        [Category("Vcc Version")]
        [DisplayName("Installed VCC Version")]
        [Description("The version of this extension and the VCC compiler.")]
        public string VccVersion { 
          get { return System.Diagnostics.FileVersionInfo.GetVersionInfo(typeof(VccOptionPage).Assembly.Location).FileVersion;; } 
        }

        protected void NotifyProperyChanged(string name)
        {
          PropertyChangedEventHandler temp = PropertyChanged;
          if (temp != null)
          {
            temp(this, new PropertyChangedEventArgs(name));
          }
        }

        public event PropertyChangedEventHandler PropertyChanged;
    }
}
