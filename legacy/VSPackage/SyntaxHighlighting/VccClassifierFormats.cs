using System.ComponentModel.Composition;
using Microsoft.VisualStudio.Text.Classification;
using Microsoft.VisualStudio.Utilities;
using System.Windows.Media;
using Microsoft.VisualStudio.Text.Adornments;

namespace Microsoft.Research.Vcc.VSPackage
{
  internal static class VccClassifierFormats
  {
    private const double Opacity = 0.6;

    [Export(typeof(EditorFormatDefinition))]
    [ClassificationType(ClassificationTypeNames = VccClassificationTypeDefinitions.SpecType)]
    [Name(VccClassificationTypeDefinitions.SpecType)]
    internal sealed class VccSpecFormat : ClassificationFormatDefinition
    {
      public VccSpecFormat()
      {
      }
    }

    [Export(typeof(EditorFormatDefinition))]
    [ClassificationType(ClassificationTypeNames = VccClassificationTypeDefinitions.KeywordType)]
    [Name(VccClassificationTypeDefinitions.KeywordType)]
    internal sealed class VccKeywordFormat : ClassificationFormatDefinition
    {
      public VccKeywordFormat()
      {
      }
    }

    [Export(typeof(EditorFormatDefinition))]
    [ClassificationType(ClassificationTypeNames = VccClassificationTypeDefinitions.DimmedSpecType)]
    [Name(VccClassificationTypeDefinitions.DimmedSpecType)]
    internal sealed class VccDimmedSpecFormat : ClassificationFormatDefinition
    {
      public VccDimmedSpecFormat()
      {
        this.ForegroundOpacity = Opacity;
      }
    }

    [Export(typeof(EditorFormatDefinition))]
    [ClassificationType(ClassificationTypeNames = VccClassificationTypeDefinitions.DimmedKeywordType)]
    [Name(VccClassificationTypeDefinitions.DimmedKeywordType)]
    internal sealed class VccDimmedKeywordFormat : ClassificationFormatDefinition
    {
      public VccDimmedKeywordFormat()
      {
        this.ForegroundOpacity = Opacity;
      }
    }

    [Export(typeof(EditorFormatDefinition))]
    [Name(VccClassificationTypeDefinitions.VccErrorTagType)]
    [Order(After = Priority.High)]
    [UserVisible(true)]
    internal class VccErrorTagClassificationFormatDefinition : EditorFormatDefinition
    {
      public VccErrorTagClassificationFormatDefinition()
      {
        this.ForegroundColor = Colors.MidnightBlue;
        this.BackgroundCustomizable = false;
        this.DisplayName = "Verification Error";
      }
    }
  }
}
