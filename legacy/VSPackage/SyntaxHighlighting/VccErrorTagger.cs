using System;
using System.Collections.Generic;
using Microsoft.VisualStudio.Text.Tagging;
using System.ComponentModel.Composition;
using Microsoft.VisualStudio.Utilities;
using Microsoft.VisualStudio.Text;

namespace Microsoft.Research.Vcc.VSPackage
{
  internal class VccErrorTagger : ITagger<ErrorTag>
  {
    private readonly string fileName;
    private readonly ITextBuffer textBuffer;

    public VccErrorTagger(ITextBuffer textBuffer)
    {
      var textDocument = textBuffer.Properties[typeof (ITextDocument)] as ITextDocument;
      this.fileName = textDocument != null ? textDocument.FilePath : "";
      this.textBuffer = textBuffer;
      VSIntegration.ErrorLinesChanged += VSIntegration_ErrorLinesChanged;
      this.textBuffer.Changing += textBuffer_Changing;
    }

    void textBuffer_Changing(object sender, TextContentChangingEventArgs e)
    {
      List<Tuple<int, string>> errorLines;
      if (VSIntegration.ErrorLines.TryGetValue(this.fileName, out errorLines))
      {
        errorLines.Clear();
        OnTagsChanged();
      }
    }

    protected void OnTagsChanged()
    {
      EventHandler<SnapshotSpanEventArgs> temp = TagsChanged;
      if (temp != null) {
        var snapshot = this.textBuffer.CurrentSnapshot;
        temp(this, new SnapshotSpanEventArgs(new SnapshotSpan(snapshot, 0, snapshot.Length)));
      }
    }

    void VSIntegration_ErrorLinesChanged(object sender, ErrorLinesChangedEventArgs e)
    {
      if (String.Equals(e.FileName, this.fileName, StringComparison.OrdinalIgnoreCase))
      {
        OnTagsChanged();
      }
    }

    public IEnumerable<ITagSpan<ErrorTag>> GetTags(NormalizedSnapshotSpanCollection spans)
    {
      List<Tuple<int, string>> errorLines;
      if (!VSIntegration.ErrorLines.TryGetValue(this.fileName, out errorLines)) 
        return new ITagSpan<ErrorTag>[] {};

      var result = new List<ITagSpan<ErrorTag>>(errorLines.Count);
      var snapshot = this.textBuffer.CurrentSnapshot;

      foreach (var entry in errorLines)
      {
        var lineSpan = snapshot.GetLineFromLineNumber(entry.Item1-1).Extent;
        if (spans.IntersectsWith(new NormalizedSnapshotSpanCollection(lineSpan)))
        {
          result.Add(new TagSpan<ErrorTag>(TrimInitialWhitespace(lineSpan), new ErrorTag(VccClassificationTypeDefinitions.VccErrorTagType, entry.Item2)));
        }
      }

      return result;
    }

    private static SnapshotSpan TrimInitialWhitespace(SnapshotSpan span)
    {
      int i = span.Start.Position;
      while (char.IsWhiteSpace(span.Snapshot[i]))
      {
        i++;
      }

      if (i == span.Start.Position) return span;
      return new SnapshotSpan(span.Snapshot, i, span.Length - (i - span.Start.Position));
    }

    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;
  }

  [Export(typeof(ITaggerProvider))]
  [ContentType("C/C++")]
  [TagType(typeof(ErrorTag))]
  internal class VccTaggerProvider : ITaggerProvider
  {
    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag
    {
      return (ITagger<T>)new VccErrorTagger(buffer);
    }
  }
}
