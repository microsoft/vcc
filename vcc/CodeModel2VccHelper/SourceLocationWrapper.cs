//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

using Microsoft.Cci;
using System;

namespace Microsoft.Research.Vcc
{
  public interface IOriginalDocumentLocation : IPrimarySourceLocation
  {
    string OriginalDocumentLocation { get; }
  }

  internal sealed class SourceLocationWrapper : Token, IOriginalDocumentLocation
  {
     internal readonly IPrimarySourceLocation firstSourceLocation;
     internal readonly IPrimarySourceLocation lastSourceLocation;
     private readonly Lazy<string> source;
      
      
    internal SourceLocationWrapper(
        IPrimarySourceLocation firstSourceLocation, 
        IPrimarySourceLocation lastSourceLocation, 
        Func<string> getSource)
    {
      this.firstSourceLocation = firstSourceLocation;
      this.lastSourceLocation = lastSourceLocation;
      this.source = new Lazy<string>(getSource);
    }

    public override int Column
    {
      get
      {
        return this.firstSourceLocation.StartColumn;
      }
    }

    public override string Filename
    {
      get
      {
        IIncludedSourceLocation/*?*/ iloc = this.firstSourceLocation as IIncludedSourceLocation;
        if (iloc != null) return iloc.OriginalSourceDocumentName.Replace("\\\\", "\\");
        return this.firstSourceLocation.PrimarySourceDocument.Name.Value;
      }
    }

    public override int Line
    {
      get
      {
        IIncludedSourceLocation/*?*/ iloc = this.firstSourceLocation as IIncludedSourceLocation;
        if (iloc != null) return iloc.OriginalStartLine;
        return this.firstSourceLocation.StartLine;
      }
    }

    public int EndLine
    {
      get
      {
        IIncludedSourceLocation/*?*/ iloc = this.lastSourceLocation as IIncludedSourceLocation;
        if (iloc != null) return iloc.OriginalEndLine;
        return this.lastSourceLocation.EndLine;
      }
    }

    public override int Byte
    {
      get { return this.firstSourceLocation.StartIndex; }
    }

    public override string Value
    {
      get { return this.source.Value; }
    }


    #region IPrimarySourceLocation Members

    int IPrimarySourceLocation.EndColumn
    {
      get { return this.lastSourceLocation.EndColumn; }
    }

    int IPrimarySourceLocation.EndLine
    {
      get { 
        var iloc = this.lastSourceLocation as IIncludedSourceLocation;
        return iloc != null ? iloc.OriginalEndLine : this.lastSourceLocation.EndLine;
      }
    }

    IPrimarySourceDocument IPrimarySourceLocation.PrimarySourceDocument
    {
      get
      {
        var iloc = this.firstSourceLocation as IIncludedSourceLocation;
        return iloc != null ? iloc.SourceDocument as IPrimarySourceDocument : this.firstSourceLocation.SourceDocument as IPrimarySourceDocument;
      }
    }

    int IPrimarySourceLocation.StartColumn
    {
      get { return this.firstSourceLocation.StartColumn; }
    }

    int IPrimarySourceLocation.StartLine
    {
      get
      {
        var iloc = this.firstSourceLocation as IIncludedSourceLocation;
        return iloc != null ? iloc.OriginalStartLine : this.firstSourceLocation.StartLine;
      }
    }

    string IOriginalDocumentLocation.OriginalDocumentLocation
    {
      get
      {
        var iloc = this.firstSourceLocation as IIncludedSourceLocation;
        return iloc != null ? iloc.OriginalSourceDocumentName.Replace("\\\\", "\\") : this.firstSourceLocation.SourceDocument.Location;

      }
    }

    #endregion

    #region ISourceLocation Members

    bool ISourceLocation.Contains(ISourceLocation location)
    {
      throw new System.NotImplementedException();
    }

    int ISourceLocation.CopyTo(int offset, char[] destination, int destinationOffset, int length)
    {
      throw new System.NotImplementedException();
    }

    int ISourceLocation.EndIndex
    {
      get { throw new System.NotImplementedException(); }
    }

    int ISourceLocation.Length
    {
      get { throw new System.NotImplementedException(); }
    }

    ISourceDocument ISourceLocation.SourceDocument
    {
      get { throw new System.NotImplementedException(); }
    }

    string ISourceLocation.Source
    {
      get { throw new System.NotImplementedException(); }
    }

    int ISourceLocation.StartIndex
    {
      get { throw new System.NotImplementedException(); }
    }

    #endregion

    #region ILocation Members

    IDocument ILocation.Document
    {
      get { throw new System.NotImplementedException(); }
    }

    #endregion
  }
}
