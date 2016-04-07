//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Globalization;
using System.Text;
using Microsoft.Cci;
using Microsoft.Cci.Ast;
using Microsoft.Research.Vcc.Parsing;
//^ using Microsoft.Contracts;

namespace Microsoft.Research.Vcc.Preprocessing {

  public sealed class Preprocessor {

    /// <summary>Changes to false as soon as a non blank character is produced as preprocessor output.</summary>
    private bool allowPPDefinitions = true;

    /// <summary>The characters to scan for preprocessor directives.</summary>
    private char[] buffer; //^ invariant buffer.Length > 0;

    /// <summary>The document to preprocess.</summary>
    private readonly IVccUnpreprocessedSourceDocument documentToProcess;

    /// <summary>When an error is reported, the source location of the error spans the interval from errorIndex to fragmentIndex.</summary>
    private int errorIndex; //^ invariant 0 <= errorIndex && errorIndex <= fragmentIndex && (errorIndex < fragmentLength || errorIndex == 0);

    /// <summary>The index of the next character to scan in the current fragment.</summary>
    private int fragmentIndex; //^ invariant 0 <= fragmentIndex && fragmentIndex <= fragmentLength;

    /// <summary>The number of characters in the current fragment.</summary>
    private int fragmentLength; //^ invariant 0 <= fragmentLength && fragmentLength < buffer.Length;
    //^ invariant this.fragmentLength == 0 ==> this.startOfCurrentLine == 0;
    //^ invariant this.offset+this.fragmentLength <= this.documentToProcess.Length;

    /// <summary>The index of the character this.documentToProcess that corresponds to this.buffer[0]. 
    /// Add offset to fragmentIndex to arrive at the index of the current character in the document.</summary>
    private int offset; //^ invariant 0 <= offset && offset+fragmentLength <= documentToProcess.Length;

    /// <summary>
    /// A line number that appeared in the last #line directive. Only valid if this.sourceOfInclusion is not null.
    /// If valid, then the text currently being processed originally came from another document via an inclusion performed by an earlier preprocessor.
    /// The line number represents the line number, in the original document, of the first line of the included text.
    /// </summary>
    private int originalLineNumber;

    /// <summary>The preprocessor symbols defined by the given compiler options as well as any #define directives. Affected by #undef directives.
    /// Does not change once allowPPDefinitions becomes false.</summary>
    private IDictionary<string,string> preprocessorDefinedSymbols;

    /// <summary>
    /// The document from which the text currently being processed originally came from. I.e. the current text represents the result of an inclusion done
    /// by an earlier preprocessor. This is null if no #line directive has been encountered so far, or if the last #line directive encountered was #line default.
    /// </summary>
    private SourceDocumentWithInclusion/*?*/ sourceOfInclusion;

    /// <summary>Either 0 or the index of first character past the last line termination sequence encountered in this fragment. </summary>
    private int startOfCurrentLine; //^ invariant 0 <= startOfCurrentLine && startOfCurrentLine <= fragmentIndex;

    /// <summary>
    /// Allocates a preprocessor instance that can be queried for a list of source locations that represent the output from the preprocessor. This output
    /// omits preprocessor directives as well as any excluded sections. It also applies line directives by mapping some of the produced source locations
    /// onto the documents mentioned in the line directives. In other words, the produced source locations will not necessarily come from the document
    /// being preprocessed. Preprocessing happens lazily when the result of calling GetIncludedSections is enumerated.
    /// </summary>
    /// <param name="documentToProcess">The source document to preprocess.</param>
    /// <param name="options">An object that specifies any preprocessor symbols that are defined as compiler options by the environment.</param>
    internal Preprocessor(IVccUnpreprocessedSourceDocument documentToProcess, VccOptions options) {
      this.documentToProcess = documentToProcess;
      List<IErrorMessage> errors = this.errors = new List<IErrorMessage>();
      this.preprocessorInformation = new PreprocessorInformation(documentToProcess, errors);
      Dictionary<string, string> preprocessorDefinedSymbols = new Dictionary<string,string>();
      foreach (string ppOption in options.PreprocessorOptions) {
        if (!ppOption.StartsWith("/D", StringComparison.Ordinal)) continue;
        int eqIndex = ppOption.IndexOf('=');
        if (eqIndex < 0) eqIndex = ppOption.Length;
        string symName = ppOption.Substring(2, eqIndex-2);
        preprocessorDefinedSymbols[symName] = eqIndex != ppOption.Length ? ppOption.Substring(eqIndex+1) : String.Empty;
      }
      preprocessorDefinedSymbols["true"] = "true";
      preprocessorDefinedSymbols.Remove("false");
      this.preprocessorDefinedSymbols = preprocessorDefinedSymbols;
      this.buffer = new char[8192];
    }

    internal Preprocessor(IVccUnpreprocessedSourceDocument documentToProcess, IDictionary<string, string> preprocessorDefinedSymbols, List<IErrorMessage> errors) {
      this.documentToProcess = documentToProcess;
      this.preprocessorDefinedSymbols = preprocessorDefinedSymbols;
      this.errors = errors;
      this.preprocessorInformation = new PreprocessorInformation(documentToProcess, errors);
      this.buffer = new char[8192];
    }

    internal int CopyTo(int offset, char[] destination, int destinationOffset, int length, IPrimarySourceLocation primarySourceLocation) {
      if (this.offset <= offset && offset < this.offset + this.buffer.Length && offset+length <= this.offset+this.buffer.Length) {
        Array.Copy(this.buffer, offset-this.offset, destination, destinationOffset, length);
        return length;
      } else
        return primarySourceLocation.CopyTo(offset-primarySourceLocation.StartIndex, destination, destinationOffset, length);
    }

    internal string GetSource(IPrimarySourceLocation primarySourceLocation) {
      if (this.offset <= primarySourceLocation.StartIndex && primarySourceLocation.EndIndex <= this.offset+this.buffer.Length)
        return new String(this.buffer, primarySourceLocation.StartIndex-this.offset, primarySourceLocation.Length);
      else
        return primarySourceLocation.Source;
    }

    /// <summary>
    /// An enumeration of any errors found by the preprocessor. Only complete once this.PreprocessingIsComplete is true.
    /// </summary>
    internal readonly List<IErrorMessage> errors;

    /// <summary>
    /// Returns an enumeration of the locations in the document being preprocessed that do not contain preprocessor directives and that are not excluded because
    /// of preprocessor directives. In addition, document sections that are mapped onto sections of other documents by means of line directives, will appear in the
    /// enumeration as if they were source locations from those documents, rather than source locations from the document being preprocessed.
    /// </summary>
    internal IEnumerable<ISourceLocation> GetIncludedSections() {
      foreach (ISourceLocation includedSection in this.ParseSection(false, false, false, true, true))
        yield return includedSection;
      this.preprocessingIsComplete = true;
    }

    /// <summary>
    /// Returns the current character (this.buffer[this.fragmentIndex]).
    /// If this.fragmentIndex == this.fragmentLength at the start of the method, a new fragment is first obtained. 
    /// The new fragment will start at the first character of the current source line. 
    /// In other words the new value of this.buffer will retain all of the
    /// characters from the start of the current source line.
    /// </summary>
    private char GetCurrentChar()
      //^ requires this.fragmentIndex <= this.fragmentLength;
      //^ requires this.fragmentLength == 0 ==> this.startOfCurrentLine == 0;
      //^ ensures 0 <= this.fragmentIndex && this.fragmentIndex <= this.fragmentLength;
      //^ ensures result != (char)0 ==> this.fragmentIndex < this.fragmentLength;
      //^ ensures this.fragmentIndex == old(this.fragmentIndex) || this.fragmentIndex == old(this.fragmentIndex) - old(this.startOfCurrentLine);
      //^ ensures this.offset+this.startOfCurrentLine == old(this.offset)+old(this.startOfCurrentLine); 
      //^ ensures this.fragmentLength == 0 ==> result == (char)0 && this.startOfCurrentLine == 0;
      //^ ensures this.fragmentLength > 0 ==> result == this.buffer[this.fragmentIndex];
    {
      if (this.fragmentIndex == this.fragmentLength) {
        //reached the end of a fragment while parsing a preprocessor directive. Get the next fragment and carry on.
        if (this.fragmentLength == 0) return (char)0; //Reached the end of the source document.
        this.GetNextFragment();
        if (this.fragmentLength == 0) return (char)0; //Reached the end of the source document.
      }
      return this.buffer[this.fragmentIndex];
    }

    /// <summary>
    /// Returns the current character (this.buffer[this.fragmentIndex]) and increments this.fragmentIndex by one.
    /// If this.fragmentIndex == this.fragmentLength at the start of the method, a new fragment is first obtained. 
    /// The new fragment will start at the first character of the current source line. 
    /// In other words the new value of this.buffer will retain all of the
    /// characters from the start of the current source line.
    /// </summary>
    private char GetCurrentCharAndAdvanceIndex()
      //^ requires this.fragmentIndex < this.fragmentLength;
      //^ ensures 0 <= this.fragmentIndex && this.fragmentIndex <= this.fragmentLength;
      //^ ensures this.fragmentIndex == old(this.fragmentIndex) + 1 || this.fragmentIndex == old(this.fragmentIndex) - old(this.startOfCurrentLine) + 1;
      //^ ensures this.fragmentLength == 0 ==> result == (char)0;
      //^ ensures this.fragmentLength > 0 ==> this.fragmentIndex > 0 && result == this.buffer[this.fragmentIndex-1];
    {
      char c = this.GetCurrentChar();
      this.fragmentIndex++;
      return c;
    }

    /// <summary>
    /// Gets another fragment of characters from the source document and updates this.buffer, this.fragmentIndex and this.startOfCurrentLine accordingly.
    /// The new fragment will start with the first character of the current source line. If the old fragment started at the same character (in other words
    /// if the old fragment did not contain more than one complete source line), the size of the buffer is doubled so that the new fragment is 
    /// bigger than the old fragment and thus scanning will not get stuck.
    /// </summary>
    private void GetNextFragment()
      //^ requires this.fragmentLength > 0;
      //^ requires this.fragmentIndex == this.fragmentLength;
      //^ ensures this.buffer[this.fragmentLength] == 0;
      //^ ensures this.fragmentIndex == old(this.fragmentIndex) - old(this.startOfCurrentLine);
      //^ ensures this.errorIndex == old(this.errorIndex) - old(this.startOfCurrentLine);
      //^ ensures this.startOfCurrentLine == 0;
      //^ ensures this.offset == old(this.offset)+old(this.startOfCurrentLine); 
    {
      int newDocumentOffset = this.offset + this.fragmentLength;
      int lengthToKeep = this.fragmentLength-this.startOfCurrentLine;
      char[] oldBuffer = this.buffer;
      this.offset += this.startOfCurrentLine;
      if (this.startOfCurrentLine == 0 && this.fragmentLength > 0){
        //ran out of fragment before hitting a new line. Have to increase the size of the buffer (and thus the new fragment) in order not to get stuck.
        this.buffer = new char[this.buffer.Length*2];
      }
      //Don't ask the document for characters that were already obtained from it, they may no longer be in its buffer
      for (int i = 0; i < lengthToKeep; i++) this.buffer[i] = oldBuffer[this.startOfCurrentLine+i];
      this.fragmentLength = this.documentToProcess.CopyTo(newDocumentOffset, this.buffer, lengthToKeep, this.buffer.Length-1-lengthToKeep)+lengthToKeep;
      this.buffer[this.fragmentLength] = (char)0;
      this.fragmentIndex -= this.startOfCurrentLine;
      this.errorIndex -= this.startOfCurrentLine;
      this.startOfCurrentLine = 0;
    }

    /// <summary>
    /// Returns a source location that represents the span of characters from the current fragment.  
    /// </summary>
    /// <param name="position">The index in this.buffer of the first character of the source location.</param>
    /// <param name="length">The number of characters to include in the source location.</param>
    //^ [Pure]
    private ISourceLocation GetSourceLocation(int position, int length)
      // ^ requires 0 <= position && (position < this.Length || position == 0);
      // ^ requires 0 <= length;
      // ^ requires length <= this.Length;
      // ^ requires position+length <= this.Length;
    {
      return new PreprocessorSourceLocation((IPrimarySourceLocation)this.documentToProcess.GetSourceLocation(this.offset+position, length), this);
    }

    /// <summary>
    /// Add a new error to this.errors. The source location of the error is the span of text from this.errorIndex to this.fragmentIndex.
    /// </summary>
    private void HandleError(Error error, params string[] messageArguments) 
      //^ requires this.fragmentIndex <= this.fragmentLength;
      //^ requires this.errorIndex < this.fragmentIndex;
    {
      ISourceLocation errorLocation = this.GetSourceLocation(this.errorIndex, this.fragmentIndex-this.errorIndex);
      this.errors.Add(new VccErrorMessage(errorLocation, error, messageArguments));
    }

    /// <summary>
    /// An object that captures information gathered by the preprocessor, such as the symbols defined at a given point in the source document.
    /// This object can also be used to find the locations of excluded code blocks, the locations of preprocessor directives and so on.
    /// Evaluate this property only after preprocessing has been completed (this.PreprocessingIsComplete is true).
    /// </summary>
    internal PreprocessorInformation PreprocessorInformation {
      get
        //^ requires this.PreprocessingIsComplete;
      {
        return this.preprocessorInformation;
      }
    }
    private PreprocessorInformation preprocessorInformation;

    /// <summary>
    /// Becomes true as soon as the enumeration of source locations returned by GetIncludedSections has been fully enumerated.
    /// Once this is true, the Errors and PreprocessorInformation properties may be evaluated.
    /// </summary>
    internal bool PreprocessingIsComplete {
      get { return this.preprocessingIsComplete; }
    }
    private bool preprocessingIsComplete;

    /// <summary>
    /// Parses a block of text that corresponds to either the entire document, or a nested section of an #if-#elif-#else-#endif directive or the body of a #region directive.
    /// </summary>
    /// <param name="allowElse">True if a section of an #if directive is being parsed and the section can be terminated with an #elif or #else.
    /// This has to be false after the #else directive has been encountered, since an #else cannot be followed by another #else or an #elif.</param>
    /// <param name="allowEndif">True if an #if directive is being parsed.</param>
    /// <param name="allowEndregion">True if a #region block is being parsed.</param>
    /// <param name="include">True if the section being parsed is not part of an excluded block.</param>
    /// <param name="allowElseToInclude">True if an #if is being parsed and none of the conditions seen so far have been true.</param>
    private IEnumerable<ISourceLocation> ParseSection(bool allowElse, bool allowEndif, bool allowEndregion, bool include, bool allowElseToInclude) {
      int startIndex = this.startOfCurrentLine; //The first character that does not form part of a preprocessor directive that has already been parsed.
      bool onlyWhiteSpaceSeenSoFar = true; //While this is true, the current source line could well be a preprocessor directive.
      for (;;) {
        this.SkipUntilEligibleHash(ref onlyWhiteSpaceSeenSoFar);

        if (this.startOfCurrentLine > startIndex) {
          //While scanning for the start of a preprocessor directive, we've skipped over one or more source lines that have not yet been reported.
          //Construct a source location that includes all of the completed lines scanned since the last time around this loop 
          //(startIndex keeps track of the last value of this.startOfCurrentLine).
          ISourceLocation fragmentUpToStartOfCurrentLine;
          if (this.sourceOfInclusion != null)
            fragmentUpToStartOfCurrentLine = new PreprocessorSourceLocation(
              (IPrimarySourceLocation)this.sourceOfInclusion.GetSourceLocation(this.offset+startIndex, this.startOfCurrentLine-startIndex), this);
          else
            fragmentUpToStartOfCurrentLine = this.GetSourceLocation(startIndex, this.startOfCurrentLine-startIndex);
          if (include) {
            if (!onlyWhiteSpaceSeenSoFar)  //The scanner has something to scan, so the first "real" token will be formed before we hit another preprocessor directive.
              this.allowPPDefinitions = false; //The effect of this to allow the scanner to back up without needing to back up the preprocessor as well.
            this.preprocessorInformation.includedLocations.Add(fragmentUpToStartOfCurrentLine);
            yield return fragmentUpToStartOfCurrentLine;
          } else {
            this.preprocessorInformation.excludedLocations.Add(fragmentUpToStartOfCurrentLine);
          }
        }

        if (this.buffer[this.fragmentIndex] != '#') {
          //ran into the end of the current fragment before discovering the start of a preprocessor directive
          this.GetNextFragment(); //gets a new buffer starting from this.offset += this.startOfCurrentLine (if need be, the buffer size will increase until it can hold the entire extent of the current line).
          if (this.fragmentLength == 0) yield break; //end of document
          startIndex = this.startOfCurrentLine; //Everything up to this.startOfCurrentLine has already been yielded if necessary. Next time around, we need to yield text starting with the current line.
          continue;
        }

        this.errorIndex = this.fragmentIndex++; //The position of the '#' that starts the directive
        string directive = this.ScanDirective();
        switch (directive) {
          case "define":
            this.ParseDefine(include);
            break;
          case "elif" :
            if (allowElse){
              foreach (ISourceLocation includedSourceFragment in this.ParseElif(allowElseToInclude))
                yield return includedSourceFragment;
              break;
            }
            goto default;
          case "else" :
            if (allowElse){
              foreach (ISourceLocation includedSourceFragment in this.ParseElse(allowElseToInclude))
                yield return includedSourceFragment;
              break;
            }
            goto default;
          case "endif" :
            if (allowEndif){
              this.ParseEndif();
              break;
            }
            goto default;
          case "endregion" :
            if (allowEndregion) {
              this.ParseEndregion();
              yield break;
            }
            goto default;
          case "error":
            this.ParseError(include);
            break;
          case "if":
            foreach (ISourceLocation includedSourceFragment in this.ParseIf(include)) 
              yield return includedSourceFragment;
            break;
          case "include":
            foreach (ISourceLocation includedSourceFragment in this.ParseInclude(include))
              yield return includedSourceFragment;
            break;
          case "line":
            this.ParseLine(include);
            break;
          case "pragma": 
            this.ParsePragma(include);
            break;
          case "region" :
            foreach (ISourceLocation includedSourceFragment in this.ParseRegion(include))
              yield return includedSourceFragment;
            break;
          case "undef":
            this.ParseUndefine(include);
            break;
          case "warning" :
            this.ParseWarning(include);
            break;
          default:
            this.HandleError(Error.PPDirectiveExpected);
            this.SkipRestOfDirective();
            break;
        }

        startIndex = this.fragmentIndex; //At this point everything up to this.fragmentIndex has been scanned and yielded (if included).
        onlyWhiteSpaceSeenSoFar = true; //Trivally true since the end of a directive is also the start of a new line.
      }
    }

    /// <summary>
    /// Parses a #define directive, starting at the character following "define". 
    /// Updates this.preprocessorDefinedSymbols and adds a directive object to this.PreprocessorInformation.
    /// Leaves this.fragmentIndex pointing to the start of the first line after the line containing the #define directive. 
    /// </summary>
    /// <param name="include">True if the definition is part of an included block. If false, the directive is parsed but ignored.</param>
    private void ParseDefine(bool include)
      //^ requires this.errorIndex < this.fragmentIndex;
      //^ requires this.fragmentIndex > this.startOfCurrentLine;
      //^ requires this.fragmentIndex <= this.fragmentLength;
      //^ ensures this.startOfCurrentLine == this.fragmentIndex;
    {
      if (!this.allowPPDefinitions) {
        this.HandleError(Error.PPDefFollowsToken);
        this.SkipRestOfDirective();
        return;
      }
      if (!Scanner.IsBlankSpace(this.GetCurrentChar())) {
        this.errorIndex = this.fragmentIndex;
        this.SkipRestOfDirective();
        //^ assume this.fragmentIndex > this.errorIndex;
        this.HandleError(Error.ExpectedIdentifier);
        return;
      }
      string s = this.ScanIdentifier();
      if (s == "true" || s == "false") {
        this.errorIndex = this.fragmentIndex-s.Length;
        this.HandleError(Error.ExpectedIdentifier);
        this.SkipRestOfDirective();
        return;
      }
      if (include) this.preprocessorDefinedSymbols[s] = s;
      PreprocessorSymbol sym = new PreprocessorSymbol(s, this.GetSourceLocation(this.fragmentIndex-s.Length, s.Length));
      ISourceLocation loc = this.GetSourceLocation(this.startOfCurrentLine, this.fragmentIndex-this.startOfCurrentLine);
      this.preprocessorInformation.directives.Add(new DefineDirective(sym, loc));
      this.SkipPastBlanksCommentAndNewLine();
    }

    /// <summary>
    /// Parses the #elif-#else-#endif part of an #if-#elif-#else-#endif construct, starting at the character following "elif". 
    /// Updates the last IfDirective instance added to this.preprocessorInformation with an additional ElifPart.
    /// Leaves this.fragmentIndex pointing to the start of the first line after the #endif directive.
    /// Returns all source locations that are to be included in the preprocessor output. (No locations are returned if the include parameter is false.)
    /// </summary>
    /// <param name="include">True if the definition is part of an included block. If false, the directive is parsed but ignored. (No locations are returned.)</param>
    private IEnumerable<ISourceLocation> ParseElif(bool include) {
      PreprocessorExpression condition = this.ParseExpression();
      ElifPart elif = new ElifPart(condition, this.GetSourceLocation(this.startOfCurrentLine, this.fragmentIndex-this.startOfCurrentLine));
      this.preprocessorInformation.AddElif(elif);
      this.SkipPastBlanksCommentAndNewLine();
      bool allowElseToInclude = include;
      if (include) {
        include = condition.IsDefined(this.preprocessorDefinedSymbols);
        if (include) allowElseToInclude = false;
      }
      foreach (ISourceLocation includedSourceFragment in this.ParseSection(true, true, false, include, allowElseToInclude))
        yield return includedSourceFragment;
    }

    /// <summary>
    /// Parses the #else-#endif part of an #if-#elif-#else-#endif construct, starting at the character following "else". 
    /// Updates the last IfDirective instance added to this.preprocessorInformation with an ElsePart.
    /// Leaves this.fragmentIndex pointing to the start of the first line after the #endif directive.
    /// Returns all source locations that are to be included in the preprocessor output. (No locations are returned if the include parameter is false.)
    /// </summary>
    /// <param name="include">True if the definition is part of an included block. If false, the directive is parsed but ignored. (No locations are returned.)</param>
    private IEnumerable<ISourceLocation> ParseElse(bool include) {
      ElsePart @else = new ElsePart(this.GetSourceLocation(this.startOfCurrentLine, this.fragmentIndex-this.startOfCurrentLine));
      this.preprocessorInformation.AddElse(@else);
      this.SkipPastBlanksCommentAndNewLine();
      foreach (ISourceLocation includedSourceFragment in this.ParseSection(false, true, false, include, false))
        yield return includedSourceFragment;
    }

    /// <summary>
    /// Parses the #endif part of an #if-#elif-#else-#endif construct, starting at the character following "endif". 
    /// Updates the last IfDirective instance added to this.preprocessorInformation with an EndifPart.
    /// Leaves this.fragmentIndex pointing to the start of the first line after the #endif directive.
    /// </summary>
    private void ParseEndif()
      //^ ensures this.startOfCurrentLine == this.fragmentIndex;
    {
      EndifPart endif = new EndifPart(this.GetSourceLocation(this.startOfCurrentLine, this.fragmentIndex-this.startOfCurrentLine));
      this.preprocessorInformation.AddEndif(endif);
      this.SkipPastBlanksCommentAndNewLine();
    }

    /// <summary>
    /// Parses the #endregion part of a #region-#endregion directive, starting at the character following "region". 
    /// Updates the last RegionDirective instance added to this.preprocesorInformation with an EndregionPart.
    /// Leaves this.fragmentIndex pointing to the start of the first line after the matching #endregion directive.
    /// </summary>
    private void ParseEndregion()
      //^ ensures this.startOfCurrentLine == this.fragmentIndex;
    {
      ISourceLocation sourceLocation = this.GetSourceLocation(this.startOfCurrentLine, this.fragmentIndex-this.startOfCurrentLine);
      string label = this.ScanMessage();
      EndregionPart endregion = new EndregionPart(label, sourceLocation);
      this.preprocessorInformation.AddEndregion(endregion);
    }

    /// <summary>
    /// Parses an #error directive, starting at the character following "error".
    /// Adds an ErrorDirective instance to this.preprocesorInformation.
    /// Leaves this.fragmentIndex pointing to the start of the first line after the line containing the #error directive. 
    /// </summary>
    private void ParseError(bool include)
      //^ ensures this.startOfCurrentLine == this.fragmentIndex;
    {
      ISourceLocation sourceLocation = this.GetSourceLocation(this.startOfCurrentLine, this.fragmentIndex-this.startOfCurrentLine);
      string message = this.ScanMessage();
      if (include) {
        ErrorDirective errorDirective = new ErrorDirective(message, sourceLocation);
        this.preprocessorInformation.directives.Add(errorDirective);
        if (message.Length > 0) {
          //^ assume this.fragmentIndex > this.errorIndex;
          this.HandleError(Error.ErrorDirective, message);
        }
      }
    }

    /// <summary>
    /// Parses the expression that follows an #if or #elif directive.
    /// The resulting expression can consist of one or more and expressions combined with the || operator.
    /// Leaves this.fragmentIndex pointing to the first non blank character that is not part of the expression.
    /// </summary>
    private PreprocessorExpression ParseExpression()
      //^ requires this.fragmentIndex > this.startOfCurrentLine;
    {
      PreprocessorExpression result = this.ParseAndExpression();
      this.SkipBlanks();
      char c = this.GetCurrentChar();
      //^ assert c == '|' ==> this.fragmentIndex < this.fragmentLength;
      while (c == '|') 
        // ^ invariant this.fragmentIndex < this.fragmentLength;
      {
        //^ assume this.fragmentIndex < this.fragmentLength;
        this.fragmentIndex++;
        char c2 = this.GetCurrentChar();
        //^ assert c2 == '|' ==> this.fragmentIndex < this.fragmentLength;
        if (c2 == '|') {
          this.fragmentIndex++;
          result = new OrExpression(result, this.ParseAndExpression());
          c2 = this.SkipBlanks();
          //^ assert c2 == '|' ==> this.fragmentIndex < this.fragmentLength;
        } else {
          this.errorIndex = this.fragmentIndex-1;
          this.HandleError(Error.InvalidPreprocExpr);
          this.SkipToCommentOrNewLine();
          return result;
        }
        c = c2;
        //^ assert c == '|' ==> this.fragmentIndex < this.fragmentLength;
      }
      return result;
    }

    /// <summary>
    /// Parses an expression than can combine one or more equality expressions with the && operator.
    /// Leaves this.fragmentIndex pointing to the first non blank character that is not part of the expression.
    /// This can be the start of an || operator or a comment or the end of the current line.
    /// </summary>
    private PreprocessorExpression ParseAndExpression()
      //^ requires this.fragmentIndex > this.startOfCurrentLine;
    {
      PreprocessorExpression result = this.ParseEqualityExpression();
      this.SkipBlanks();
      char c = this.GetCurrentChar();
      //^ assert c == '&' ==> this.fragmentIndex < this.fragmentLength;
      while (c == '&')
        // ^ invariant this.fragmentIndex < this.fragmentLength;
      {
        //^ assume this.fragmentIndex < this.fragmentLength;
        this.fragmentIndex++;
        char c2 = this.GetCurrentChar();
        if (c2 == '&') {
          result = new AndExpression(result, this.ParseEqualityExpression());
          c2 = this.SkipBlanks();
        } else {
          this.errorIndex = this.fragmentIndex-1;
          this.HandleError(Error.InvalidPreprocExpr);
          this.SkipToCommentOrNewLine();
          return result;
        }
        c = c2;
        //^ assert c == '&' ==> this.fragmentIndex < this.fragmentLength;
      }
      return result;
    }

    /// <summary>
    /// Parses an expression than can combine one or more unary expressions with the == or != operator.
    /// Leaves this.fragmentIndex pointing to the first non blank character that is not part of the expression.
    /// This can be the start of an && operator, an || operator, or a comment or the end of the current line.
    /// </summary>
    private PreprocessorExpression ParseEqualityExpression()
      //^ requires this.fragmentIndex > this.startOfCurrentLine;
    {
      PreprocessorExpression result = this.ParseUnaryExpression();
      this.SkipBlanks();
      char c = this.GetCurrentChar();
      //^ assert (c == '=' || c == '!') ==> this.fragmentIndex < this.fragmentLength;
      while (c == '=' || c == '!')
        // ^ invariant this.fragmentIndex < this.fragmentLength;
      {
        //^ assume this.fragmentIndex < this.fragmentLength;
        this.fragmentIndex++;
        char c2 = this.GetCurrentChar();
        if (c2 == '=') {
          this.fragmentIndex++;
          if (c == '=')
            result = new EqualsExpression(result, this.ParseUnaryExpression());
          else
            result = new NotEqualsExpression(result, this.ParseUnaryExpression());
          c2 = this.SkipBlanks();
        } else {
          this.errorIndex = this.fragmentIndex-1;
          this.HandleError(Error.InvalidPreprocExpr);
          this.SkipToCommentOrNewLine();
          return result;
        }
        c = c2;
        //^ assert (c == '=' || c == '!') ==> this.fragmentIndex < this.fragmentLength;
      }
      return result;
    }

    /// <summary>
    /// Parses a primary expression, optionally preceded by a ! operator.
    /// Leaves this.fragmentIndex pointing to the first non blank character that is not part of the expression.
    /// This can be the start of an == operator, a != operator, an && operator, an || operator, or a comment or the end of the current line.
    /// </summary>
    private PreprocessorExpression ParseUnaryExpression()
      //^ requires this.fragmentIndex > this.startOfCurrentLine;
    {
      this.SkipBlanks();
      char c = this.buffer[this.fragmentIndex];
      if (c == '!') {
        int position = this.fragmentIndex++;
        this.SkipBlanks();
        PreprocessorExpression operand = this.ParsePrimaryExpression();
        return new NotExpression(operand, this.GetSourceLocation(position, this.fragmentIndex-position));
      }
      return this.ParsePrimaryExpression();
    }

    /// <summary>
    /// Parses an identifier or a parenthesized expression.
    /// Leaves this.fragmentIndex pointing to the first non blank character that is not part of the expression.
    /// This can be the start of an == operator, a != operator, an && operator, an || operator, or a comment or the end of the current line.
    /// </summary>
    private PreprocessorExpression ParsePrimaryExpression()
      //^ requires this.fragmentIndex > this.startOfCurrentLine;
    {
      char c = this.GetCurrentChar();
      if (c == '/' || Scanner.IsEndOfLine(c)) {
        this.errorIndex = this.fragmentIndex++;
        this.HandleError(Error.InvalidPreprocExpr);
        this.SkipPastBlanksCommentAndNewLine();
        return new MissingExpression(this.GetSourceLocation(this.errorIndex, 1));
      }
      PreprocessorExpression result;
      if (c == '(') {
        this.fragmentIndex++;
        result = this.ParseExpression();
        c = this.SkipBlanks();
        if (c != ')') {
          this.errorIndex = this.fragmentIndex-1;
          this.HandleError(Error.ExpectedRightParenthesis);
        }
        return result; //TODO: keep track of the parentheses
      }
      int position = this.fragmentIndex - this.startOfCurrentLine;
      //^ assert position > 0;
      string symbolName = this.ScanIdentifier();
      //^ assume position+this.startOfCurrentLine <= this.fragmentLength;
      return new PreprocessorSymbol(symbolName, this.GetSourceLocation(position+this.startOfCurrentLine, this.fragmentIndex-(position+this.startOfCurrentLine)));
    }

    /// <summary>
    /// Parses the #if part of an #if-#elif-#else-#endif construct, starting at the character following "if". 
    /// Adds a corresponding IfDirective instance to this.preprocesorInformation.
    /// Leaves this.fragmentIndex pointing to the start of the first line after the matching #endif directive.
    /// Returns all source locations that are to be included in the preprocessor output. (No locations are returned if the include parameter is false.)
    /// </summary>
    /// <param name="include">True if the directive is part of an included block. If false, the directive is parsed but ignored. (No locations are returned.)</param>
    private IEnumerable<ISourceLocation> ParseIf(bool include)  {
      SourceLocationBuilder slb = new SourceLocationBuilder(this.GetSourceLocation(this.startOfCurrentLine, this.fragmentIndex-this.startOfCurrentLine));
      PreprocessorExpression condition = this.ParseExpression();
      IfDirective ifDirective = new IfDirective(condition, slb);
      this.preprocessorInformation.directives.Add(ifDirective);
      this.SkipPastBlanksCommentAndNewLine();
      bool allowElseToInclude = include;
      if (include) {
        include = condition.IsDefined(this.preprocessorDefinedSymbols);
        if (include)
          allowElseToInclude = false;
      }
      foreach (ISourceLocation includedSourceFragment in this.ParseSection(true, true, false, include, allowElseToInclude))
        yield return includedSourceFragment;
      slb.UpdateToSpan(this.GetSourceLocation(this.fragmentIndex-1, 0));
    }

    /// <summary>
    /// Parses a #line directive, starting at the character following "line".
    /// Adds a LineDirective instance to this.preprocesorInformation.
    /// Leaves this.fragmentIndex pointing to the start of the first line after the line containing the #line directive. 
    /// </summary>
    private void ParseLine(bool include)
      //^ requires this.fragmentIndex > 0;
      //^ ensures this.startOfCurrentLine == this.fragmentIndex;
    {
      this.SkipBlanks();
      int? lineNumber = null;
      string/*?*/ documentName = null;
      string docName;
      this.errorIndex = this.fragmentIndex;
      char c = this.GetCurrentChar();
      if (c == 'd') {
        string d = this.ScanDirective();
        if (d != "default") {
          //^ assume this.fragmentIndex > this.errorIndex;
          this.HandleError(Error.PPDirectiveExpected);
        }
        this.sourceOfInclusion = null;
      } else {
        if (!Scanner.IsDigit(c)) {
          if (this.fragmentIndex == this.fragmentLength)
            this.errorIndex = fragmentIndex -1;
          else
            this.fragmentIndex++;
          this.HandleError(Error.InvalidLineNumber);
        } else
          lineNumber = this.originalLineNumber = this.ScanNumber();
      }
      this.SkipBlanks();
      if (this.GetCurrentChar() == '"') {
        documentName = docName = this.ScanString('"');
      } else {
        docName = this.documentToProcess.Name.Value;
        if (this.sourceOfInclusion != null) docName = this.sourceOfInclusion.Name.Value;
      }
      if (include) {
        //^ assume this.fragmentIndex > this.startOfCurrentLine;
        LineDirective lineDirective = new LineDirective(lineNumber, documentName, this.GetSourceLocation(this.startOfCurrentLine, this.fragmentIndex-this.startOfCurrentLine));
        this.preprocessorInformation.directives.Add(lineDirective);
      }
      //^ assume this.fragmentIndex <= this.fragmentLength;
      this.SkipPastBlanksCommentAndNewLine();
      this.sourceOfInclusion = new SourceDocumentWithInclusion(this.documentToProcess, this.originalLineNumber, docName, this.offset+this.startOfCurrentLine);
    }

    /// <summary>
    /// Parses a #pragma warning directive, starting at the character following "pragma".
    /// Adds a PragmaWarningDirective instance to this.preprocesorInformation.
    /// Leaves this.fragmentIndex pointing to the start of the first line after the line containing the #pragma warning directive. 
    /// </summary>
    private void ParsePragma(bool include)
      //^ requires this.fragmentIndex > this.startOfCurrentLine;
      //^ ensures this.startOfCurrentLine == this.fragmentIndex;
    {
      this.SkipBlanks();
      //^ assume 0 <= this.fragmentIndex && this.fragmentIndex <= this.fragmentLength;
      this.SkipPastBlanksCommentAndNewLine();
      return;
      /*
      this.errorIndex = this.fragmentIndex;
      bool disabled = false;
      string/*?* / action = null;
      string kind = this.ScanDirective();
      if (kind == "once" || kind == "pack") {
        //^ assume 0 <= this.fragmentIndex && this.fragmentIndex <= this.fragmentLength;
        this.SkipPastBlanksCommentAndNewLine();
        return;
      }
      if (kind != "warning") {
        if (this.errorIndex == this.fragmentIndex) this.errorIndex--;
        this.HandleError(Error.IllegalPragma);
        if (kind == "disable" || kind == "restore")
          action = kind;
      }
      if (action == null){
        this.SkipBlanks();
        this.errorIndex = this.fragmentIndex;
        action = this.ScanDirective();
        if (this.errorIndex == this.fragmentIndex) this.errorIndex--;
      }
      if (action == "restore")
        disabled = false;
      else if (action != "disable")
        this.HandleError(Error.IllegalPPWarning);
      List<WarningNumber> warnings = new List<WarningNumber>();
      //^ assume this.fragmentIndex > this.startOfCurrentLine;
      for (; ; ) 
        //^ invariant this.startOfCurrentLine >= 0;
        //^ invariant this.fragmentIndex > this.startOfCurrentLine;
        //^ invariant this.fragmentIndex <= this.fragmentLength;
        //^ invariant this.errorIndex <= this.fragmentIndex;
        //^ invariant this.fragmentLength == 0 ==> this.startOfCurrentLine == 0;
      {
        char c = this.SkipBlanks();
        //^ assume this.fragmentIndex > this.startOfCurrentLine; //SkipBlanks does not scan past the end of the current (non empty) line.
        this.errorIndex = this.fragmentIndex;
        if (!Scanner.IsDigit(c)) {
          if (this.fragmentIndex == this.fragmentLength) {
            //^ assert this.fragmentLength > 0;
            this.errorIndex--;
            this.HandleError(Error.InvalidNumber);
          } else {
            //^ assert 0 <= this.fragmentIndex;
            //^ assert this.fragmentIndex < this.fragmentLength;
            this.fragmentIndex++;
            this.HandleError(Error.InvalidNumber);
            this.fragmentIndex--;
            //^ assume 0 <= this.fragmentIndex;
          }
          break;
        } else {
          int number = this.ScanNumber();
          //^ assume 0 <= this.errorIndex && this.errorIndex < this.fragmentIndex;
          //^ assume this.fragmentIndex <= this.fragmentLength;
          warnings.Add(new WarningNumber(number, this.GetSourceLocation(this.errorIndex, this.fragmentIndex-this.errorIndex)));
        }
        this.SkipBlanks();
        //^ assume this.fragmentIndex <= this.fragmentLength;
        //^ assume this.fragmentLength == 0 ==> this.startOfCurrentLine == 0;
        c = this.GetCurrentChar();
        if (c != ',') break;
        //^ assume this.fragmentIndex > this.startOfCurrentLine;;
      }
      //^ assume 0 <= this.startOfCurrentLine && this.startOfCurrentLine <= this.fragmentIndex;
      //^ assume this.fragmentIndex < this.fragmentLength;
      if (include) {
        ISourceLocation sourceLocation = this.GetSourceLocation(this.startOfCurrentLine, this.fragmentIndex-this.startOfCurrentLine);
        PragmaWarningDirective pragmaWarningDirective = new PragmaWarningDirective(disabled, warnings.AsReadOnly(), sourceLocation);
        this.preprocessorInformation.directives.Add(pragmaWarningDirective);
      }
      //^ assume 0 <= this.fragmentIndex && this.fragmentIndex <= this.fragmentLength;
      this.SkipPastBlanksCommentAndNewLine();
      */
    }

    /// <summary>
    /// Parses a #region-#endregion directive, starting at the character following "region". 
    /// Adds a corresponding RegionDirective instance to this.preprocesorInformation.
    /// Leaves this.fragmentIndex pointing to the start of the first line after the matching #endif directive.
    /// Returns all source locations that are to be included in the preprocessor output. (No locations are returned if the include parameter is false.)
    /// </summary>
    /// <param name="include">True if the directive is part of an included block. If false, the directive is parsed but ignored. (No locations are returned.)</param>
    private IEnumerable<ISourceLocation> ParseRegion(bool include) {
      SourceLocationBuilder slb = new SourceLocationBuilder(this.GetSourceLocation(this.startOfCurrentLine, this.fragmentIndex-this.startOfCurrentLine));
      string label = this.ScanMessage();
      RegionDirective regionDirective = new RegionDirective(label, slb);
      this.preprocessorInformation.directives.Add(regionDirective);
      foreach (ISourceLocation includedSourceFragment in this.ParseSection(false, false, true, include, false))
        yield return includedSourceFragment;
      slb.UpdateToSpan(this.GetSourceLocation(this.fragmentIndex-1, 0));
    }

    /// <summary>
    /// Parses an #include directive, starting at the character following "include".
    /// Adds an IncludeDirective instance to this.preprocesorInformation.
    /// Leaves this.fragmentIndex pointing to the start of the first line after the line containing the #include directive. 
    /// </summary>
    private IEnumerable<ISourceLocation> ParseInclude(bool include) 
      //^ requires this.fragmentIndex > this.startOfCurrentLine;
      //^ ensures this.startOfCurrentLine == this.fragmentIndex;
    {
      SourceLocationBuilder slb = new SourceLocationBuilder(this.GetSourceLocation(this.startOfCurrentLine, this.fragmentIndex-this.startOfCurrentLine));
      string/*?*/ fileToInclude = null;
      bool searchParentsDirectory = false;
      this.SkipBlanks();
      if (this.GetCurrentChar() == '"') {
        fileToInclude = this.ScanString('"');
        this.fragmentIndex++;
        searchParentsDirectory = true;
      } else if (this.GetCurrentChar() == '<') {
        fileToInclude = this.ScanString('>');
        this.fragmentIndex++;
      } else {
        this.HandleError(Error.PPDirectiveExpected);
      }
      slb.UpdateToSpan(this.GetSourceLocation(this.fragmentIndex, 0));
      this.preprocessorInformation.directives.Add(new IncludeDirective(fileToInclude, slb));
      this.SkipPastBlanksCommentAndNewLine();
      if (fileToInclude == null || !include) return Enumerable<ISourceLocation>.Empty;
      return this.GetIncludedContent(fileToInclude, searchParentsDirectory);
    }

    private IEnumerable<ISourceLocation> GetIncludedContent(string fileToInclude, bool searchParentsDirectory) {
      string/*?*/ path = this.GetFilePath(fileToInclude, searchParentsDirectory);
      if (path != null) {
        Preprocessor includedPreprocessor = this.documentToProcess.GetPreprocessorFor(path, this.preprocessorDefinedSymbols);
        return includedPreprocessor.GetIncludedSections();
      }
      return Enumerable<ISourceLocation>.Empty;
    }

    private string/*?*/ GetFilePath(string fileToInclude, bool searchParentsDirectory) {
      string/*?*/ path = null;
      if (searchParentsDirectory) {
        path = System.IO.Path.Combine(System.IO.Path.GetDirectoryName(this.documentToProcess.Location), fileToInclude);
        if (System.IO.File.Exists(path)) return path;
      }
      //TODO: use command line options
      string/*?*/ includeVar = System.Environment.GetEnvironmentVariable("INCLUDE");
      if (includeVar == null) includeVar = "";
      string[] includePaths = includeVar.Split(';');
      foreach (string includePath in includePaths) {
        path = System.IO.Path.Combine(includePath, fileToInclude);
        if (System.IO.File.Exists(path)) return path;
      }
      return null;
    }

    /// <summary>
    /// Parses an #undef directive, starting at the character following "undef". 
    /// Updates this.preprocessorDefinedSymbols and adds a directive object to this.PreprocessorInformation.
    /// Leaves this.fragmentIndex pointing to the start of the current line. 
    /// </summary>
    /// <param name="include">True if the definition is part of an included block. If false, the directive is parsed but ignored.</param>
    private void ParseUndefine(bool include)
      //^ requires this.errorIndex < this.fragmentIndex;
      //^ requires this.fragmentIndex > this.startOfCurrentLine;
      //^ ensures this.startOfCurrentLine == this.fragmentIndex;
    {
      if (!this.allowPPDefinitions) {
        this.HandleError(Error.PPDefFollowsToken);
        this.SkipRestOfDirective();
        return;
      }
      if (!Scanner.IsBlankSpace(this.GetCurrentChar())) {
        this.errorIndex = this.fragmentIndex;
        this.SkipRestOfDirective();
        //^ assume this.fragmentIndex > this.errorIndex;
        this.HandleError(Error.ExpectedIdentifier);
        return;
      }
      string s = this.ScanIdentifier();
      //^ assert this.startOfCurrentLine <= this.fragmentIndex-s.Length; 
      if (s == "true" || s == "false") {
        //^ assume s.Length > 0;
        this.errorIndex = this.fragmentIndex-s.Length;
        this.HandleError(Error.ExpectedIdentifier);
        this.SkipRestOfDirective();
        return;
      }
      if (include) this.preprocessorDefinedSymbols.Remove(s);
      PreprocessorSymbol sym = new PreprocessorSymbol(s, this.GetSourceLocation(this.fragmentIndex-s.Length, s.Length));
      ISourceLocation loc = this.GetSourceLocation(this.startOfCurrentLine, this.fragmentIndex-this.startOfCurrentLine);
      //^ assume loc.Contains(sym.SourceLocation);
      this.preprocessorInformation.directives.Add(new UndefDirective(sym, loc));
      this.SkipPastBlanksCommentAndNewLine();
    }

    /// <summary>
    /// Parses a #warning directive, starting at the character following "warning".
    /// Adds an ErrorDirective instance to this.preprocesorInformation.
    /// Leaves this.fragmentIndex pointing to the start of the first line after the line containing the #warning directive. 
    /// </summary>
    private void ParseWarning(bool include)
      //^ requires this.startOfCurrentLine < this.fragmentIndex;
      //^ ensures this.startOfCurrentLine == this.fragmentIndex;
    {
      ISourceLocation sourceLocation = this.GetSourceLocation(this.startOfCurrentLine, this.fragmentIndex-this.startOfCurrentLine);
      string message = this.ScanMessage();
      if (include) {
        WarningDirective warningDirective = new WarningDirective(message, sourceLocation);
        this.preprocessorInformation.directives.Add(warningDirective);
        if (message.Length > 0) {
          //^ assume this.fragmentIndex > this.errorIndex;
          this.HandleError(Error.WarningDirective, message);
        }
      }
    }

    /// <summary>
    /// Skips over any preceding blanks and then scans a possibly empty sequence of Ascii letters.
    /// Returns the sequence as a (possibly empty) string. 
    /// Leaves this.fragmentIndex pointing to the first character that is not included in the result string.
    /// </summary>
    private string ScanDirective() {
      this.SkipBlanks();
      int length = 0;
      for (; ; length++)
        //^ invariant this.fragmentIndex >= length;
      {
        char c = this.GetCurrentChar();
        if (!Scanner.IsAsciiLetter(c)) break;
        this.fragmentIndex++;
      }
      return new string(this.buffer, this.fragmentIndex-length, length);
    }

    /// <summary>
    /// Starting with this.fragmentIndex pointing to a backslash character, this routine
    /// scans a complete escape sequence and returns the corresponding (unescaped) character
    /// value. Upon return this.fragmentIndex points to the first character that is not
    /// part of the escape sequence. If the escape sequence is malformed, an error is reported.
    /// </summary>
    private char ScanEscapedChar()
      //^ requires this.fragmentIndex > 0;
      //^ requires this.buffer[this.fragmentIndex] == '\\';
    {
      int escVal = 0;
      bool requireFourDigits = false;
      //^ assume this.fragmentIndex < this.fragmentLength; //follows from this.buffer[this.fragmentIndex] == '\\'
      this.errorIndex = this.fragmentIndex;
      char ch = this.GetCurrentCharAndAdvanceIndex();
      //^ assume this.fragmentIndex > this.errorIndex;
      switch (ch) {
        default:
          this.HandleError(Error.IllegalEscape);
          if (ch == 'X') goto case 'x';
          return (char)0;
        // Single char escape sequences \a etc
        case 'a': return (char)7;
        case 'b': return (char)8;
        case 't': return (char)9;
        case 'n': return (char)10;
        case 'v': return (char)11;
        case 'f': return (char)12;
        case 'r': return (char)13;
        case '"': return '"';
        case '\'': return '\'';
        case '\\': return '\\';
        case '0': return (char)0;
        // unicode escape sequence \uHHHH
        case 'u':
          requireFourDigits = true;
          goto case 'x';
        // hexadecimal escape sequence \xH or \xHH or \xHHH or \xHHHH
        case 'x':
          for (int i = 0; i < 4; i++) {
            ch = this.GetCurrentCharAndAdvanceIndex();
            escVal <<= 4;
            if (Scanner.IsHexDigit(ch))
              escVal |= Scanner.GetHexValue(ch);
            else {
              if (i == 0 || requireFourDigits) {
                this.HandleError(Error.IllegalEscape);
              }
              return (char)(escVal >> 4);
            }
          }
          return (char)escVal;
      }
    }

    /// <summary>
    /// Scans an identifier according to standard C# identifier rules.
    /// Returns a string that represents the value of the identifier after
    /// any escape sequences have been interpreted (unescaped).
    /// </summary>
    private string ScanIdentifier() 
      //^ requires this.fragmentIndex > this.startOfCurrentLine;
      //^ ensures result.Length <= this.fragmentIndex-this.startOfCurrentLine;
      //^ ensures result.Length > 0;
    {
      this.SkipBlanks();
      StringBuilder sb = new StringBuilder();
      //^ assume sb.Length == 0;
      bool firstChar = true;
      for (; ; )
        //^ invariant this.fragmentIndex > this.startOfCurrentLine;
        //^ invariant sb.Length < this.fragmentIndex-this.startOfCurrentLine;
      {
        char c = this.GetCurrentChar();
        if (c == '\\') c = this.ScanEscapedChar();
        if (!IsIdentifierChar(c, firstChar)) break;
        sb.Append(c);
        this.fragmentIndex++;
        //^ assume sb.Length < this.fragmentIndex-this.startOfCurrentLine;
        firstChar = false;
      }
      //^ assume sb.Length < this.fragmentIndex-this.startOfCurrentLine;
      if (sb.Length == 0) {
        this.errorIndex = this.fragmentIndex-1;
        this.HandleError(Error.ExpectedIdentifier);
        sb.Append(' ');
      }
      string result = sb.ToString();
      //^ assume result.Length > 0;
      //^ assume result.Length < this.fragmentIndex-this.startOfCurrentLine;
      return result;
    }

    /// <summary>
    /// Returns true if the given character can legally start or form part of an identifier.
    /// </summary>
    /// <param name="c">The character to test.</param>
    /// <param name="firstChar">If true, an restricted set of characters are accepted. For example, an identifier may not start with a digit.</param>
    private static bool IsIdentifierChar(char c, bool firstChar) {
      if ('a' <= c && c <= 'z' || 'A' <= c && c <= 'Z' || c == '_' || c == '$')
        return true;
      if ('0' <= c && c <= '9')
        return !firstChar;
      if (c < 128)
        return false;
      UnicodeCategory ccat = Char.GetUnicodeCategory(c);
      switch (ccat) {
        case UnicodeCategory.UppercaseLetter:
        case UnicodeCategory.LowercaseLetter:
        case UnicodeCategory.TitlecaseLetter:
        case UnicodeCategory.ModifierLetter:
        case UnicodeCategory.OtherLetter:
        case UnicodeCategory.LetterNumber:
          return true;
        case UnicodeCategory.NonSpacingMark:
        case UnicodeCategory.SpacingCombiningMark:
        case UnicodeCategory.DecimalDigitNumber:
        case UnicodeCategory.ConnectorPunctuation:
        case UnicodeCategory.Format:
          return !firstChar;
        default:
          return false;
      }
    }

    /// <summary>
    /// Skips over any blanks and then returns a string consisting of any characters that appear before the end of the current line.
    /// Leaves this.fragmentIndex pointing to the start of the next line. Updates this.startOfCurrentLine to be the same as this.fragmentIndex.
    /// </summary>
    private string ScanMessage()
      //^ ensures this.startOfCurrentLine == this.fragmentIndex;
    {
      this.SkipBlanks();
      this.errorIndex = this.fragmentIndex;
      int messageOffset = this.fragmentIndex-this.startOfCurrentLine;
      int length = 0;
      char c = this.GetCurrentChar();
      for (; ; )
        //^ invariant this.fragmentIndex-this.startOfCurrentLine == messageOffset+length;
        //^ invariant this.fragmentIndex == this.fragmentLength ==> c == (char)0;
      {
        if (c == (char)0 && this.fragmentIndex == this.fragmentLength) {
          //End of document
          break; 
        }
        if (Scanner.IsEndOfLine(c)) break;
        this.fragmentIndex++;
        length++;
        c = this.GetCurrentChar();
      }
      //^ assert this.fragmentIndex == this.startOfCurrentLine+messageOffset+length;
      //^ assert this.fragmentIndex < this.buffer.Length; 
      string result = new string(this.buffer, this.startOfCurrentLine+messageOffset, length);
      if (Scanner.IsEndOfLine(c)) {
        this.fragmentIndex++;
        if (c == '\r' && this.GetCurrentChar() == '\n') {
          this.fragmentIndex++;
        }
      }
      this.startOfCurrentLine = this.fragmentIndex;
      return result;
    }

    /// <summary>
    /// Starting with the current character known to be a digit, scans over characters until reaching a non digit, accumulating the values
    /// of the digits into a 32-bit integer. If overflow occurs, an error is reported.
    /// </summary>
    private int ScanNumber()
      //^ requires this.fragmentIndex < this.fragmentLength;
      //^ requires Scanner.IsDigit(this.buffer[this.fragmentIndex]);
    {
      long result = 0;
      this.errorIndex = this.fragmentIndex;
      char c = this.GetCurrentChar();
      while (Scanner.IsDigit(c)) 
        // ^ invariant this.fragmentIndex < this.fragmentLength;
      {
        //^ assume this.fragmentIndex < this.fragmentLength;
        int d = c - '0';
        if (result < int.MaxValue)
          result = result*10 + d;
        this.fragmentIndex++;
        c = this.GetCurrentChar();
      }
      if (result > int.MaxValue) {
        //^ assume this.errorIndex < this.fragmentIndex;
        this.HandleError(Error.IntOverflow);
        result = int.MaxValue;
      }
      return (int)result;
    }

    /// <summary>
    /// Starting with a current character scans over characters until reaching the given terminating character (for example '"' or '>').
    /// If the end of the current line is reached before the terminating character is encoutered, an error is reported.
    /// Returns a string consisting of the characters in between the current character and the terminating character.
    /// </summary>
    private string ScanString(char terminator) 
      //^ requires terminator != (char)0;
    {
      int offsetToStartOfString = ++this.fragmentIndex - this.startOfCurrentLine;
      for (; ; )
        //^ invariant offsetToStartOfString+this.startOfCurrentLine <= this.fragmentIndex;
      {
        char c = this.GetCurrentChar();
        if (c == (char)0) break; //End of document
        if (Scanner.IsEndOfLine(c)) {
          this.errorIndex = offsetToStartOfString-1 + this.startOfCurrentLine;
          this.HandleError(Error.MissingPPFile);
          break;
        }
        if (c == terminator) break;
        this.fragmentIndex++;
      }
      int startOfString = offsetToStartOfString+this.startOfCurrentLine;
      return new string(this.buffer, startOfString, this.fragmentIndex-startOfString);
    }

    /// <summary>
    /// If the current character (this.buffer[this.fragmentIndex]) is not a blank space, do nothing.
    /// If it is a blank space skip it and repeat until the current character is not a blank space.
    /// Embedded null characters are treated as if they were blank spaces.
    /// </summary>
    private char SkipBlanks() 
      //^ ensures result == (char)0 ==> this.fragmentIndex == this.fragmentLength;
      //^ ensures result != (char)0 ==> !Scanner.IsBlankSpace(result) && this.fragmentIndex >= 0 && result == this.buffer[this.fragmentIndex] && this.fragmentIndex < this.fragmentLength;
    {
      for (;;){
        char c = this.GetCurrentChar();
        if (c == (char)0 && this.fragmentIndex == this.fragmentLength) return c; //Reached the end of the document
        if (!Scanner.IsBlankSpace(c) && c != (char)0) return c;
        this.fragmentIndex++;
      }
    }

    /// <summary>
    /// Skips over any blanks, then over an optional single line comment and then over the end of line, leaving this.fragmentIndex and
    /// this.startOfCurrentLine both pointing to the first character of the next line. If the characters following the blanks do not
    /// form a legal single-line comment, an error is reported.
    /// </summary>
    private void SkipPastBlanksCommentAndNewLine()
      //^ requires this.fragmentIndex >= 0;
      //^ requires this.fragmentIndex <= this.fragmentLength;
      //^ ensures this.startOfCurrentLine == this.fragmentIndex;
    {
      this.SkipBlanks();
      char c = this.GetCurrentChar();
      if (c == '/') {
        this.errorIndex = this.fragmentIndex++;
        c = this.GetCurrentChar();
        if (c != '/') {
          this.HandleError(Error.EndOfPPLineExpected);
        }
      }
      this.SkipRestOfDirective();
    }

    /// <summary>
    /// Skips over characters until the start of the next line is encountered, leaving this.fragmentIndex and
    /// this.startOfCurrentLine both pointing to the first character of the next line.
    /// </summary>
    private void SkipRestOfDirective()
      //^ ensures this.startOfCurrentLine == this.fragmentIndex;
    {
      bool lastCharWasBackslash = false;
      for (; ; ) {
        char c = this.GetCurrentChar();
        if (this.fragmentIndex == this.fragmentLength) {
          break; //End of document
        }
        this.fragmentIndex++;
        if (c == '\\') {
          lastCharWasBackslash = true;
          continue;
        }
        if (Scanner.IsEndOfLine(c)) {
          if (c == '\r' && this.GetCurrentChar() == '\n') this.fragmentIndex++;
          if (!lastCharWasBackslash) break;
        }
        lastCharWasBackslash = false;
      }
      this.startOfCurrentLine = this.fragmentIndex;
    }

    /// <summary>
    /// Skips over characters until the start of an end of line sequence or a single-line comment is encountered.
    /// Leaves this.fragmentIndex pointing to the first character of the end of line sequence or single-line comment.
    /// </summary>
    private void SkipToCommentOrNewLine() {
      for (; ; ) {
        if (this.fragmentIndex == this.fragmentLength) return; //Reached the end of the document
        char c = this.GetCurrentChar();
        if (Scanner.IsEndOfLine(c)) return;
        this.fragmentIndex++;
        if (c == '/' && this.GetCurrentChar() == '/') {
          this.fragmentIndex--;
          return;
        }
      }
    }

    /// <summary>
    /// Skips over characters until the end of the current fragment is reached or until a # that is the first
    /// non blank character on a new has been encountered. Leaves this.fragmentIndex pointing to either the # character
    /// or the end of the fragment (== this.fragmentLength).
    /// </summary>
    /// <param name="onlyWhiteSpaceSeenSoFar">If the initial value of this parameter is true, then it means that only blank
    /// characters were encountered in the last line of the previous fragment. Likewise upon exit.</param>
    private void SkipUntilEligibleHash(ref bool onlyWhiteSpaceSeenSoFar) {
      for (; ; ) {
        if (this.fragmentIndex == this.fragmentLength) {
          if (this.fragmentLength < this.buffer.Length-1) {
            //end of last fragment in document, or still have to read in the first fragment
            this.startOfCurrentLine = this.fragmentLength; //Treat end of document as end of line.
          }
          return; //end of fragment
        }
        char c = this.buffer[this.fragmentIndex];
        //TODO: keep track of multi line comments
        if (c == '#' && onlyWhiteSpaceSeenSoFar) return;
        this.fragmentIndex++;
        if (Scanner.IsBlankSpace(c)) continue;
        onlyWhiteSpaceSeenSoFar = false;
        if (Scanner.IsEndOfLine(c)){
          if (c == '\r' && this.buffer[this.fragmentIndex] == '\n') this.fragmentIndex++;
          this.startOfCurrentLine = this.fragmentIndex;
          onlyWhiteSpaceSeenSoFar = true;
        }
      }
    }

  }

  /// <summary>
  /// A preprocessor directive, such as a #define.
  /// </summary>
  public abstract class Directive : SourceItem {

    /// <summary>
    /// Initializes the source location of a preprocessor directive.
    /// </summary>
    /// <param name="sourceLocation">The location in the source document where the preprocessor directive appears.</param>
    internal Directive(ISourceLocation sourceLocation)
      : base(sourceLocation)
    {
    }

    /// <summary>
    /// Makes a shallow copy of the directive by updating its source location to come from the given document,
    /// but otherwise keeping all of the information the same.
    /// </summary>
    internal abstract Directive MakeShallowCopy(ISourceDocument newDocumentToPreprocess);
    //^ requires newDocumentToPreprocess.IsUpdatedVersionOf(this.SourceLocation.SourceDocument);
  }

  /// <summary>
  /// An object that models a preprocessor #define directive.
  /// </summary>
  public sealed class DefineDirective : Directive {

    /// <summary>
    /// Allocates an object that models a preprocessor #define directive.
    /// </summary>
    /// <param name="definedSymbol">The preprocessor symbol that is defined by this directive.</param>
    /// <param name="sourceLocation">The location in the source document where the #define directive appears.</param>
    internal DefineDirective(PreprocessorSymbol definedSymbol, ISourceLocation sourceLocation)
      : base(sourceLocation)
    {
      this.definedSymbol = definedSymbol;
    }

    /// <summary>
    /// The preprocessor symbol that is defined by this directive.
    /// </summary>
    public PreprocessorSymbol DefinedSymbol{
      get{ return this.definedSymbol; }
    }
    readonly PreprocessorSymbol definedSymbol;

    /// <summary>
    /// Makes a shallow copy of the directive by updating its source location to come from the given document,
    /// but otherwise keeping all of the information the same.
    /// </summary>
    internal override Directive MakeShallowCopy(ISourceDocument newDocumentToPreprocess)
      //^^ requires newDocumentToPreprocess.IsUpdatedVersionOf(this.SourceLocation.SourceDocument);
    {
      ISourceLocation sloc = this.SourceLocation;
      //^ assume newDocumentToPreprocess.IsUpdatedVersionOf(sloc.SourceDocument); //follows from the precondition
      //unsatisfied precondition: requires this.IsUpdatedVersionOf(sourceLocationInPreviousVersionOfDocument.SourceDocument);
      return new DefineDirective(this.DefinedSymbol, newDocumentToPreprocess.GetCorrespondingSourceLocation(sloc));
    }
  }

  /// <summary>
  /// An object that models an #elif part of an #if-#elif-#else-#endif directive.
  /// </summary>
  public sealed class ElifPart : SourceItem {

    /// <summary>
    /// Allocates an object that models an #elif part of an #if-#elif-#else-#endif directive.
    /// </summary>
    /// <param name="condition">An expression that evaluates to either defined or undefined.</param>
    /// <param name="sourceLocation">The location in the source document where the #elif part appears.</param>
    internal ElifPart(PreprocessorExpression condition, ISourceLocation sourceLocation)
      : base(sourceLocation) 
    {
      this.condition = condition;
    }

    /// <summary>
    /// An expression that evaluates to either defined or undefined.
    /// </summary>
    public PreprocessorExpression Condition {
      get { return this.condition; }
    }
    readonly PreprocessorExpression condition;

  }

  /// <summary>
  /// An object that models the #else part of an #if-#elif-#else-#endif directive.
  /// </summary>
  public sealed class ElsePart : SourceItem {

    /// <summary>
    /// Allocates an object that models the #else part of an #if-#elif-#else-#endif directive.
    /// </summary>
    /// <param name="sourceLocation">The location in the source document where the #else part appears.</param>
    internal ElsePart(ISourceLocation sourceLocation)
      : base(sourceLocation) {
    }

  }

  /// <summary>
  /// An object that models the #end part of an #if-#elif-#else-#endif directive.
  /// </summary>
  public sealed class EndifPart : SourceItem {

    /// <summary>
    /// Allocates an object that models the #end part of an #if-#elif-#else-#endif directive.
    /// </summary>
    /// <param name="sourceLocation">The location in the source document where the #end part appears.</param>
    internal EndifPart(ISourceLocation sourceLocation)
      : base(sourceLocation) {
    }

  }

  /// <summary>
  /// An object that models the #endregion part of a #region-#endregion directive.
  /// </summary>
  public sealed class EndregionPart : SourceItem {

    /// <summary>
    /// Allocates an object that models the #endregion part of a #region-#endregion directive.
    /// </summary>
    /// <param name="label">A string to associate with the region. This may be different from the string associated with the #region part.</param>
    /// <param name="sourceLocation">The location in the source document where the #endregion part appears.</param>
    internal EndregionPart(string label, ISourceLocation sourceLocation)
      : base(sourceLocation) 
    {
      this.label = label;
    }
    
    /// <summary>
    /// A string to associate with the region. This may be different from the string associated with the #region part.
    /// </summary>
    public string Label {
      get { return this.label; }
    }
    readonly string label;
  }

  /// <summary>
  /// An object that models an #error directive.
  /// </summary>
  public sealed class ErrorDirective : Directive {

    /// <summary>
    /// Allocates an object that models an #error directive.
    /// </summary>
    /// <param name="message">The text of the error message to generate as result of processing this directive.</param>
    /// <param name="sourceLocation">The location in the source document where the #error directive appears.</param>
    internal ErrorDirective(string message, ISourceLocation sourceLocation)
      : base(sourceLocation) 
    {
      this.message = message;
    }

    /// <summary>
    /// The text of the error message to generate as result of processing this directive.
    /// </summary>
    public string Message {
      get { return this.message; }
    }
    readonly string message;


    internal override Directive MakeShallowCopy(ISourceDocument newDocumentToPreprocess) 
      //^^ requires newDocumentToPreprocess.IsUpdatedVersionOf(this.SourceLocation.SourceDocument);
    {
      ISourceLocation sloc = this.SourceLocation;
      //^ assume newDocumentToPreprocess.IsUpdatedVersionOf(sloc.SourceDocument); //follows from the precondition
      //unsatisfied precondition: requires this.IsUpdatedVersionOf(sourceLocationInPreviousVersionOfDocument.SourceDocument);
      return new ErrorDirective(this.Message, newDocumentToPreprocess.GetCorrespondingSourceLocation(sloc));
    }
  }

  /// <summary>
  /// An object that models an #if-#elif-#else-#endif directive.
  /// </summary>
  public sealed class IfDirective : Directive {

    /// <summary>
    /// Allocates an object that models an #if-#elif-#else-#endif directive.
    /// </summary>
    /// <param name="condition">An expression that evaluates to either defined or undefined.</param>
    /// <param name="sourceLocation">The location in the source document where the #if-#elif-#else-#endif directive appears.</param>
    internal IfDirective(PreprocessorExpression condition, ISourceLocation sourceLocation) 
      : base (sourceLocation)
    {
      this.condition = condition;
    }

    /// <summary>
    /// An expression that evaluates to either defined or undefined. If defined then the source text starting with the first line
    /// following the #if upto the last line not containing a matching #elif, #else or #endif is included in the preprocessor output.
    /// </summary>
    public PreprocessorExpression Condition {
      get { return this.condition; }
    }
    readonly PreprocessorExpression condition;

    /// <summary>
    /// A sequence of #elif parts that match the #if.
    /// </summary>
    public IEnumerable<ElifPart> Elifs {
      get { return this.elifs.AsReadOnly(); }
    }
    /// <summary>
    /// A list of #elif parts that match the #if.
    /// </summary>
    internal readonly List<ElifPart> elifs = new List<ElifPart>();

    /// <summary>
    /// An #else parts that matches the #if. May be null if no #else was specified.
    /// </summary>
    public ElsePart/*?*/ Else {
      get { return this.@else; }
    }
    /// <summary>
    /// An #else part that matches the #if.
    /// </summary>
    internal ElsePart/*?*/ @else;

    /// <summary>
    /// An #endif part that matches the #if. Can be null if the #endif is missing in the source.
    /// </summary>
    public EndifPart/*?*/ Endif {
      get { 
        return this.endif;  
      }
    }
    /// <summary>
    /// An #endif part that matches the #if. Can be null if the #endif is missing in the source.
    /// </summary>
    internal EndifPart/*?*/ endif;

    internal override Directive MakeShallowCopy(ISourceDocument newDocumentToPreprocess)
      //^^ requires newDocumentToPreprocess.IsUpdatedVersionOf(this.SourceLocation.SourceDocument);
    {
      ISourceLocation sloc = this.SourceLocation;
      //^ assume newDocumentToPreprocess.IsUpdatedVersionOf(sloc.SourceDocument); //follows from the precondition
      //unsatisfied precondition: requires this.IsUpdatedVersionOf(sourceLocationInPreviousVersionOfDocument.SourceDocument);
      IfDirective result = new IfDirective(this.Condition, newDocumentToPreprocess.GetCorrespondingSourceLocation(sloc));
      foreach (ElifPart elifPart in this.Elifs)
        result.elifs.Add(new ElifPart(elifPart.Condition, newDocumentToPreprocess.GetCorrespondingSourceLocation(elifPart.SourceLocation)));
      if (this.Else != null)
        result.@else = new ElsePart(newDocumentToPreprocess.GetCorrespondingSourceLocation(this.Else.SourceLocation));
      if (this.Endif != null)
        result.endif = new EndifPart(newDocumentToPreprocess.GetCorrespondingSourceLocation(this.Endif.SourceLocation));
      return result;
    }
  }

  public sealed class IncludeDirective : Directive {

    internal IncludeDirective(string/*?*/ pathToInclude, ISourceLocation sourceLocation) 
      : base(sourceLocation) {
      this.pathToInclude = pathToInclude;
    }

    public string/*?*/ PathToInclude {
      get { return this.pathToInclude; }
    }
    string/*?*/ pathToInclude;

    internal override Directive MakeShallowCopy(ISourceDocument newDocumentToPreprocess)
      //^^ requires newDocumentToPreprocess.IsUpdatedVersionOf(this.SourceLocation.SourceDocument);
    {
      ISourceLocation sloc = this.SourceLocation;
      //^ assume newDocumentToPreprocess.IsUpdatedVersionOf(sloc.SourceDocument); //follows from the precondition
      //unsatisfied precondition: requires this.IsUpdatedVersionOf(sourceLocationInPreviousVersionOfDocument.SourceDocument);
      return new IncludeDirective(this.PathToInclude, newDocumentToPreprocess.GetCorrespondingSourceLocation(sloc));
    }
  }

  public sealed class LineDirective : Directive {

    internal LineDirective(int? lineNumber, string/*?*/ documentName, ISourceLocation sourceLocation)
      : base(sourceLocation) {
      this.lineNumber = lineNumber;
      this.documentName = documentName;
    }

    public int? LineNumber {
      get { return this.lineNumber; }
    }
    readonly int? lineNumber;

    public string/*?*/ DocumentName {
      get { return this.documentName; }
    }
    readonly string/*?*/ documentName;


    internal override Directive MakeShallowCopy(ISourceDocument newDocumentToPreprocess)
      //^^ requires newDocumentToPreprocess.IsUpdatedVersionOf(this.SourceLocation.SourceDocument);
    {
      ISourceLocation sloc = this.SourceLocation;
      //^ assume newDocumentToPreprocess.IsUpdatedVersionOf(sloc.SourceDocument); //follows from the precondition
      //unsatisfied precondition: requires this.IsUpdatedVersionOf(sourceLocationInPreviousVersionOfDocument.SourceDocument);
      return new LineDirective(this.LineNumber, this.DocumentName, newDocumentToPreprocess.GetCorrespondingSourceLocation(sloc));
    }
  }

  public sealed class PragmaWarningDirective : Directive {

    internal PragmaWarningDirective(bool disabled, IEnumerable<WarningNumber> warnings, ISourceLocation sourceLocation)
      : base(sourceLocation) {
      this.disabled = disabled;
      this.warnings = warnings;
    }

    public bool Disabled {
      get { return this.disabled; }
    }
    readonly bool disabled;

    public IEnumerable<WarningNumber> Warnings {
      get { return this.warnings; }
    }
    readonly IEnumerable<WarningNumber> warnings;


    internal override Directive MakeShallowCopy(ISourceDocument newDocumentToPreprocess)
      //^^ requires newDocumentToPreprocess.IsUpdatedVersionOf(this.SourceLocation.SourceDocument);
    {
      List<WarningNumber> newWarnings = new List<WarningNumber>(this.Warnings);
      for (int i = 0, n = newWarnings.Count; i < n; i++) {
        newWarnings[i] = new WarningNumber(newWarnings[i].Value, newDocumentToPreprocess.GetCorrespondingSourceLocation(newWarnings[i].SourceLocation));
      }
      return new PragmaWarningDirective(this.Disabled, newWarnings, newDocumentToPreprocess.GetCorrespondingSourceLocation(this.SourceLocation));
    }
  }

  public sealed class RegionDirective : Directive {

    internal RegionDirective(string label, ISourceLocation sourceLocation)
      : base(sourceLocation) 
    {
      this.label = label;
    }

    public EndregionPart/*?*/ Endregion {
      get {
        return this.endregion;
      }
    }
    internal EndregionPart/*?*/ endregion;

    public string Label {
      get { return this.label; }
    }
    readonly string label;

    internal override Directive MakeShallowCopy(ISourceDocument newDocumentToPreprocess)
      //^^ requires newDocumentToPreprocess.IsUpdatedVersionOf(this.SourceLocation.SourceDocument);
    {
      ISourceLocation sloc = this.SourceLocation;
      //^ assume newDocumentToPreprocess.IsUpdatedVersionOf(sloc.SourceDocument); //follows from the precondition
      RegionDirective result = new RegionDirective(this.Label, newDocumentToPreprocess.GetCorrespondingSourceLocation(sloc));
      if (this.Endregion != null)
        result.endregion = new EndregionPart(this.Endregion.Label, newDocumentToPreprocess.GetCorrespondingSourceLocation(this.Endregion.SourceLocation));
      return result;
    }
  }

  public sealed class UndefDirective : Directive {

    internal UndefDirective(PreprocessorSymbol definedSymbol, ISourceLocation sourceLocation)
      : base(sourceLocation) 
      // ^ requires sourceLocation.Contains(definedSymbol.SourceLocation);
    {
      this.definedSymbol = definedSymbol;
    }

    public PreprocessorSymbol DefinedSymbol {
      get { return this.definedSymbol; }
    }
    readonly PreprocessorSymbol definedSymbol;


    internal override Directive MakeShallowCopy(ISourceDocument newDocumentToPreprocess)
      //^^ requires newDocumentToPreprocess.IsUpdatedVersionOf(this.SourceLocation.SourceDocument);
    {
      ISourceLocation sloc = this.SourceLocation;
      //^ assume newDocumentToPreprocess.IsUpdatedVersionOf(sloc.SourceDocument); //follows from the precondition
      ISourceLocation dsloc = this.DefinedSymbol.SourceLocation;
      //^ assume sloc.Contains(dsloc); //follows from the preconditon of the constructor
      PreprocessorSymbol newSymbol = new PreprocessorSymbol(this.DefinedSymbol.Name, newDocumentToPreprocess.GetCorrespondingSourceLocation(dsloc));
      return new UndefDirective(newSymbol, newDocumentToPreprocess.GetCorrespondingSourceLocation(sloc));
    }
  }

  public sealed class WarningDirective : Directive {

    internal WarningDirective(string message, ISourceLocation sourceLocation)
      : base(sourceLocation) {
      this.message = message;
    }

    public string Message {
      get { return this.message; }
    }
    readonly string message;


    internal override Directive MakeShallowCopy(ISourceDocument newDocumentToPreprocess)
      //^^ requires newDocumentToPreprocess.IsUpdatedVersionOf(this.SourceLocation.SourceDocument);
    {
      ISourceLocation sloc = this.SourceLocation;
      //^ assume newDocumentToPreprocess.IsUpdatedVersionOf(sloc.SourceDocument); //follows from the precondition
      return new WarningDirective(this.Message, newDocumentToPreprocess.GetCorrespondingSourceLocation(sloc));
    }
  }

  public abstract class PreprocessorExpression : SourceItem {

    internal PreprocessorExpression(ISourceLocation sourceLocation)
      : base(sourceLocation)
    {
    }

    public abstract bool IsDefined(IDictionary<string,string> definedSymbols);

  }

  internal class PreprocessorSourceLocation : IPrimarySourceLocation {
    IPrimarySourceLocation slFromDocument;
    Preprocessor preprocessor;

    internal PreprocessorSourceLocation(IPrimarySourceLocation slFromDocument, Preprocessor preprocessor) {
      this.slFromDocument = slFromDocument;
      this.preprocessor = preprocessor;
    }

    #region IPrimarySourceLocation Members

    public int EndColumn {
      get { return this.slFromDocument.EndColumn; }
    }

    public int EndLine {
      get { return this.slFromDocument.EndLine; }
    }

    public IPrimarySourceDocument PrimarySourceDocument {
      get { return this.slFromDocument.PrimarySourceDocument; }
    }

    public int StartColumn {
      get { return this.slFromDocument.StartColumn; }
    }

    public int StartLine {
      get { return this.slFromDocument.StartLine; }
    }

    #endregion

    #region ISourceLocation Members

    public bool Contains(ISourceLocation location) {
      return this.slFromDocument.Contains(location);
    }

    public int CopyTo(int offset, char[] destination, int destinationOffset, int length) {
      return this.preprocessor.CopyTo(this.StartIndex+offset, destination, destinationOffset, length, this.slFromDocument);
    }

    public int EndIndex {
      get { return this.slFromDocument.EndIndex; }
    }

    public int Length {
      get { return this.slFromDocument.Length; }
    }

    public ISourceDocument SourceDocument {
      get { return this.slFromDocument.SourceDocument; }
    }

    public string Source {
      get { return this.preprocessor.GetSource(this.slFromDocument); }
    }

    public int StartIndex {
      get { return this.slFromDocument.StartIndex; }
    }

    #endregion

    #region ILocation Members

    public IDocument Document {
      get { return ((ILocation)this.slFromDocument).Document; }
    }

    #endregion
  }

  public abstract class BinaryExpression : PreprocessorExpression {

    internal BinaryExpression(PreprocessorExpression leftOperand, PreprocessorExpression rightOperand) 
      : base(leftOperand.SourceLocation.SourceDocument.GetSourceLocation(leftOperand.SourceLocation.StartIndex, 
        rightOperand.SourceLocation.StartIndex + rightOperand.SourceLocation.Length - leftOperand.SourceLocation.StartIndex))
    {
      this.leftOperand = leftOperand;
      this.rightOperand = rightOperand;
    }

    public PreprocessorExpression LeftOperand {
      get { return this.leftOperand; }
    }
    readonly PreprocessorExpression leftOperand;

    public PreprocessorExpression RightOperand {
      get { return this.rightOperand; }
    }
    readonly PreprocessorExpression rightOperand;
  }

  public sealed class AndExpression : BinaryExpression {

    internal AndExpression(PreprocessorExpression leftOperand, PreprocessorExpression rightOperand)
      : base(leftOperand, rightOperand) {
    }

    public override bool IsDefined(IDictionary<string,string> definedSymbols) {
      return this.LeftOperand.IsDefined(definedSymbols) && this.RightOperand.IsDefined(definedSymbols);
    }

  }

  public sealed class EqualsExpression : BinaryExpression {

    internal EqualsExpression(PreprocessorExpression leftOperand, PreprocessorExpression rightOperand)
      : base(leftOperand, rightOperand) {
    }

    public override bool IsDefined(IDictionary<string,string> definedSymbols) {
      return this.LeftOperand.IsDefined(definedSymbols) == this.RightOperand.IsDefined(definedSymbols);
    }

  }

  public sealed class MissingExpression : PreprocessorExpression {

    public MissingExpression(ISourceLocation sourceLocation)
      : base(sourceLocation){
    }

    public override bool IsDefined(IDictionary<string,string> definedSymbols) {
      return false;
    }

  }

  public sealed class NotEqualsExpression : BinaryExpression {

    internal NotEqualsExpression(PreprocessorExpression leftOperand, PreprocessorExpression rightOperand)
      : base(leftOperand, rightOperand) {
    }

    public override bool IsDefined(IDictionary<string,string> definedSymbols) {
      return this.LeftOperand.IsDefined(definedSymbols) != this.RightOperand.IsDefined(definedSymbols);
    }

  }

  public sealed class NotExpression : PreprocessorExpression {

    internal NotExpression(PreprocessorExpression operand, ISourceLocation sourceLocation) 
      : base(sourceLocation)
    {
      this.operand = operand;
    }

    public PreprocessorExpression Operand {
      get { return this.operand; }
    }
    private readonly PreprocessorExpression operand;

    public override bool IsDefined(IDictionary<string,string> definedSymbols) {
      return !this.Operand.IsDefined(definedSymbols);
    }

  }

  public sealed class OrExpression : BinaryExpression {

    internal OrExpression(PreprocessorExpression leftOperand, PreprocessorExpression rightOperand)
      : base(leftOperand, rightOperand) {
    }

    public override bool IsDefined(IDictionary<string,string> definedSymbols) {
      return this.LeftOperand.IsDefined(definedSymbols) || this.RightOperand.IsDefined(definedSymbols);
    }

  }

  public sealed class PreprocessorSymbol : PreprocessorExpression {

    internal PreprocessorSymbol(string name, ISourceLocation sourceLocation) 
      : base(sourceLocation)
    {
      this.name = name;
    }

    public string Name {
      get { return this.name; }
    }
    private readonly string name;

    public override bool IsDefined(IDictionary<string,string> definedSymbols) {
      return definedSymbols.ContainsKey(this.Name);
    }

  }

  public sealed class WarningNumber : SourceItem {

    internal WarningNumber(int value, ISourceLocation sourceLocation) 
      : base(sourceLocation)
    {
      this.value = value;
    }

    public int Value {
      get { return this.value; }
    }
    readonly int value;

  }

  /// <summary>
  /// An object that records the preprocessor directives that were encountered when preprocessing a source document,
  /// as well as the source locations that were included or excluded by the preprocessor.
  /// </summary>
  public sealed class PreprocessorInformation {

    internal PreprocessorInformation(IPrimarySourceDocument documentToPreprocess, List<IErrorMessage> errors) {
      this.errors = errors;
      this.sourceDocument = documentToPreprocess;
    }

    internal PreprocessorInformation(IPrimarySourceDocument newDocumentToPreprocess, PreprocessorInformation template) {
      this.sourceDocument = newDocumentToPreprocess;
      SourceDocumentWithInclusion/*?*/ sourceOfInclusion = null;
      List<Directive> directives = new List<Directive>(template.Directives);
      List<IErrorMessage> errors = new List<IErrorMessage>(template.errors);
      List<ISourceLocation> excludedLocations = new List<ISourceLocation>(template.ExcludedLocations);
      List<ISourceLocation> includedLocations = new List<ISourceLocation>(template.IncludedLocations);
      for (int i = 0, n = directives.Count; i < n; i++) {
        //^ assume newDocumentToPreprocess.IsUpdatedVersionOf(directives[i].SourceLocation.SourceDocument);
        directives[i] = directives[i].MakeShallowCopy(newDocumentToPreprocess);
      }
      for (int i = 0, n = errors.Count; i < n; i++) {
        ISourceErrorMessage/*?*/ sourceError = errors[i] as ISourceErrorMessage;
        //^ assume sourceError != null;
        //^ assume newDocumentToPreprocess.IsUpdatedVersionOf(sourceError.SourceLocation.SourceDocument);
        errors[i] = sourceError.MakeShallowCopy(newDocumentToPreprocess);
      }
      for (int i = 0, n = excludedLocations.Count; i < n; i++) {
        ISourceLocation excludedLocation = excludedLocations[i];
        SourceDocumentWithInclusion/*?*/ idoc = excludedLocation.SourceDocument as SourceDocumentWithInclusion;
        if (idoc != null) {
          if (sourceOfInclusion == null || !idoc.IsUpdatedVersionOf(sourceOfInclusion))
            sourceOfInclusion = new SourceDocumentWithInclusion(newDocumentToPreprocess, idoc.OriginalLineNumber, idoc.OriginalDocumentName, idoc.StartingPositionOfIncludedRegion);
          excludedLocations[i] = sourceOfInclusion.GetCorrespondingSourceLocation(excludedLocation);
        } else {
          //^ assume newDocumentToPreprocess.IsUpdatedVersionOf(excludedLocation.SourceDocument);
          excludedLocations[i] =  newDocumentToPreprocess.GetCorrespondingSourceLocation(excludedLocation);
        }
      }
      for (int i = 0, n = includedLocations.Count; i < n; i++) {
        ISourceLocation includedLocation = includedLocations[i];
        SourceDocumentWithInclusion/*?*/ idoc = includedLocation.SourceDocument as SourceDocumentWithInclusion;
        if (idoc != null) {
          if (sourceOfInclusion == null || !idoc.IsUpdatedVersionOf(sourceOfInclusion))
            sourceOfInclusion = new SourceDocumentWithInclusion(newDocumentToPreprocess, idoc.OriginalLineNumber, idoc.OriginalDocumentName, idoc.StartingPositionOfIncludedRegion);
          includedLocations[i] = sourceOfInclusion.GetCorrespondingSourceLocation(includedLocation);
        } else {
          //^ assume newDocumentToPreprocess.IsUpdatedVersionOf(includedLocation.SourceDocument);
          includedLocations[i] =  newDocumentToPreprocess.GetCorrespondingSourceLocation(includedLocation);
        }
      }
      this.directives = directives;
      this.errors = errors;
      this.excludedLocations = excludedLocations;
      this.includedLocations = includedLocations;
    }

    internal void AddElif(ElifPart elif) {
      for (int i = this.directives.Count; i > 0; i--) {
        IfDirective/*?*/ ifDirective = this.directives[i-1] as IfDirective;
        if (ifDirective == null) continue;
        ifDirective.elifs.Add(elif);
        return;
      }
    }

    internal void AddElse(ElsePart @else) {
      for (int i = this.directives.Count; i > 0; i--) {
        IfDirective/*?*/ ifDirective = this.directives[i-1] as IfDirective;
        if (ifDirective == null) continue;
        ifDirective.@else = @else;
        return;
      }
    }

    internal void AddEndif(EndifPart endif) {
      for (int i = this.directives.Count; i > 0; i--) {
        IfDirective/*?*/ ifDirective = this.directives[i-1] as IfDirective;
        if (ifDirective == null) continue;
        ifDirective.endif = endif;
        return;
      }
    }

    internal void AddEndregion(EndregionPart endregion) {
      for (int i = this.directives.Count; i > 0; i--) {
        RegionDirective/*?*/ regionDirective = this.directives[i-1] as RegionDirective;
        if (regionDirective == null) continue;
        regionDirective.endregion = endregion;
        return;
      }
    }

    public IEnumerable<Directive> Directives {
      get { 
        return this.directives.AsReadOnly(); 
      }
    }
    readonly internal List<Directive> directives = new List<Directive>();

    public IPrimarySourceDocument SourceDocument {
      get { return this.sourceDocument; }
    }
    readonly IPrimarySourceDocument sourceDocument;

    readonly internal List<IErrorMessage> errors;

    public IEnumerable<ISourceLocation> ExcludedLocations {
      get { 
        return this.excludedLocations.AsReadOnly(); 
      }
    }
    readonly internal List<ISourceLocation> excludedLocations = new List<ISourceLocation>();

    public IEnumerable<ISourceLocation> IncludedLocations {
      get { 
        return this.includedLocations.AsReadOnly(); 
      }
    }
    readonly internal List<ISourceLocation> includedLocations = new List<ISourceLocation>();


    //TODO:
    //method to check if symbol is defined at a source position (of the preprocessed document)
    //method to check if warning is enabled at a source position
    //method to get an updated OM, given some edit to the original source document
  }

}
