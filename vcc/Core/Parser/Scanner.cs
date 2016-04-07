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
//^ using Microsoft.Contracts;

namespace Microsoft.Research.Vcc.Parsing {

  public sealed class Scanner {
    /// <summary>The character value of the last scanned character literal token.</summary>
    internal int charLiteralValue;

    /// <summary>The index of the first character beyond the last scanned token.</summary>
    private int endPos; //^ invariant startPos <= endPos && endPos <= charsInBuffer;

    /// <summary>The index of sourceChars[0] in this.sourceLocation. Add this to startPos to arrive at the true starting position of the current token.</summary>
    private int offset; //^ invariant 0 <= offset && 0 <= offset+charsInBuffer && offset+charsInBuffer <= sourceLocation.Length; 

    /// <summary>The number of characters in the current document buffer being scanned. this.buffer[this.charsInBuffer] always == 0.</summary>
    private int charsInBuffer; //^ invariant 0 <= charsInBuffer && charsInBuffer < buffer.Length && buffer[charsInBuffer] == (char)0;

    /// <summary>True if the last token scanned was separated from the preceding token by whitespace that includes a line break.</summary>
    public bool TokenIsFirstAfterLineBreak { 
      get { return this.tokenIsFirstAfterLineBreak; } 
    }
    private bool tokenIsFirstAfterLineBreak;

    /// <summary>A linked list of keywords that start with "_".</summary>
    private static readonly Keyword ExtendedKeywords = Keyword.InitExtendedKeywords();

    /// <summary>A linked list of keywords that start with "__".</summary>
    private static readonly Keyword MicrosoftKeywords = Keyword.InitMicrosoftKeywords();

    /// <summary>A linked list of keywords that start with "\".</summary>
    private static readonly Keyword ExtendedVccKeywords = Keyword.InitExtendedVccKeywords();

    /// <summary>
    /// Used to build the unescaped contents of an identifier when the identifier contains escape sequences. An instance variable because multiple methods are involved.
    /// </summary>
    private readonly StringBuilder identifierBuilder = new StringBuilder(128);

    /// <summary>Records the extent of the identifier source that has already been appended to the identifier builder.</summary>
    private int idLastPosOnBuilder; //^ invariant 0 <= idLastPosOnBuilder && idLastPosOnBuilder <= this.endPos;

    /// <summary>True if the scanner should not return tokens corresponding to comments.</summary>
    private bool ignoreComments = true;

    /// <summary>True if _ should be treated as a keyword.</summary>
    private bool underscoreIsKeyword = false;

    /// <summary>An array of linked lists of keywords, to be indexed with the first character of the keyword.</summary>
    private static readonly Keyword/*?*/[] Keywords = Keyword.InitKeywords();
    // ^ invariant Keywords.Length == 26; //TODO: Boogie crashes on this invariant

    /// <summary>An array of linked list of spec keywords that are allowed at the beginning of spec(...) code</summary>
    private static readonly Keyword/*?*/[] SpecKeywords = Keyword.InitSpecKeywords();

    /// <summary>Keeps track of the end position of the last malformed token. Used to avoid repeating lexical error messages when the parser backtracks.</summary>
    private int lastReportedErrorPos;

    /// <summary>A list to which any scanner errors should be appended if it is not null.</summary>
    private readonly List<IErrorMessage>/*?*/ scannerErrors;

    /// <summary>The characters to scan for tokens.</summary>
    private char[] buffer; 
    //^ invariant 0 < buffer.LongLength+this.offset;
    //^ invariant buffer.LongLength+this.offset <= int.MaxValue;
    //TODO: switch to using char* and an unmanaged memory block. This will get rid of the (unnecessary) index out range check. (First verify code.)

    /// <summary>Keeps track of the source location being scanned.</summary>
    private ISourceLocation sourceLocation;

    /// <summary>The position of the first character forming part of the last scanned token.</summary>
    private int startPos; //^ invariant 0 <= startPos && startPos <= charsInBuffer;

    /// <summary>The contents of the last string literal scanned, with escape sequences already replaced with their corresponding characters.</summary>
    private string/*?*/ unescapedString;

    public Scanner(List<IErrorMessage>/*?*/ scannerErrors, ISourceLocation sourceLocation, bool ignoreComments, bool underscoreIsKeyword) {
      this.scannerErrors = scannerErrors;
      this.sourceLocation = sourceLocation;
      char[] buffer = new char[8192];
      this.charsInBuffer = sourceLocation.CopyTo(0, buffer, 0, buffer.Length-1);
      this.buffer = buffer;
      this.endPos = this.startPos = 0;
      this.offset = 0;
      this.ignoreComments = ignoreComments;
      this.underscoreIsKeyword = underscoreIsKeyword;
    }

    private char GetCurrentChar()
      //^ requires 0 <= this.endPos;
      //^ requires this.endPos <= this.charsInBuffer;
      //^ ensures result != (char)0 ==> this.endPos < this.charsInBuffer;
      //^ ensures old(this.endPos)-old(this.startPos) == this.endPos-this.startPos;
    {
      char c = this.buffer[this.endPos];
      if (c == (char)0 && this.endPos == this.charsInBuffer && this.charsInBuffer > 0) {
        this.GetNextFragment();
        c = this.buffer[this.endPos];
      }
      return c;
    }

    private char GetCurrentCharAndIncrementEndPos() 
      //^ requires 0 <= this.endPos;
      //^ requires this.endPos < this.charsInBuffer;
      //^ ensures result != (char)0 ==> this.endPos <= this.charsInBuffer;
    {
      char c = this.buffer[this.endPos++];
      if (c == (char)0 && this.endPos == this.charsInBuffer) {
        this.GetNextFragment();
        c = this.buffer[this.endPos];
      }
      return c;
    }

    private char GetChar(int index)
      //^ requires 0 <= index;
      //^ requires index <= this.charsInBuffer;
    {
      return this.buffer[index];
    }

    private char PeekAheadBy(int offset)
      //^ requires 0 <= offset;
      //^ requires this.endPos+offset <= this.charsInBuffer;
      //^ requires this.charsInBuffer > 0;
      //^ ensures result != (char)0 ==> this.endPos+offset < this.charsInBuffer;
      //^ ensures result == this.buffer[this.endPos+offset];
    {
      if (this.endPos+offset == this.charsInBuffer)
        this.GetNextFragment();
      return this.buffer[this.endPos+offset];
    }

    private char GetNextCharAndIncrementEndPos()
      //^ requires this.endPos < this.charsInBuffer;
      //^ ensures result != (char)0 ==> this.endPos < this.charsInBuffer;
    {
      char c =  this.buffer[++this.endPos];
      if (c == (char)0 && this.endPos == this.charsInBuffer) {
        this.GetNextFragment();
        c = this.buffer[this.endPos];
      }
      return c;
    }

    /// <summary>
    /// Gets another fragment of characters from the source document and updates this.buffer, this.endPos and this.startPos accordingly.
    /// The new fragment will start with the first character of the current token (this.startPos). If the old fragment started at the same character (in other words
    /// if the old fragment did not contain more than one complete token), the size of the buffer is doubled so that the new fragment is 
    /// bigger than the old fragment and thus scanning will not get stuck. (This assumes that all token scanning code will tread EOF as a token terminator.)
    /// </summary>
    private void GetNextFragment()
      //^ requires this.charsInBuffer > 0 || (this.charsInBuffer == 0 && this.startPos == 0 && this.endPos == 0);
      //^ ensures this.buffer[this.charsInBuffer] == 0;
      //^ ensures this.endPos == old(this.endPos) - old(this.startPos);
      //^ ensures this.startPos == 0;
    {
      this.offset += this.startPos;
      if (this.startPos == 0 && this.charsInBuffer > 0) {
        //ran out of characters in the buffer before hitting a new token. Have to increase the size of the buffer in order not to get stuck.
        long newBufferLength = this.buffer.Length*2L;
        if (newBufferLength+this.offset > int.MaxValue) 
          newBufferLength = int.MaxValue-this.offset;
        int bufLen = (int)newBufferLength;
        //^ assume 0 < bufLen; //no overlow is assured by previous if statement
        this.buffer = new char[bufLen];
      }
      this.charsInBuffer = this.sourceLocation.CopyTo(this.offset, this.buffer, 0, this.buffer.Length-1);
      this.buffer[this.charsInBuffer] = (char)0;
      this.endPos -= this.startPos;
      this.startPos = 0;
    }

    private char GetPreviousChar() 
      //^ requires this.endPos > 0;
    {
      return this.buffer[this.endPos-1];
    }

    internal static int GetHexValue(char hex) {
      int hexValue;
      if ('0' <= hex && hex <= '9')
        hexValue = hex - '0';
      else if ('a' <= hex && hex <= 'f')
        hexValue = hex - 'a' + 10;
      else
        hexValue = hex - 'A' + 10;
      return hexValue;
    }

    /// <summary>
    /// Returns a string that corresponds to the last token that was scanned.
    /// If the last token was an identifier that includes escape sequences then
    /// the returned string is the unescaped string (the escape sequences have been
    /// replaced by the characters they represent). If the last token was an identifier
    /// that was prefixed by the @ character, that character is omitted from the result.
    /// </summary>
    //^ [Pure]
    internal string GetIdentifierString() {
      if (this.identifierBuilder.Length > 0) return this.identifierBuilder.ToString();
      int start = this.startPos;
      if (this.GetChar(start) == '@' && start < this.endPos) start++;
      return this.Substring(start, this.endPos-start);
    }

    public Token GetNextToken(bool inSpecCode, bool specKeywordExpected) {
      Token token = Token.None;
      this.tokenIsFirstAfterLineBreak = false;
    nextToken:
      this.identifierBuilder.Length = 0;
      char c = this.SkipBlanks();
      if (this.endPos > 0) this.startPos = this.endPos - 1;
      switch (c) {
        case (char)0:
          token = Token.EndOfFile; //Null char is a signal from SkipBlanks that end of source has been reached
          this.tokenIsFirstAfterLineBreak = true;
          break;
        case '[':
          token = Token.LeftBracket;
          break;
        case ']':
          token = Token.RightBracket;
          break;
        case '(':
          token = Token.LeftParenthesis;
          break;
        case ')':
          token = Token.RightParenthesis;
          break;
        case '{':
          token = Token.LeftBrace;
          break;
        case '}':
          token = Token.RightBrace;
          break;
        case '∀':
          token = Token.Forall;
          break;
        case '∃':
          token = Token.Exists;
          break;
        case '∈':
          token = Token.SetIn;
          break;
        case 'λ':
          token = Token.Lambda;
          break;
        case '∩':
          token = Token.SetIntersection;
          break;
        case '∪':
          token = Token.SetUnion;
          break;
        case '.':
          token = Token.Dot;
          c = this.GetCurrentChar();
          if (Scanner.IsDigit(c)) {
            token = this.ScanNumber('.');
          } else if (c == '.' && this.PeekAheadBy(1) == '.') {
            token = Token.Range;
            this.endPos+=2;
          }
          break;
        case '-':
          token = Token.Subtract;
          c = this.GetCurrentChar();
          if (c == '=') {
            token = Token.SubtractAssign; this.endPos++;
          } else if (c == '-') {
            token = Token.SubtractOne; this.endPos++;
          } else if (c == '>') {
            token = Token.Arrow; this.endPos++;
          }
          break;
        case '+':
          token = Token.Plus;
          c = this.GetCurrentChar();
          if (c == '=') {
            token = Token.AddAssign; this.endPos++;
          } else if (c == '+') {
            token = Token.AddOne; this.endPos++;
          }
          break;
        case '&':
          token = Token.BitwiseAnd;
          c = this.GetCurrentChar();
          if (c == '=') {
            token = Token.BitwiseAndAssign; this.endPos++;
          } else if (c == '&') {
            token = Token.LogicalAnd; this.endPos++;
          }
          break;
        case '*':
          token = Token.Multiply;
          c = this.GetCurrentChar();
          if (c == '=') {
            token = Token.MultiplyAssign; this.endPos++;
          }
          break;
        case '~':
          token = Token.BitwiseNot;
          break;
        case '!':
          token = Token.LogicalNot;
          c = this.GetCurrentChar();
          if (c == '=') {
            token = Token.NotEqual; this.endPos++;
          }
          break;
        case '/':
          token = Token.Divide;
          c = this.GetCurrentChar();
          switch (c) {
            case '=':
              token = Token.DivideAssign; this.endPos++;
              break;
            case '/':
              c = this.PeekAheadBy(1);
              if (c == '^') {
                this.endPos+=2;
                goto nextToken;
              }
              this.SkipSingleLineComment();
              if (this.ignoreComments) {
                if (this.endPos >= this.charsInBuffer) {
                  token = Token.EndOfFile;
                  this.tokenIsFirstAfterLineBreak = true;
                  break; // just break out and return
                }
                goto nextToken; // read another token this last one was a comment
              } else {
                token = Token.SingleLineComment;
                break;
              }
            case '*':
              this.endPos++;
              c = this.GetCurrentChar();
              //^ assert 0 < this.endPos;
              //^ assume 0 < this.endPos; //follows from previous assert
              if (this.ignoreComments) {
                int savedEndPos = this.endPos;
                this.SkipMultiLineComment();
                if (this.endPos == this.charsInBuffer && this.GetPreviousChar() != '/') {
                  this.endPos = savedEndPos;
                  this.HandleError(Error.NoCommentEnd);
                  this.tokenIsFirstAfterLineBreak = true;
                  token = Token.EndOfFile;
                  this.endPos = this.charsInBuffer;
                  break;
                }
                goto nextToken; // read another token this last one was a comment
              } else {
                this.SkipMultiLineComment();
                token = Token.MultiLineComment;
                break;
              }
          }
          break;
        case '%':
          token = Token.Remainder;
          c = this.GetCurrentChar();
          if (c == '=') {
            token = Token.RemainderAssign; this.endPos++;
          } else if (c == '>') {
            token = Token.RightBrace; this.endPos++;
          }
          break;
        case '<':
          token = Token.LessThan;
          c = this.GetCurrentChar();
          if (c == '=') {
            token = Token.LessThanOrEqual;
            c = this.GetNextCharAndIncrementEndPos();
            if (c == '=') {
              token = Token.Explies;
              c = this.GetNextCharAndIncrementEndPos();
              if (c == '>') {
                token = Token.IfAndOnlyIf; this.endPos+=1;
              }
            }
          } else if (c  == '%'){
            token = Token.LeftBrace; this.endPos++;
          } else if (c  == ':') {
            token = Token.LeftBracket; this.endPos++;
          } else if (c == '<') {
            token = Token.LeftShift;
            c = this.GetNextCharAndIncrementEndPos();
            if (c == '=') {
              token = Token.LeftShiftAssign; this.endPos++;
            }
          }
          break;
        case '>':
          token = Token.GreaterThan;
          c = this.GetCurrentChar();
          if (c == '=') {
            token = Token.GreaterThanOrEqual; this.endPos++;
          } else if (c == '>') {
            token = Token.RightShift;
            c = this.GetNextCharAndIncrementEndPos();
            if (c == '=') {
              token = Token.RightShiftAssign; this.endPos++;
            }
          }
          break;
        case '=':
          token = Token.Assign;
          c = this.GetCurrentChar();
          if (c == '=') {
            token = Token.Equal;
            c = this.GetNextCharAndIncrementEndPos();
            if (c == '>') {
              token = Token.Implies; this.endPos++;
            }
          }
          break;
        case '^':
          token = Token.BitwiseXor;
          c = this.GetCurrentChar();
          if (c == '=') {
            token = Token.BitwiseXorAssign; this.endPos++;
          }
          break;
        case '|':
          token = Token.BitwiseOr;
          c = this.GetCurrentChar();
          if (c == '=') {
            token = Token.BitwiseOrAssign; this.endPos++;
          } else if (c == '|') {
            token = Token.LogicalOr; this.endPos++;
          }
          break;
        case '?':
          token = Token.Conditional;
          break;
        case ':':
          token = Token.Colon;
          c = this.GetCurrentChar();
          if (c == '>') {
            token = Token.RightBracket; 
            this.endPos++;
          } else if (c == ':') {
            token = Token.ScopeResolution;
            this.endPos++;
          }
          break;
        case ';':
          token = Token.Semicolon;
          break;
        case ',':
          token = Token.Comma;
          break;
        case '\'':
          token = this.ScanCharacter(true);
          break;
        case '"':
          token = Token.SByteStringLiteral;
          this.ScanString(c, true);
          break;
        case '\\':
          if (inSpecCode) goto default;
          if (this.IsIdentifierStartChar(c)) {
            token = Token.Identifier;
            this.ScanIdentifier();
            break;
          }
          if (this.GetCurrentChar() == '\r') {
            c = this.GetNextCharAndIncrementEndPos();
            if (c == '\n') this.GetNextCharAndIncrementEndPos();
            goto nextToken;
          }
          //^ assume this.endPos < this.charsInBuffer; //otherwise c would be (char)0
          this.ScanEscapedChar();
          token = Token.IllegalCharacter;
          break;
        // line terminators
        case '\r':
          this.tokenIsFirstAfterLineBreak = true;
          if (this.GetCurrentChar() == '\n') this.endPos++;
          goto nextToken;
        case '\n':
        case (char)0x85:
        case (char)0x2028:
        case (char)0x2029:
          this.tokenIsFirstAfterLineBreak = true;
          goto nextToken;
        default:
          if ('a' <= c && c <= 'z') {
            token = this.ScanKeyword(c, specKeywordExpected);
          } else if (c == '_') {
            token = this.ScanExtendedKeyword();
          } else if (c == '\\') {
            token = this.ScanExtendedVccKeyword();
          } else if ('A' <= c && c <= 'Z') {
            if (c == 'L'){
              char ch = this.PeekAheadBy(0);
              if (ch == '\'') {
                this.startPos++;
                this.endPos++;
                token = this.ScanCharacter(false);
              } else if (ch == '"') {
                token = Token.StringLiteral;
                this.startPos++;
                this.endPos++;
                this.ScanString('"', false);
              } else {
                token = Token.Identifier;
                //^ assume 0 < this.endPos && this.endPos < this.charsInBuffer; //otherwise c would be (char)0
                this.ScanIdentifier();
              }
            } else {
              token = Token.Identifier;
              //^ assume 0 < this.endPos && this.endPos < this.charsInBuffer; //otherwise c would be (char)0
              this.ScanIdentifier();
            }
          } else if (Scanner.IsDigit(c)) {
            token = this.ScanNumber(c);
          } else if (Scanner.IsUnicodeLetter(c)) {
            token = Token.Identifier;
            //^ assume 0 < this.endPos && this.endPos < this.charsInBuffer; //otherwise c would be (char)0
            this.ScanIdentifier();
          } else if (inSpecCode && c == '\\') {
            token = Token.Identifier;
            this.endPos++;
            this.ScanIdentifier();
          } else
            token = Token.IllegalCharacter;
          break;
      }
      return token;
    }

    //^ [Pure]
    private ISourceLocation GetSourceLocation(int position, int length)
      //^ requires position >= 0;
      //^ requires 0 <= this.sourceLocation.StartIndex + position;
      //^ requires this.sourceLocation.StartIndex + position <= this.sourceLocation.Length;
      //^ requires this.sourceLocation.StartIndex+position+length <= this.sourceLocation.Length;
      //^ requires 0 <= length && length <= this.sourceLocation.Length;
    {
      int start = this.sourceLocation.StartIndex+position;
      ISourceDocument sdoc = this.sourceLocation.SourceDocument;
      //^ assume start < sdoc.Length; //follows from the precondition
      //^ assume start+length <= sdoc.Length; //follows from the precondition
      return sdoc.GetSourceLocation(start, length);
    } 

    internal string/*?*/ GetString() {
      return this.unescapedString;
    }

    internal string GetTokenSource() {
      int endPos = this.endPos;
      return this.Substring(this.startPos, Math.Max(endPos - this.startPos, 1));
    }

    private void HandleError(Error error, params string[] messageParameters) {
      if (this.endPos <= this.lastReportedErrorPos) return;
      if (this.scannerErrors == null) return;
      this.lastReportedErrorPos = this.endPos;
      ISourceLocation errorLocation;
      if (error == Error.BadHexDigit) {
        //^ assume 0 <= this.offset+this.endPos-1; //no overflow
        //^ assume 0 <= this.sourceLocation.StartIndex+this.offset+this.endPos-1; //no overflow
        //^ assume this.sourceLocation.StartIndex+this.offset+this.endPos <= this.sourceLocation.Length; //from invariants
        errorLocation = this.GetSourceLocation(this.offset+this.endPos-1, 1);
      } else {
        //^ assume 0 <= this.offset+this.startPos; //no overflow
        //^ assume 0 <= this.sourceLocation.StartIndex+this.offset+this.startPos; //no overflow
        //^ assume this.sourceLocation.StartIndex+this.offset+this.endPos <= this.sourceLocation.Length; //from invariants
        errorLocation = this.GetSourceLocation(this.offset+this.startPos, this.endPos-this.startPos);
      }
      this.scannerErrors.Add(new VccErrorMessage(errorLocation, error, messageParameters));
    }

    //^ [Pure]
    public static bool IsBlankSpace(char c) {
      if (c == (char)0x20) return true;
      if (c <= 128)
        return c == (char)0x09 || c == (char)0x0C || c == (char)0x1A;
      else
        return IsUnicodeBlankSpace(c);
    }

    //^ [Pure]
    private static bool IsUnicodeBlankSpace(char c) {
      return Char.GetUnicodeCategory(c) == UnicodeCategory.SpaceSeparator;
    }

    //^ [Pure]
    public static bool IsBlankSpaceOrNull(char c)
      //^ ensures c == (char)0 ==> result;
    {
      if (c == (char)0x20) return true;
      if (c <= 128)
        return c == (char)0x09 || c == (char)0x0C || c == (char)0x1A || c == (char)0;
      else
        return IsUnicodeBlankSpace(c);
    }

    //^ [Pure]
    public static bool IsEndOfLine(char c)
      //^ ensures result <==> c == (char)0x0D || c == (char)0x0A || c == (char)0x85 || c == (char)0x2028 || c == (char)0x2029;
    {
      if (c == (char)0x0D || c == (char)0x0A) return true;
      return c == (char)0x85 || c == (char)0x2028 || c == (char)0x2029;
    }

    private bool IsIdentifierPartChar(char c) 
      //^ requires this.charsInBuffer > 0;
      //^ requires this.endPos < this.charsInBuffer;
    {
      if (this.IsIdentifierStartCharHelper(c, true))
        return true;
      if ('0' <= c && c <= '9')
        return true;
      if (c == '\\' && this.endPos < this.charsInBuffer-1) {
        this.endPos++;
        this.ScanEscapedChar();
        this.endPos--;
        return true; //It is not actually true, or IsIdentifierStartCharHelper would have caught it, but this makes for better error recovery
      }
      return false;
    }

    private bool IsIdentifierStartChar(char c)
      //^ requires this.charsInBuffer > 0;
      //^ requires this.endPos < this.charsInBuffer;
    {
      return this.IsIdentifierStartCharHelper(c, false);
    }

    private bool IsIdentifierStartCharHelper(char c, bool expandedUnicode)
      //^ requires this.charsInBuffer > 0;
      //^ requires this.endPos < this.charsInBuffer;
    {
      int escapeLength = 0;
      int savedEndPos = this.endPos;
      UnicodeCategory ccat = 0;
      if (c == '\\') {
        this.endPos++;
        char cc = this.GetCurrentChar();
        switch (cc) {
          case 'u':
            escapeLength = 4;
            break;
          case 'U':
            escapeLength = 8;
            break;
          default:
            this.endPos--;
            return false;
        }
        int escVal = 0;
        for (int i = 0; i < escapeLength; i++)
          //^ invariant this.charsInBuffer > 0;
        {
          this.endPos++;
          char ch = this.GetCurrentChar();
          escVal <<= 4;
          if (Scanner.IsHexDigit(ch))
            escVal |= Scanner.GetHexValue(ch);
          else {
            escVal >>= 4;
            break;
          }
        }
        if (escVal > 0xFFFF) return false; //REVIEW: can a 32-bit Unicode char ever be legal? If so, how does one categorize it?
        c = (char)escVal;
        //TODO: error if c < 0xA0 (except '$', '@' and '`') or if 0xD800 <= c <= 0xDFFF;
      }
      if ('a' <= c && c <= 'z' || 'A' <= c && c <= 'Z' || c == '_')
        goto isIdentifierChar;
      if (c < 128) {
        if (escapeLength > 0) this.endPos = savedEndPos;
        return false;
      }
      ccat = Char.GetUnicodeCategory(c);
      switch (ccat) {
        case UnicodeCategory.UppercaseLetter:
        case UnicodeCategory.LowercaseLetter:
        case UnicodeCategory.TitlecaseLetter:
        case UnicodeCategory.ModifierLetter:
        case UnicodeCategory.OtherLetter:
        case UnicodeCategory.LetterNumber:
          goto isIdentifierChar;
        case UnicodeCategory.NonSpacingMark:
        case UnicodeCategory.SpacingCombiningMark:
        case UnicodeCategory.DecimalDigitNumber:
        case UnicodeCategory.ConnectorPunctuation:
          if (expandedUnicode) goto isIdentifierChar;
          if (escapeLength > 0) this.endPos -= escapeLength + 1;
          return false;
        case UnicodeCategory.Format:
          if (expandedUnicode) goto isIdentifierChar;
          if (escapeLength > 0) this.endPos -= escapeLength + 1;
          return false;
        default:
          if (escapeLength > 0) this.endPos -= escapeLength + 1;
          return false;
      }
    isIdentifierChar:
      if (escapeLength > 0) {
        int escapePos = this.endPos-escapeLength-1;
        int startPos = this.idLastPosOnBuilder;
        if (startPos == 0) startPos = this.startPos;
        if (escapePos > startPos)
          this.identifierBuilder.Append(this.Substring(startPos, escapePos - startPos));
        if (ccat != UnicodeCategory.Format)
          this.identifierBuilder.Append(c);
        this.idLastPosOnBuilder = this.endPos;
      } else if (ccat == UnicodeCategory.Format) {
        int startPos = this.idLastPosOnBuilder;
        if (startPos == 0) startPos = this.startPos;
        if (this.endPos > startPos)
          this.identifierBuilder.Append(this.Substring(startPos, this.endPos - startPos));
        this.idLastPosOnBuilder = this.endPos;
      }
      return true;
    }

    /// <summary>
    /// Returns true if '0' &lt;= c &amp;&amp; c &lt;= '9'.
    /// </summary>
    //^ [Pure]
    internal static bool IsDigit(char c)
      //^ ensures result <==> '0' <= c && c <= '9';
    {
      return '0' <= c && c <= '9';
    }

    internal static bool IsHexDigit(char c)
      //^ ensures result <==> Scanner.IsDigit(c) || 'A' <= c && c <= 'F' || 'a' <= c && c <= 'f';
    {
      return Scanner.IsDigit(c) || 'A' <= c && c <= 'F' || 'a' <= c && c <= 'f';
    }

    /// <summary>
    /// Returns true if '0' &lt;= c &amp;&amp; c &lt;= '7'.
    /// </summary>
    //^ [Pure]
    internal static bool IsOcatalDigit(char c)
      //^ ensures result <==> '0' <= c && c <= '7';
    {
      return '0' <= c && c <= '7';
    }

    internal static bool IsAsciiLetter(char c)
      //^ ensures result <==> 'A' <= c && c <= 'Z' || 'a' <= c && c <= 'z';
    {
      return 'A' <= c && c <= 'Z' || 'a' <= c && c <= 'z';
    }

    internal static bool IsUnicodeLetter(char c)
      // ^ ensures result <==> c >= 128 && Char.IsLetter(c);
    {
      return c >= 128 && Char.IsLetter(c);
    }

    private Token ScanCharacter(bool isByteCharacter)
      //^ requires this.endPos <= this.charsInBuffer;
      //^ requires this.charsInBuffer > 0;
    {
      this.ScanString('\'', isByteCharacter);
      //^ assert this.unescapedString != null;
      int n = this.unescapedString.Length;
      if (n == 0) {
        if (this.GetCurrentChar() == '\'') {
          //this happens when ''' is encountered. Scan it as if it were legal, but give an error.
          this.charLiteralValue = '\'';
          this.endPos++;
          this.HandleError(Error.UnescapedSingleQuote);
        } else {
          this.charLiteralValue = (char)0;
          this.HandleError(Error.EmptyCharConst);
        }
        return isByteCharacter ? Token.SByteLiteral : Token.CharLiteral;
      } else {
        this.charLiteralValue = this.unescapedString[0];
        if (n == 1) {
          if (isByteCharacter) return Token.SByteLiteral;
          return Token.CharLiteral;
        }
        if (n > 4)
          this.HandleError(Error.TooManyCharsInConst);
        if (n > 1)
          this.charLiteralValue = (this.charLiteralValue << 8) | (this.unescapedString[1] & 0xFF);
        if (n > 2)
          this.charLiteralValue = (this.charLiteralValue << 8) | (this.unescapedString[2] & 0xFF);
        if (n > 3)
          this.charLiteralValue = (this.charLiteralValue << 8) | (this.unescapedString[3] & 0xFF);
        return Token.MultiCharLiteral;
      }
    }

    private void ScanEscapedChar(StringBuilder sb) 
      //^ requires this.endPos <= this.charsInBuffer;
    {
      char ch = this.GetCurrentChar();
      if (ch == '\r') {
        ch = this.GetNextCharAndIncrementEndPos();
        if (ch == '\n') this.GetNextCharAndIncrementEndPos();
        return;
      }
      if (ch != 'U') {
        sb.Append(this.ScanEscapedChar());
        return;
      }
      //Scan 32-bit Unicode character. 
      uint escVal = 0;
      this.endPos++;
      for (int i = 0; i < 8; i++)
        //^ invariant this.endPos <= this.charsInBuffer;
      {
        ch = this.GetCurrentChar();
        escVal <<= 4;
        if (Scanner.IsHexDigit(ch))
          escVal |= (uint)Scanner.GetHexValue(ch);
        else {
          this.HandleError(Error.IllegalEscape);
          escVal >>= 4;
          break;
        }
        this.endPos++;
      }
      if (escVal < 0x10000)
        sb.Append((char)escVal);
      else if (escVal <= 0x10FFFF) {
        //Append as surrogate pair of 16-bit characters.
        char ch1 = (char)((escVal - 0x10000) / 0x400 + 0xD800);
        char ch2 = (char)((escVal - 0x10000) % 0x400 + 0xDC00);
        sb.Append(ch1);
        sb.Append(ch2);
      } else {
        sb.Append((char)escVal);
        this.HandleError(Error.IllegalEscape);
      }
    }

    private char ScanEscapedChar()
      //^ requires this.endPos <= this.charsInBuffer;
    {
      int escVal = 0;
      bool requireFourDigits = false;
      int savedStartPos = this.startPos;
      int errorStartPos = this.endPos - 1;
      if (this.endPos == this.charsInBuffer) {
        this.startPos = errorStartPos;
        this.HandleError(Error.IllegalEscape);
        this.startPos = savedStartPos;
        return (char)0;
      }
      char ch = this.GetCurrentCharAndIncrementEndPos();
      switch (ch) {
        default:
          this.startPos = errorStartPos;
          this.HandleError(Error.IllegalEscape);
          this.startPos = savedStartPos;
          if (ch == 'X') goto case 'x';
          return (char)0;
        // Single char escape sequences \b etc
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
        // octal escape sequences \O \OO \OOO
        case '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7':
          escVal = ch - '0';
          for (int i = 0; i < 2; i++)
            //^ invariant this.endPos <= this.charsInBuffer;
          {
            ch = this.GetCurrentChar();
            escVal <<= 3;
            if (Scanner.IsOcatalDigit(ch))
              escVal |= ch - '0';
            else
              return (char)(escVal >> 3);
            this.endPos++;
          }
          return (char)escVal;
        // unicode escape sequence \uHHHH
        case 'u':
          requireFourDigits = true;
          goto case 'x';
        // hexadecimal escape sequence \xH or \xHH or \xHHH or \xHHHH
        case 'x':
          for (int i = 0; i < 4; i++)
            //^ invariant this.endPos <= this.charsInBuffer;
          {
            ch = this.GetCurrentChar();
            escVal <<= 4;
            if (Scanner.IsHexDigit(ch))
              escVal |= Scanner.GetHexValue(ch);
            else {
              if (i == 0 || requireFourDigits) {
                this.startPos = errorStartPos;
                this.HandleError(Error.IllegalEscape);
                this.startPos = savedStartPos;
              }
              return (char)(escVal >> 4);
            }
            this.endPos++;
          }
          return (char)escVal;
      }
    }

    /// <summary>
    /// We've already seen _
    /// </summary>
    /// <returns>Extended keyword token or identifier.</returns>
    private Token ScanExtendedKeyword() 
      //^ requires this.charsInBuffer > 0;
      //^ requires this.startPos < this.endPos;
    {
      bool microsoftKeyword = this.GetCurrentChar() == '_';
      for (; ; ) 
        //^ invariant this.charsInBuffer > 0;
        //^ invariant this.startPos < this.endPos;
      {
        char c = this.GetCurrentChar();
        if ('a' <= c && c <= 'z' || c == 'B' || c == '_' || '0' <= c && c <= '9') {
          this.endPos++;
          continue;
        } else {
          if (this.endPos == this.charsInBuffer)
            return Token.Identifier;
          if (this.IsIdentifierPartChar(c)) {
            this.endPos++;
            this.ScanIdentifier();
            return Token.Identifier;
          }
          break;
        }
      }
      Keyword extendedKeyword = microsoftKeyword ? Scanner.MicrosoftKeywords : Scanner.ExtendedKeywords;
      if (this.underscoreIsKeyword && this.startPos + 1 == this.endPos)
        return Token.Specification;
      return extendedKeyword.GetKeyword(this.buffer, this.startPos, this.endPos);
    }

    private Token ScanExtendedVccKeyword() {
      for (; ; )
      //^ invariant this.charsInBuffer > 0;
      //^ invariant this.startPos < this.endPos;
      {
        char c = this.GetCurrentChar();
        if ('a' <= c && c <= 'z' || c == 'B' || c == '_' || '0' <= c && c <= '9') {
          this.endPos++;
          continue;
        } else {
          if (this.endPos == this.charsInBuffer)
            return Token.Identifier;
          if (this.IsIdentifierPartChar(c)) {
            this.endPos++;
            this.ScanIdentifier();
            return Token.Identifier;
          }
          break;
        }
      }
      return ExtendedVccKeywords.GetKeyword(this.buffer, this.startPos, this.endPos);
    }


    private void ScanIdentifier()
      //^ requires this.endPos > 0;
    {
      int i = this.endPos;
      char[] buffer = this.buffer;
      for (; ; )
        //^ invariant this.charsInBuffer > 0;
        //^ invariant 0 <= i && i <= this.charsInBuffer && buffer == this.buffer;
        //^ invariant i >= this.endPos;
      {
        char c = buffer[i];
        if ('a' <= c && c <= 'z' || 'A' <= c && c <= 'Z' || '0' <= c && c <= '9' || c == '_') {
          i++;
          continue;
        }
        this.endPos = i;
        if (c == (char)0 && i >= this.charsInBuffer) {
          this.GetNextFragment();
          i = this.endPos;
          buffer = this.buffer;
          if (i >= this.charsInBuffer) break;
          continue;
        }
        if (c == '\\') {
          if (!this.IsIdentifierPartChar(c)) {
            break;
          }
        }else if (c < 128 || !this.IsIdentifierPartChar(c)) {
          break;
        }
        i++;
      }
      this.endPos = i;
      if (this.idLastPosOnBuilder > 0) {
        this.identifierBuilder.Append(this.Substring(this.idLastPosOnBuilder, i - this.idLastPosOnBuilder));
        this.idLastPosOnBuilder = 0;
        if (this.identifierBuilder.Length == 0)
          this.HandleError(Error.UnexpectedToken);
      }
    }

    private Token ScanKeyword(char ch, bool specKeywordExpected)
      //^ requires 'a' <= ch && ch <= 'z';
      //^ requires this.startPos < this.endPos;
    {
      int i = this.endPos;
      char[] buffer = this.buffer;
      for (; ; )
        //^ invariant this.charsInBuffer > 0;
        //^ invariant 0 <= i && i <= this.charsInBuffer && buffer == this.buffer;
        //^ invariant this.startPos < this.endPos;
        //^ invariant this.endPos <= i;
      {
        char c = buffer[i];
        if ('a' <= c && c <= 'z' || c == '_') {
          i++;
          continue;
        }
        this.endPos = i;
        if (c == (char)0 && this.endPos == this.charsInBuffer) {
          this.GetNextFragment();
          i = this.endPos;
          buffer = this.buffer;
          if (i >= this.charsInBuffer) break;
          continue;
        }
        if (this.IsIdentifierPartChar(c)) {
          this.endPos++;
          this.ScanIdentifier();
          return Token.Identifier;
        }
        break;
      }
      this.endPos = i;

      Token result = Token.Identifier;
      if (specKeywordExpected) {
        var specKeyword = Scanner.SpecKeywords[ch - 'a'];
        if (specKeyword != null) result = specKeyword.GetKeyword(this.buffer, this.startPos, this.endPos);
      }
      if (result == Token.Identifier) {
        Keyword/*?*/ keyword = Scanner.Keywords[ch - 'a'];
        if (keyword != null) result = keyword.GetKeyword(this.buffer, this.startPos, this.endPos);
      }
      return result;
    }

    private Token ScanNumber(char leadChar)
      //^ requires this.charsInBuffer > 0;
      //^ requires this.endPos > 0;
    {
      Token token = leadChar == '.' ? Token.RealLiteral : Token.IntegerLiteral;
      char c;
      bool octal = false;
      bool hex = false;
      if (leadChar == '0') {
        c = this.GetCurrentChar();
        if (c == 'x' || c == 'X') {
          if (!Scanner.IsHexDigit(this.PeekAheadBy(1)))
            return token; //return the 0 as a separate token
          this.endPos++;
          token = Token.HexLiteral;
          do
          //^ invariant this.endPos <= this.charsInBuffer;
          //^ invariant this.endPos > 0;
          {
            c = this.GetCurrentChar();
            if (!Scanner.IsHexDigit(c)) break;
            this.endPos++;
          } while (true);
          if (c == '.' || c == 'p' || c == 'P')
            hex = true;
          else
            return token;
        } else {
          token = Token.OctalLiteral;
          octal = true;
        }
      }
      if (leadChar == '0' && !octal)
        this.HandleError(Error.SyntaxError); //TODO: specific error about expecting an octal number
      bool alreadyFoundPoint = leadChar == '.';
      bool alreadyFoundExponent = false;
      int positionOfFirstPoint = -1;
      for (; ; )
        //^ invariant this.endPos <= this.charsInBuffer;
        //^ invariant this.endPos > 0;
      {
        c = this.GetCurrentChar();
        bool isDigit;
        if (hex)
          isDigit = Scanner.IsHexDigit(c);
        else
          isDigit = Scanner.IsDigit(c);
        if (!isDigit) {
          if (c == '.') {
            if (alreadyFoundPoint) break;
            alreadyFoundPoint = true;
            positionOfFirstPoint = this.endPos;
            token = hex ? Token.HexFloatLiteral : Token.RealLiteral;
          } else if (c == 'e' || c == 'E') {
            if (alreadyFoundExponent || hex) break;
            alreadyFoundExponent = true;
            alreadyFoundPoint = true;
            token = Token.RealLiteral;
          } else if (c == 'p' || c == 'P') {
            if (alreadyFoundExponent || !hex) break;
            alreadyFoundExponent = true;
            alreadyFoundPoint = true;
            token = Token.HexFloatLiteral;
          } else if (c == '+' || c == '-') {
            char e = this.GetPreviousChar();
            if (hex) {
              if (e != 'p' && e != 'P') break;
            } else {
              if (e != 'e' && e != 'E') break;
            }
          } else
            break;
        } else if (octal && !Scanner.IsOcatalDigit(c)) {
          //TODO: error
          octal = false;
        }
        this.endPos++;
      }
      c = this.GetPreviousChar();
      if (c == '+' || c == '-') {
        this.endPos--;
        c = this.GetPreviousChar();
      }
      if (c == 'e' || c == 'E') {
        this.endPos--;
        if (positionOfFirstPoint == -1) 
          return hex ? Token.HexLiteral : (octal ? Token.OctalLiteral : Token.IntegerLiteral);
      }
      return token;
    }

    public TypeCode ScanNumberSuffix() {
      return ScanNumberSuffix(true);
    }

    /// <summary>
    /// Suffix of a numeric constant could be at most two different chars of 'u'  'l' for integer and 'f' 'l' for floating point, 
    /// case insensitive, or u followed by ix, where x is size in bits. 
    /// 
    /// We do not allow long long ("ll" or "ull") constant. 
    /// </summary>
    /// <param name="parsingInteger">Whether we are parsing an integer. We use this information to disambigute the 'l' case,
    /// which applies to both floating point and integer. </param>
    /// <returns></returns>
    public TypeCode ScanNumberSuffix(bool parsingInteger) {
      this.startPos = this.endPos;
      char ch = this.GetCurrentChar();
      if (ch == 'u' || ch == 'U') {
        this.endPos++;
        char ch2 = this.GetCurrentChar();
        if (ch2 == 'l' || ch2 == 'L') {
          this.endPos++;
          char ch3 = this.GetCurrentChar();
          if (ch3 == 'l' || ch3 == 'L') {
            this.endPos++;
            return TypeCode.UInt64;
          }
          return TypeCode.UInt32;
        } else if (ch2 == 'i' || ch2 == 'I') {
          return this.ScanExtendedIntegerSuffix(true);
        }
        return TypeCode.UInt32;
      } else if (ch == 'l' || ch == 'L') {
        this.endPos++;
        if (ch == 'l') this.HandleError(Error.LowercaseEllSuffix);
        char ch2 = this.GetCurrentChar();
        if (ch2 == 'l' || ch2 == 'L') {
          this.endPos++;
          char ch3 = this.GetCurrentChar();
          if (ch3 == 'u' || ch3 == 'U') {
            this.endPos++;
            return TypeCode.UInt64;
          }
          return TypeCode.Int64;
        } else if (ch2 == 'u' || ch2 == 'U') {
          this.endPos++;
          return TypeCode.UInt32;
        }
        if (parsingInteger) {
          return TypeCode.Int32;
        } else {
          return TypeCode.Double;
        }
      } else if (ch == 'f' || ch == 'F') {
        this.endPos++;
        return TypeCode.Single;
      } else if (ch == 'i' || ch == 'I') {
        return this.ScanExtendedIntegerSuffix(false);
      }
      return TypeCode.Empty;
    }

    private TypeCode ScanExtendedIntegerSuffix(bool seenUnsigned) {
      TypeCode result = TypeCode.Empty;
      int consumedChars = 3;

      if (this.PeekAheadBy(1) == '6' && this.PeekAheadBy(2) == '4')
        result = seenUnsigned ? TypeCode.UInt64 : TypeCode.Int64;
      else if (this.PeekAheadBy(1) == '3' && this.PeekAheadBy(2) == '2')
        result = seenUnsigned ? TypeCode.UInt32 : TypeCode.Int32;
      else if (this.PeekAheadBy(1) == '1' && this.PeekAheadBy(2) == '6')
        result = seenUnsigned ? TypeCode.UInt16 : TypeCode.Int16;
      else if (this.PeekAheadBy(1) == '8') {
        result = seenUnsigned ? TypeCode.Byte : TypeCode.Char;
        consumedChars = 2;
      }

      if (result != TypeCode.Empty)
        this.endPos = this.endPos + consumedChars;

      return result;
    }

    private void ScanString(char closingQuote, bool isByteString) 
      //^ requires closingQuote == '"' || closingQuote == '\'';
      //^ requires this.endPos <= this.charsInBuffer;
      //^ requires this.charsInBuffer > 0;
      //^ ensures this.unescapedString != null;
    {
      char ch;
      char[] buffer = this.buffer;
      int start = this.endPos;
      int i = start;
      this.unescapedString = null;
      StringBuilder/*?*/ unescapedSB = null;
      do
        //^ invariant 0 <= start;
        //^ invariant start <= i && i <= this.charsInBuffer && buffer == this.buffer;
        //^ invariant 0 < this.charsInBuffer && this.charsInBuffer <= buffer.Length;
      {
        ch = buffer[i++];
        if (isByteString && ch > byte.MaxValue) {
          //TODO: error message
        }
        if (ch == (char)0 && i == this.charsInBuffer+1) {
          //Reached the end of a fragment
          this.endPos = --i;
          this.GetNextFragment();
          start -= i-this.endPos;
          i = this.endPos;
          buffer = this.buffer;
          if (i == this.charsInBuffer) {
            //Reached the end of the document
            this.endPos = this.charsInBuffer-1;
            this.FindGoodRecoveryPointAndComplainAboutMissingClosingQuote(closingQuote);
            i = this.endPos;
            break;
          }
          ch = buffer[i++];
        }
        if (ch == '\\') {
          // Got an escape of some sort. Have to use the StringBuilder (but avoid calling Append for every character).
          if (unescapedSB == null) unescapedSB = new StringBuilder(256);
          // start points to the first position that has not been written to the StringBuilder.
          // The first time we get in here that position is the beginning of the string, after that
          // it is the character immediately following the escape sequence
          int len = i - start - 1;
          if (len > 0) // append all the non escaped chars to the string builder
            unescapedSB.Append(buffer, start, len);
          this.endPos = i;
          this.ScanEscapedChar(unescapedSB);
          buffer = this.buffer;
          start = i = this.endPos;
        } else if (Scanner.IsEndOfLine(ch)) {
          this.endPos = i-1;
          this.FindGoodRecoveryPointAndComplainAboutMissingClosingQuote(closingQuote);
          i = this.endPos;
          break;
        }
      } while (ch != closingQuote);

      // update this.unescapedString using the StringBuilder
      if (unescapedSB != null) {
        int len = i - start - 1;
        if (len > 0) // append any trailing non escaped chars to the string builder
          unescapedSB.Append(buffer, start, len);
        this.unescapedString = unescapedSB.ToString();
      } else {
        if (closingQuote == '\'' && (this.startPos >= i-1 || buffer[i-1] != '\'')) {
          //Get here if the closing character quote is missing. An error has already been reported and this.endPos has been positioned at an appropriate recovery point.
          if (this.startPos+1 < this.charsInBuffer)
            this.unescapedString = this.Substring(this.startPos+1, 1);
          else
            this.unescapedString = " ";
        } else {
          if (i <= this.startPos+2)
            this.unescapedString = "";
          else
            this.unescapedString = this.Substring(this.startPos+1, i-this.startPos-2);
        }
      }

      this.endPos = i;
    }

    /// <summary>
    /// If an end of line sequence is encountered before the end of a string or character literal has been encountered,
    /// then this routine will look for a position where either the desired closing quote can be found (becuase the programmer does not know that new lines terminate strings)
    /// or it seems likely that the closing quote has actually been forgotten. 
    /// The routine does not scan beyond the end of the current buffer.
    /// </summary>
    private void FindGoodRecoveryPointAndComplainAboutMissingClosingQuote(char closingQuote) 
      //^ requires this.endPos < this.charsInBuffer;
    {
      int maxPos = this.charsInBuffer;
      int endPos = this.endPos;
      int i;
      if (endPos == maxPos) {
        //Reached the end of the file before reaching the end of the line containing the start of the unterminated string or character literal.
        this.endPos = endPos = maxPos;
      } else {
        //^ assert 0 <= endPos && endPos < maxPos;
        //peek ahead in the buffer looking for a matching quote that occurs before any character that is probably not part of the literal.
        for (i = endPos; i < maxPos; i++)
          //^ invariant maxPos == this.charsInBuffer;
          //^ invariant endPos == this.endPos;
          // ^ invariant 0 <= i && i < maxPos;
        {
          //^ assume 0 <= i;
          //^ assume i < maxPos;
          char ch = this.GetChar(i);
          if (ch == closingQuote) {
            //Found a matching quote before running into a character that is probably not part of the literal.
            //Give an error, but go on as if a new line is actually allowed inside the string or character literal.
            if (this.endPos > 0) {
              //Trim the span of the error to coincide with the last character of the line in which the literal starts.
              this.endPos--;
              if (this.endPos > 0 && this.GetPreviousChar() == (char)0x0d) this.endPos--;
            }
            this.HandleError(Error.NewlineInConst);
            this.endPos = i + 1; //Now update this.endPos to point to the first character beyond the closing quote
            return;
          }
          //^ assert 0 <= i && i < maxPos;
          switch (ch) {
            case ';':
            case '}':
            case ')':
            case ']':
            case '(':
            case '[':
            case '+':
            case '-':
            case '*':
            case '/':
            case '%':
            case '!':
            case '=':
            case '<':
            case '>':
            case '|':
            case '&':
            case '^':
            case '~':
            case '@':
            case ':':
            case '?':
            case ',':
            case '"':
            case '\'':
              //Found a character that is probably not meant to be part of the string or character literal.
              i = maxPos; //Terminate the for loop.
              break;
          }
          //^ assert 0 <= i && i <= maxPos;
        }
      }

      //At this point the assumption is that the closing quote has been omitted by mistake.
      //Look for a likely point where the ommission occurred.
      int lastSemicolon = endPos;
      int lastNonBlank = this.startPos;
      for (i = this.startPos+1; i < endPos; i++)
        //^ invariant endPos == this.endPos;
        // ^ invariant 0 <= i && i < endPos;
      {
        //^ assume 0 <= i && i < endPos;
        char ch = this.GetChar(i);
        if (ch == ';') { lastSemicolon = i; lastNonBlank = i; }
        if (ch == '/' && i < endPos - 1) {
          char ch2 = this.GetChar(++i);
          if (ch2 == '/' || ch2 == '*') {
            i -= 2; break;
          }
        }
        if (Scanner.IsEndOfLine(ch)) break;
        if (!Scanner.IsBlankSpace(ch)) lastNonBlank = i;
      }
      if (lastSemicolon == lastNonBlank)
        this.endPos = lastSemicolon; //The last non blank character before the end of the line (or start of a comment) is a semicolon. Likely, the missing quote should precede it.
      else
        this.endPos = i; //i is the position of the end of line, or of the start of a comment.
      int savedStartPos = this.startPos; //Save the start of the current token
      //Constrain the span of the error to the character before which the missing quote should be inserted.
      this.startPos = this.endPos;
      this.endPos++; //increment endPos to provide a non empty span for the error
      if (closingQuote == '"')
        this.HandleError(Error.ExpectedDoubleQuote);
      else
        this.HandleError(Error.ExpectedSingleQuote);
      //Restore the start of the current token
      this.startPos = savedStartPos;
      //Undo the increment of this.endPos
      this.endPos--;
    }

    private char SkipBlanks() 
      //^ ensures result == (char)0 ==> this.startPos == 0 && this.endPos == 0 && this.charsInBuffer == 0;
      //^ ensures result != (char)0 ==> result == this.buffer[this.startPos] && this.endPos == this.startPos+1;
    {
      char[] buffer = this.buffer;
      int i = this.endPos;
      char c = buffer[i];
      while (Scanner.IsBlankSpaceOrNull(c))
        //^ invariant 0 <= i && i <= this.charsInBuffer && buffer == this.buffer;
        //^ invariant c == buffer[i];
      {
        if (i == this.charsInBuffer){
          //Reached the end of a fragment
          this.startPos = this.endPos = i;
          this.GetNextFragment();
          if (this.charsInBuffer == 0) return (char)0; //Reached the end of the document
          i = this.endPos-1;
          buffer = this.buffer;
        }
        c = buffer[++i];
      }
      if (c != (char)0) {
        this.startPos = i;
        this.endPos = ++i;
      }
      return c;
    }

    private void SkipMultiLineComment() 
      //^ requires this.endPos > 0;
    {
      int i = this.endPos;
      char[] buffer = this.buffer;
      bool previousCharWasAsterisk = false;
      for (; ; )
        //^ invariant 0 <= i && i <= this.charsInBuffer && buffer == this.buffer;
      {
        char c = buffer[i++];
        if (c == '/' && previousCharWasAsterisk) {
          this.endPos = i;
          return;
        }
        if (i > this.charsInBuffer) {
          //Reached the end of a fragment
          this.endPos = --i;
          this.GetNextFragment();
          i = this.endPos;
          buffer = this.buffer;
          if (i >= this.charsInBuffer) return; //Reached the end of the document
          continue;
        }
        previousCharWasAsterisk = c == '*';        
      }
    }

    private void SkipSingleLineComment() {
      char[] buffer = this.buffer;
      int i = this.endPos;
      char c = buffer[i];
      while (!Scanner.IsEndOfLine(c))
        //^ invariant 0 <= i && i <= this.charsInBuffer && buffer == this.buffer;
        //^ invariant i == this.charsInBuffer ==> c == (char)0;
      {
        if (i == this.charsInBuffer) {
          //Reached the end of a fragment
          this.endPos = i;
          this.GetNextFragment();
          i = this.endPos;
          buffer = this.buffer;
          if (i >= this.charsInBuffer) return; //Reached the end of the document
          c = buffer[i];
          continue;
        }
        c = buffer[++i];
      }
      this.endPos = i;
      if (c == (char)0x0D && this.PeekAheadBy(1) == (char)0x0A)
        this.endPos++;
    }

    public ISourceLocation SourceLocationOfLastScannedToken {
      get {
        //^ assume 0 <= this.sourceLocation.StartIndex+this.offset+this.startPos; //no overflow
        //^ assume this.sourceLocation.StartIndex+this.offset+this.endPos <= this.sourceLocation.Length; //invariant
        return this.GetSourceLocation(this.offset+this.startPos, this.endPos-this.startPos);
      }
    }

    private string Substring(int start, int length)
      //^ requires 0 <= start;
      //^ requires start < this.buffer.Length;
      //^ requires 0 <= length;
      //^ requires 0 <= start + length;
      //^ requires start + length <= this.charsInBuffer;
    {
      return new string(this.buffer, start, length);
    }

    internal Snapshot MakeSnapshot() {
      if (this.startPos  > this.charsInBuffer - 512) this.GetNextFragment(); // make sure that we have wiggle room for the token lookahead
      return new Snapshot(this.startPos, this.endPos);
    }

    internal void RevertToSnapshot(Snapshot snapshot) {
      this.startPos = snapshot.startPos;
      this.endPos = snapshot.endPos;
    }

    internal sealed class Snapshot
    {
      internal readonly int startPos;
      internal readonly int endPos;

      internal Snapshot(int startPos, int endPos) {
        this.startPos = startPos;
        this.endPos = endPos;
      }
    }
  }

  public enum Token : int {
    /// <summary>
    /// default(Token). Not a real token.
    /// </summary>
    None,
    /// <summary>
    /// __alignof
    /// </summary>
    AlignOf,
    /// <summary>
    /// auto
    /// </summary>
    Auto,
    /// <summary>
    /// +=
    /// </summary>
    AddAssign,
    /// <summary>
    /// ++
    /// </summary>
    AddOne,
    /// <summary>
    /// ->
    /// </summary>
    Arrow,
    /// <summary>
    /// __assert
    /// </summary>
    Assert,
    /// <summary>
    /// =
    /// </summary>
    Assign,
    /// <summary>
    /// __assume
    /// </summary>
    Assume,
    /// <summary>
    /// __axiom
    /// </summary>
    Axiom,
    /// <summary>
    /// &amp;
    /// </summary>
    BitwiseAnd,
    /// <summary>
    /// &=
    /// </summary>
    BitwiseAndAssign,
    /// <summary>
    /// ~
    /// </summary>
    BitwiseNot,
    /// <summary>
    /// |
    /// </summary>
    BitwiseOr,
    /// <summary>
    /// |=
    /// </summary>
    BitwiseOrAssign,
    /// <summary>
    /// ^
    /// </summary>
    BitwiseXor,
    /// <summary>
    /// ^=
    /// </summary>
    BitwiseXorAssign,
    /// <summary>
    /// __block
    /// </summary>
    Block,
    /// <summary>
    /// _Bool
    /// </summary>
    Bool,
    /// <summary>
    /// break
    /// </summary>
    Break,
    /// <summary>
    /// case
    /// </summary>
    Case,
    /// <summary>
    /// __cdecl
    /// </summary>
    Cdecl,
    /// <summary>
    /// char
    /// </summary>
    Char,
    /// <summary>
    /// L'x'
    /// </summary>
    CharLiteral,
    ///// <summary>
    ///// _Complex
    ///// </summary>
    //Complex,
    /// <summary>
    /// ?
    /// </summary>
    Conditional,
    /// <summary>
    /// :
    /// </summary>
    Colon,
    /// <summary>
    /// ,
    /// </summary>
    Comma,
    /// <summary>
    /// const
    /// </summary>
    Const,
    /// <summary>
    /// continue
    /// </summary>
    Continue,
    /// <summary>
    /// __declspec
    /// </summary>
    Declspec,
    /// <summary>
    /// __decreases
    /// </summary>
    Decreases,
    /// <summary>
    /// default
    /// </summary>
    Default,
    /// <summary>
    /// /
    /// </summary>
    Divide,
    /// <summary>
    /// /=
    /// </summary>
    DivideAssign,
    /// <summary>
    /// do
    /// </summary>
    Do,
    /// <summary>
    /// .
    /// </summary>
    Dot,
    /// <summary>
    /// double
    /// </summary>
    Double,
    /// <summary>
    /// else
    /// </summary>
    Else,
    /// <summary>
    /// enum
    /// </summary>
    Enum,
    /// <summary>
    /// __ensures
    /// </summary>
    Ensures,
    /// <summary>
    /// ==
    /// </summary>
    Equal,
    /// <summary>
    /// __exists
    /// </summary>
    Exists,
    /// <summary>
    /// <==
    /// </summary>
    Explies,
    /// <summary>
    /// extern
    /// </summary>
    Extern,
    /// <summary>
    /// __fastcall
    /// </summary>
    Fastcall,
    /// <summary>
    /// float
    /// </summary>
    Float,
    /// <summary>
    /// for
    /// </summary>
    For,
    /// <summary>
    /// __forall
    /// </summary>
    Forall,
    /// <summary>
    /// goto
    /// </summary>
    Goto,
    /// <summary>
    /// >
    /// </summary>
    GreaterThan,
    /// <summary>
    /// >=
    /// </summary>
    GreaterThanOrEqual,
    /// <summary>
    /// 0x01234567890ABCDEF
    /// </summary>
    HexLiteral,
    /// <summary>
    /// 0x01234567890ABCDEF.01234567890ABCDEFp1234567890
    /// </summary>
    HexFloatLiteral,
    /// <summary>
    /// a-zA-Z0-9_
    /// </summary>
    Identifier,
    /// <summary>
    /// if
    /// </summary>
    If,
    /// <summary>
    /// <==>
    /// </summary>
    IfAndOnlyIf,
    /// <summary>
    /// #
    /// </summary>
    IllegalCharacter,
    /// <summary>
    /// ==>
    /// </summary>
    Implies,
    /// <summary>
    /// inline or __inline or __forceinline
    /// </summary>
    Inline,
    /// <summary>
    /// int
    /// </summary>
    Int,
    /// <summary>
    /// __int16
    /// </summary>
    Int16,
    /// <summary>
    /// __int32
    /// </summary>
    Int32,
    /// <summary>
    /// __int64
    /// </summary>
    Int64,
    /// <summary>
    /// __int8
    /// </summary>
    Int8,
    /// <summary>
    /// 1234567890
    /// </summary>
    IntegerLiteral,
    /// <summary>
    /// __invariant
    /// </summary>
    Invariant,
    /// <summary>
    /// __lambda
    /// </summary>
    Lambda,
    /// <summary>
    /// { or &lt;%
    /// </summary>
    LeftBrace,
    /// <summary>
    /// [ or &lt;:
    /// </summary>
    LeftBracket,
    /// <summary>
    /// (
    /// </summary>
    LeftParenthesis,
    /// <summary>
    /// &lt;&lt;
    /// </summary>
    LeftShift,
    /// <summary>
    /// &lt;&lt;=
    /// </summary>
    LeftShiftAssign,
    /// <summary>
    /// &lt;
    /// </summary>
    LessThan,
    /// <summary>
    /// &lt;=
    /// </summary>
    LessThanOrEqual,
    /// <summary>
    /// &amp;&amp;
    /// </summary>
    LogicalAnd,
    /// <summary>
    /// !
    /// </summary>
    LogicalNot,
    /// <summary>
    /// ||
    /// </summary>
    LogicalOr,
    /// <summary>
    /// long
    /// </summary>
    Long,
    /// <summary>
    /// 'abcd'
    /// </summary>
    MultiCharLiteral,
    /// <summary>
    /// /*....*/
    /// </summary>
    MultiLineComment,
    /// <summary>
    /// *
    /// </summary>
    Multiply,
    /// <summary>
    /// *=
    /// </summary>
    MultiplyAssign,
    /// <summary>
    /// !=
    /// </summary>
    NotEqual,
    /// <summary>
    /// 01234567
    /// </summary>
    OctalLiteral,
    /// <summary>
    /// __old
    /// </summary>
    Old,
    /// <summary>
    /// +
    /// </summary>
    Plus,
    /// <summary>
    /// __pragma
    /// </summary>
    Pragma,
    /// <summary>
    /// ...
    /// </summary>
    Range,
    /// <summary>
    /// __reads
    /// </summary>
    Reads,
    /// <summary>
    /// 0-9.0-9e+-0-9
    /// </summary>
    RealLiteral,
    /// <summary>
    /// register
    /// </summary>
    Register,
    /// <summary>
    /// %
    /// </summary>
    Remainder,
    /// <summary>
    /// %=
    /// </summary>
    RemainderAssign,
    /// <summary>
    /// requires
    /// </summary>
    Requires,
    /// <summary>
    /// return
    /// </summary>
    Return,
    /// <summary>
    /// \result
    /// </summary>
    Result, 
    /// <summary>
    /// } or :&gt;
    /// </summary>
    RightBrace,
    /// <summary>
    /// ] or :&gt;
    /// </summary>
    RightBracket,
    /// <summary>
    /// )
    /// </summary>
    RightParenthesis,
    /// <summary>
    /// &gt;&gt;
    /// </summary>
    RightShift,
    /// <summary>
    /// &gt;&gt;=
    /// </summary>
    RightShiftAssign,
    /// <summary>
    /// 'x'
    /// </summary>
    SByteLiteral,
    /// <summary>
    /// " ... "
    /// </summary>
    SByteStringLiteral,
    /// <summary>
    /// ::
    /// </summary>
    ScopeResolution,
    /// <summary>
    /// \in
    /// </summary>
    SetIn,
    /// <summary>
    /// \in0
    /// </summary>
    SetIn0,
    /// <summary>
    /// \union
    /// </summary>
    SetUnion,
    /// <summary>
    /// \inter
    /// </summary>
    SetIntersection,
    /// <summary>
    /// \diff
    /// </summary>
    SetDifference,
    /// <summary>
    /// __stdcall
    /// </summary>
    Stdcall,
    /// <summary>
    /// ;
    /// </summary>
    Semicolon,
    /// <summary>
    /// //.....
    /// </summary>
    SingleLineComment,
    /// <summary>
    /// short
    /// </summary>
    Short,
    /// <summary>
    /// signed
    /// </summary>
    Signed,
    /// <summary>
    /// sizeof
    /// </summary>
    Sizeof,
    /// <summary>
    /// __specification
    /// </summary>
    Specification,
    /// <summary>
    /// static
    /// </summary>
    Static,
    /// <summary>
    /// L" ... "
    /// </summary>
    StringLiteral,
    /// <summary>
    /// struct
    /// </summary>
    Struct,
    /// <summary>
    /// -
    /// </summary>
    Subtract,
    /// <summary>
    /// -=
    /// </summary>
    SubtractAssign,
    /// <summary>
    /// --
    /// </summary>
    SubtractOne,
    /// <summary>
    /// switch
    /// </summary>
    Switch,
    /// <summary>
    /// template
    /// </summary>
    Template,
    /// <summary>
    /// \this
    /// </summary>
    This,
    /// <summary>
    /// typedef
    /// </summary>
    Typedef,
    /// <summary>
    /// typename
    /// </summary>
    Typename,
    /// <summary>
    /// __unaligned
    /// </summary>
    Unaligned,
    /// <summary>
    /// union
    /// </summary>
    Union,
    /// <summary>
    /// unsigned
    /// </summary>
    Unsigned,
    /// <summary>
    /// __unchecked
    /// </summary>
    Unchecked,
    /// <summary>
    /// void
    /// </summary>
    Void,
    /// <summary>
    /// volatile
    /// </summary>
    Volatile,
    /// <summary>
    /// __w64
    /// </summary>
    W64,
    /// <summary>
    /// while
    /// </summary>
    While,
    /// <summary>
    /// __writes
    /// </summary>
    Writes,
    /// <summary>
    /// assert, context-dependent
    /// </summary>
    SpecAssert,
    /// <summary>
    /// assume, context-dependent
    /// </summary>
    SpecAssume,
    /// <summary>
    /// atomic, context-dependent
    /// </summary>
    SpecAtomic,
    /// <summary>
    /// axiom, context-dependent
    /// </summary>
    SpecAxiom,
    /// <summary>
    /// decreases, context-dependent
    /// </summary>
    SpecDecreases,
    /// <summary>
    /// ensures, context-dependent
    /// </summary>
    SpecEnsures,
    /// <summary>
    /// ghost, context-dependent
    /// </summary>
    SpecGhost,
    /// <summary>
    /// group, context-dependent
    /// </summary>
    SpecGroup,
    /// <summary>
    /// invariant, context-dependent
    /// </summary>
    SpecInvariant,
    /// <summary>
    /// \is
    /// </summary>
    SpecIs,
    /// <summary>
    /// logic, context-dependent
    /// </summary>
    SpecLogic,
    /// <summary>
    /// out, context-dependent
    /// </summary>
    SpecOut,
    /// <summary>
    /// reads, context-dependent
    /// </summary>
    SpecReads,
    /// <summary>
    /// requires, context-dependent
    /// </summary>
    SpecRequires,
    /// <summary>
    /// unwrapping, context-dependent
    /// </summary>
    SpecUnwrapping,
    /// <summary>
    /// writes, context-dependent
    /// </summary>
    SpecWrites,

    /// <summary>
    /// A dummy token produced when the end of the file is reached.
    /// </summary>
    EndOfFile,
  }

  internal sealed class Keyword {
    private Keyword/*?*/ next;
    private Token token;
    private string name;
    private int length; //^ invariant length >= 0;

    private Keyword(Token token, string name)
      //^ requires name.Length > 0;
    {
      this.name = name;
      this.token = token;
      this.length = name.Length;
    }

    private Keyword(Token token, string name, Keyword next)
      //^ requires name.Length > 0;
    {
      this.name = name;
      this.next = next;
      this.token = token;
      this.length = name.Length;
    }


    internal Token GetKeyword(char[] source, int startPos, int endPos)
      //^ requires 0 <= startPos && startPos < endPos;
      //^ requires endPos < source.Length;
    {
      int length = endPos - startPos;
      Keyword/*?*/ keyword = this;
    nextToken:
      while (keyword != null) 
        //^ invariant 0 <= startPos && 0 < startPos+length && startPos+length < source.Length;
      {
        if (length == keyword.length) {
          // we know the first char has to match
          string name = keyword.name;
          for (int i = 1, j = startPos + 1; i < length; i++, j++) 
            //^ invariant i == j - startPos;
          {
            char ch1 = name[i];
            char ch2 = source[j];
            if (ch1 == ch2)
              continue;
            else if (ch2 < ch1)
              return Token.Identifier;
            else {
              keyword = keyword.next;
              goto nextToken;
            }
          }
          return keyword.token;
        } else if (length < keyword.length)
          return Token.Identifier;

        keyword = keyword.next;
      }
      return Token.Identifier;
    }

    internal static Keyword/*?*/[] InitKeywords() {
      // There is a linked list for each letter.
      // In each list, the keywords are sorted first by length, and then lexicographically.
      // So the constructor invocations must occur in the opposite order.
      Keyword/*?*/[] keywords = new Keyword/*?*/[26];
      Keyword keyword;
      // a
      keyword = new Keyword(Token.Auto, "auto");
      keywords['a' - 'a'] = keyword;
      // b+
      keyword = new Keyword(Token.Break, "break");
      keywords['b' - 'a'] = keyword;
      // c
      keyword = new Keyword(Token.Continue, "continue");
      keyword = new Keyword(Token.Const, "const", keyword);
      keyword = new Keyword(Token.Char, "char", keyword);
      keyword = new Keyword(Token.Case, "case", keyword);
      keywords['c' - 'a'] = keyword;
      // d      
      keyword = new Keyword(Token.Default, "default", keyword);
      keyword = new Keyword(Token.Double, "double", keyword);
      keyword = new Keyword(Token.Do, "do", keyword);
      keywords['d' - 'a'] = keyword;
      // e
      keyword = new Keyword(Token.Extern, "extern");
      keyword = new Keyword(Token.Enum, "enum", keyword);
      keyword = new Keyword(Token.Else, "else", keyword);
      keywords['e' - 'a'] = keyword;
      // f
      keyword = new Keyword(Token.Float, "float");
      keyword = new Keyword(Token.For, "for", keyword);
      keywords['f' - 'a'] = keyword;
      // g
      keyword = new Keyword(Token.Goto, "goto");
      keywords['g' - 'a'] = keyword;
      // i
      keyword = new Keyword(Token.Inline, "inline");
      keyword = new Keyword(Token.Int, "int", keyword);
      keyword = new Keyword(Token.If, "if", keyword);
      keywords['i' - 'a'] = keyword;
      //l
      keyword = new Keyword(Token.Long, "long");
      keywords['l' - 'a'] = keyword;
      // r
      keyword = new Keyword(Token.Register, "register");
      keyword = new Keyword(Token.Return, "return", keyword);
      keywords['r' - 'a'] = keyword;
      // s
      keyword = new Keyword(Token.Switch, "switch");
      keyword = new Keyword(Token.Struct, "struct", keyword);
      keyword = new Keyword(Token.Static, "static", keyword);
      keyword = new Keyword(Token.Sizeof, "sizeof", keyword);
      keyword = new Keyword(Token.Signed, "signed", keyword);
      keyword = new Keyword(Token.Short, "short", keyword);
      keywords['s' - 'a'] = keyword;
      // t
      keyword = new Keyword(Token.Typename, "typename");
      keyword = new Keyword(Token.Template, "template", keyword);
      keyword = new Keyword(Token.Typedef, "typedef", keyword);
      keywords['t' - 'a'] = keyword;
      // u
      keyword = new Keyword(Token.Unsigned, "unsigned");
      keyword = new Keyword(Token.Union, "union", keyword);
      keywords['u' - 'a'] = keyword;
      // v
      keyword = new Keyword(Token.Volatile, "volatile");
      keyword = new Keyword(Token.Void, "void", keyword);
      keywords['v' - 'a'] = keyword;
      // w
      keyword = new Keyword(Token.While, "while");
      keywords['w' - 'a'] = keyword;

      return keywords;
    }

    internal static Keyword/*?*/[] InitSpecKeywords() {
      Keyword/*?*/[] keywords = new Keyword/*?*/[26];
      Keyword keyword;

      keyword = new Keyword(Token.SpecAtomic, "atomic");
      keyword = new Keyword(Token.SpecAssume, "assume", keyword);
      keyword = new Keyword(Token.SpecAssert, "assert", keyword);
      keyword = new Keyword(Token.SpecAxiom, "axiom", keyword); 
      keywords['a' - 'a'] = keyword;

      keyword = new Keyword(Token.SpecDecreases, "decreases");
      keywords['d' - 'a'] = keyword;

      keyword = new Keyword(Token.SpecEnsures, "ensures");
      keywords['e' - 'a'] = keyword;

      keyword = new Keyword(Token.SpecGroup, "group");
      keyword = new Keyword(Token.SpecGhost, "ghost", keyword);
      keywords['g' - 'a'] = keyword;

      keyword = new Keyword(Token.SpecInvariant, "invariant");
      keywords['i' - 'a'] = keyword;

      keyword = new Keyword(Token.SpecLogic, "logic");
      keywords['l' - 'a'] = keyword;

      keyword = new Keyword(Token.SpecOut, "out");
      keywords['o' - 'a'] = keyword;

      keyword = new Keyword(Token.SpecRequires, "requires");
      keyword = new Keyword(Token.SpecReads, "reads", keyword);
      keywords['r' - 'a'] = keyword;

      keyword = new Keyword(Token.SpecUnwrapping, "unwrapping");
      keyword = new Keyword(Token.Unchecked, "unchecked", keyword);
      keywords['u' - 'a'] = keyword;

      keyword = new Keyword(Token.SpecWrites, "writes");
      keywords['w' - 'a'] = keyword;
      return keywords;
    }

    public static Keyword InitExtendedKeywords() {
      // This is a linked list of keywords starting with _
      // In the list, the keywords are sorted first by length, and then lexicographically.
      // So the constructor invocations must occur in the opposite order.
      Keyword keyword;
      // _
      //keyword = new Keyword(Token.Imaginary, "_Imaginary");
      //keyword = new Keyword(Token.Complex, "_Complex", keyword);
      keyword = new Keyword(Token.Bool, "_Bool");
      // keyword = new Keyword(Token.Specification, "_", keyword);

      return keyword;
    }

    public static Keyword InitMicrosoftKeywords() {
      // This is a linked list of keywords starting with __
      // In the list, the keywords are sorted first by length, and then lexicographically.
      // So the constructor invocations must occur in the opposite order.
      Keyword keyword = null;
      // __
      keyword = new Keyword(Token.Inline,        "__forceinline", keyword);
      keyword = new Keyword(Token.Unaligned, "__unaligned", keyword);
      keyword = new Keyword(Token.Fastcall,  "__fastcall", keyword);
      keyword = new Keyword(Token.Declspec,  "__declspec", keyword);
      keyword = new Keyword(Token.Stdcall,   "__stdcall", keyword);
      keyword = new Keyword(Token.AlignOf,   "__alignof", keyword);
      keyword = new Keyword(Token.Pragma,    "__pragma", keyword);
      keyword = new Keyword(Token.Inline,    "__inline", keyword);
      keyword = new Keyword(Token.Int64,     "__int64", keyword);
      keyword = new Keyword(Token.Int32,     "__int32", keyword);
      keyword = new Keyword(Token.Int16,     "__int16", keyword);
      keyword = new Keyword(Token.Cdecl,     "__cdecl", keyword);
      keyword = new Keyword(Token.Int8,      "__int8", keyword);
      keyword = new Keyword(Token.W64,       "__w64", keyword);

      return keyword;
    }

    internal static Keyword InitExtendedVccKeywords() {
      Keyword keyword = null;
      keyword         = new Keyword(Token.Result,           "\\result", keyword);
      keyword         = new Keyword(Token.Lambda,           "\\lambda", keyword);
      keyword         = new Keyword(Token.Forall,           "\\forall", keyword);
      keyword         = new Keyword(Token.Exists,           "\\exists", keyword);
      keyword         = new Keyword(Token.SetUnion,         "\\union", keyword);
      keyword         = new Keyword(Token.SetIntersection,  "\\inter", keyword);
      keyword         = new Keyword(Token.This,             "\\this", keyword);
      keyword         = new Keyword(Token.SetDifference,    "\\diff", keyword);
      keyword         = new Keyword(Token.Old,              "\\old", keyword);
      keyword         = new Keyword(Token.SetIn0,           "\\in0", keyword);
      keyword         = new Keyword(Token.SpecIs,           "\\is", keyword);
      keyword         = new Keyword(Token.SetIn,            "\\in", keyword);
      return keyword;
    }
  }
}
