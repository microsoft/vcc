//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Text;

// Partial implementation of printf
namespace Microsoft.Research.Vcc {
  public static unsafe partial class Runtime {
    static int width;
    static int width2;
    public static int printf(sbyte* _Format, __arglist) {
      StringBuilder output = new StringBuilder();
      ArgIterator ai = new ArgIterator(__arglist);  
      string format = new string(_Format);
      int i = 0, n = format.Length;

      bool after_parse_width = false;

      while (i < n) {
        char c = format[i];
        if (c == '%' || after_parse_width ) {
          if (i + 1 <= n) {
            i++;
            char next = format[i];
            switch (next) {
              // ignore width for now. 
              case 'd': i++; output.AppendFormat("{0}", TypedReference.ToObject(ai.GetNextArg())); break;
              case 'c': i++; output.Append(getChar(ai)); break;
              case 'x': i++; output.AppendFormat("{0}", TypedReference.ToObject(ai.GetNextArg())); break;
              case 's': i++; output.Append(getString(ai)); break;
              case 'f': i++; output.AppendFormat("{0}", TypedReference.ToObject(ai.GetNextArg())); break;
              case 'l': i++;
                if (format[i] == 'f') {
                  i++;
                  output.AppendFormat("{0}", TypedReference.ToObject(ai.GetNextArg())); 
                } 
                else {
                  output.AppendFormat("{0}", TypedReference.ToObject(ai.GetNextArg()));
                }
                break;
              default: 
                if (Char.IsDigit(next)) {
                  StringBuilder sb = new StringBuilder();
                  while (i < n && Char.IsDigit(format[i])) {
                    sb.Append(format[i]);
                    i++;
                  }
                  width = int.Parse(sb.ToString());
                  width2 = 0;
                  if (format[i] == '.') {
                    i++;
                    StringBuilder sb2 = new StringBuilder();
                    while (i < n && Char.IsDigit(format[i])) {
                      sb2.Append(format[i]);
                      i++;
                    }
                    width2 = int.Parse(sb2.ToString());
                  }
                }
                break;
            }
          } 
          else break; // break the loop
        } 
        else if (c == '\\') {
          // it is impossible for the next char to be out of bound.
          i++;
          char escaped = format[i];
          output.Append(c);
          output.Append(escaped); 
          i ++;
        } 
        else {
          output.Append(c);
          i++;
        }
      }
      Console.Write(output.ToString());
      return 0;
    }

    private static int getInt(ArgIterator ai) {
      TypedReference tr = ai.GetNextArg();
      Type t = __reftype(tr);
      if (t == typeof(int)) {
        return (int)(__refvalue(tr, int));
      }
      throw new FormatException("expecting an integer");
    }

    private static char getChar(ArgIterator ai) {
      TypedReference tr = ai.GetNextArg();
      Type t = __reftype(tr);
      if (t == typeof(sbyte)) {
        return (char)(__refvalue(tr, sbyte));
      }
      throw new FormatException("expecting a char");
    }

    private unsafe static string getString(ArgIterator ai) {
      TypedReference tr = ai.GetNextArg();
      Type t = __reftype(tr);
      if (t == typeof(sbyte*)) {
        return new String(__refvalue(tr, sbyte*));
      }
      throw new FormatException("expecting a string");
    }

    private static double getFloat(ArgIterator ai) {
      TypedReference tr = ai.GetNextArg();
      Type t = __reftype(tr);
      if (t == typeof(double)) {
        return __refvalue( tr, double);
      }
      throw new FormatException("expecting a double");
    }
  }
}
