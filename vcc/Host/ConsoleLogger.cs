using System;
using System.Collections.Generic;
using System.Text;
using System.IO;

namespace Microsoft.Research.Vcc
{
  internal class ConsoleLogger : ILogger
  {
    private static readonly Lazy<ILogger> instance = new Lazy<ILogger>(() => new ConsoleLogger());

    public static ILogger Instance
    {
      get { return instance.Value; }
    }

    protected bool atStartOfLine = true;

    protected ConsoleLogger()
    {
    }

    public void Log(string msg, LogKind kind)
    {
      if (!atStartOfLine) {
        Console.WriteLine("...");
        atStartOfLine = true;
      }
      
      var savedColor = Console.ForegroundColor;

      switch (kind) {
        case LogKind.Error:
          Console.ForegroundColor = ConsoleColor.Red;
          break;
        case LogKind.Warning:
          Console.ForegroundColor = ConsoleColor.Yellow;
          break;
      }

      Console.WriteLine(msg);
      Console.ForegroundColor = savedColor;
    }

    public void NewLine()
    {
      this.Log("", LogKind.Message);
    }

    public void Dispose()
    {
      Console.Out.Flush();
    }

    public virtual void LogFileSummary(string fileName, int errorCount, IEnumerable<Tuple<string, double>> timers)
    {
      if (timers != null) {
        Console.Write("Time: ");
        bool first = true;
        foreach (var entry in timers) {
          if (first) {
            first = false;
          } else {
            Console.Write(", ");
          }
          Console.Write("{0:0.00}s {1}", entry.Item2, entry.Item1);
        }
        Console.WriteLine();
      }

      if (errorCount > 0) {
        this.Log(String.Format("Verification errors in {0} function(s)", errorCount), LogKind.Error);
      }
    }

    public virtual void LogWithLocation(string code, string msg, Location loc, LogKind kind, bool isRelated)
    {
      StringBuilder logMsg = new StringBuilder();
      logMsg.Append(loc.FileName);
      if (loc.Column >= 0) {
        logMsg.Append(String.Format("({0},{1})", loc.Line, loc.Column));
      } else {
        logMsg.Append(String.Format("({0})", loc.Line));
      }

      logMsg.Append(" : ");

      switch (kind) {
        case LogKind.Error:
          logMsg.Append("error");
          break;
        case LogKind.Warning:
          logMsg.Append("warning");
          break;
        case LogKind.Message:
          logMsg.Append("message");
          break;
      }

      logMsg.Append(' ');
      if (code != null) logMsg.Append(code);
      logMsg.Append(": ").Append(msg);
      this.Log(logMsg.ToString(), kind);
    }

    public virtual void LogMethodSummary(string methodName, Location loc, Outcome outcome, string additionalInfo, double time)
    {
      string outcomeStr = additionalInfo ?? OutcomeToDescription(outcome);
      if (this.atStartOfLine) {
        Console.WriteLine("Verification of {0} {1}. [{2:0.00}s]", methodName, outcomeStr, time);
      } else {
        Console.WriteLine("{0}. [{1:0.00}]", outcomeStr, time);
      }

      this.atStartOfLine = true;
    }

    protected static string OutcomeToDescription(Outcome outcome)
    {
      switch (outcome) {
        case Outcome.Correct:
          return "succeeded";
        case Outcome.Inconclusive:
          return "was inconclusive";
        case Outcome.TimedOut:
          return "timed out";
        case Outcome.Errors:
          return "failed";
        case Outcome.OutOfMemory:
          return "ran out of memory";
        default:
          return "returned an unknown result";
      }
    }

    public virtual void LogMethodStart(string methodName)
    {
      Console.Write("Verification of {0} ", methodName);
      Console.Out.Flush();
      this.atStartOfLine = false;
    }

    public virtual void LogProgress(string methodName, string phase, string progressMsg)
    {
      if (!this.atStartOfLine) {
          try {
              Console.CursorLeft = 0;
          } catch (IOException)
          {
              Console.WriteLine();
          }
      }

      Console.Write("Verification of {0} - {1} {2} ", methodName, phase, progressMsg);
      Console.Out.Flush();
      this.atStartOfLine = false;
    }
  }

  internal class ConsoleLoggerForTestRun : ConsoleLogger
  {
    public override void LogMethodStart(string methodName)
    {
    }

    public override void LogProgress(string methodName, string phase, string progressMsg)
    {
    }

    public override void LogFileSummary(string fileName, int errorCount, IEnumerable<Tuple<string, double>> timers)
    {
    }

    public override void LogWithLocation(string code, string msg, Location loc, LogKind kind, bool isRelated)
    {
      Location normalizedLoc;
      if (loc.FileName != null && loc.FileName.EndsWith("vccp.h")) {
        normalizedLoc = new Location("vccp.h", 0, 0);
      } else {
        normalizedLoc = new Location("testcase", loc.Line, loc.Column);
      }

      string normalizedCode;

      if (code == null) {
        normalizedCode = null;
      } else if (code.StartsWith("VC")) {
        int no = Int32.Parse(code.Substring(2));
        if (no < 8000) {
          normalizedCode = "VC0000";
        } else {
          normalizedCode = String.Format("VC{0:0000}", no);
        }
      } else {
        normalizedCode = code;
      }

      base.LogWithLocation(normalizedCode, msg, normalizedLoc, kind, isRelated);
    }

    public override void LogMethodSummary(string methodName, Location loc, Outcome outcome, string additionalInfo, double time)
    {
      string outcomeStr = additionalInfo ?? OutcomeToDescription(outcome);
      Console.WriteLine("Verification of {0} {1}.", methodName, outcomeStr);
      this.atStartOfLine = true;
    }
  }
}
