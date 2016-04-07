using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Research.Vcc
{

  public class Location : IEquatable<Location>, IComparable<Location>
  {
  
    private readonly int line;
    private readonly int column;
    private readonly string filename;

    public Location(string filename, int line, int column) {
      this.filename = filename;
      this.line = line;
      this.column = column;
    }

    public int Line {
      get {return this.line;}
    }

    public int Column {
      get { return this.column; }
    }

    public string FileName {
      get { return this.filename; }
    }

    public override bool Equals(object obj)
    {
      return this.Equals(obj as Location);
    }

    public bool Equals(Location other)
    {
      if (other == null) return false;
      return this.line == other.line && this.column == other.column && this.filename == other.filename;
    }

    public override int GetHashCode()
    {
      if (this.filename != null)
        return this.filename.GetHashCode() ^ this.line.GetHashCode() ^ this.column.GetHashCode();
      else
        return this.line.GetHashCode() ^ this.column.GetHashCode();
    }

    public int CompareTo(Location other)
    {
      if (other == null) return 1;
      int c = this.line.CompareTo(other.line);
      if (c != 0) return c;
      c = this.column.CompareTo(other.column);
      if (c!= 0) return c;
      return String.CompareOrdinal(this.filename, other.filename);
    }
  }

  public interface ILogger : IDisposable
  {
    void Log(string msg, LogKind kind);

    void LogFileSummary(string fileName, int errorCount, IEnumerable<Tuple<string, double>> timers);

    void LogMethodStart(string methodName);

    void LogMethodSummary(string methodName, Location loc, Outcome outcome, string additionalInfo, double time);

    void LogWithLocation(string code, string msg, Location loc, LogKind kind, bool isRelated);

    void LogProgress(string methodName, string phase, string progressMsg);

    void NewLine();
  }

  public enum LogKind
  {
    Message,
    Warning,
    Error,
  }

  public enum Outcome {
      Correct,
      Errors,
      TimedOut,
      OutOfMemory,
      Inconclusive,
      ReachedBound,
  }

  public sealed class Logger : ILogger
  {
    private static readonly Lazy<Logger> instance = new Lazy<Logger>(() => new Logger());

    private readonly List<ILogger> loggers = new List<ILogger>();

    private readonly HashSet<Tuple<Location, string, string>> reportedErrors = new HashSet<Tuple<Location, string, string>>();

    private Logger()
    {
    }

    public void NewLine()
    {
      this.DoForAll(logger => logger.NewLine());
    }

    public void Log(string msg, LogKind kind = LogKind.Message)
    {
      this.DoForAll(logger => logger.Log(msg, kind));
    }

    public void LogFileSummary(string fileName, int errorCount, IEnumerable<Tuple<string, double>> timers)
    {
      this.DoForAll(logger => logger.LogFileSummary(fileName, errorCount, timers));
    }

    public void LogWithLocation(string code, string msg, Location loc, LogKind kind, bool isRelated)
    {
      if (!isRelated) {
        var tup = Tuple.Create(loc, code, msg);
        if (reportedErrors.Contains(tup)) return;
        this.reportedErrors.Add(tup);
      }

      this.DoForAll(logger => logger.LogWithLocation(code, msg, loc, kind, isRelated));
    }

    public void LogMethodStart(string methodName)
    {
      this.DoForAll(logger => logger.LogMethodStart(methodName));
    }

    public void LogMethodSummary(string methodName, Location loc, Outcome outcome, string additionalInfo, double time)
    {
      this.DoForAll(logger => logger.LogMethodSummary(methodName, loc, outcome, additionalInfo, time));
    }

    public void LogProgress(string methodName, string phase, string progressMsg)
    {
      this.DoForAll(logger => logger.LogProgress(methodName, phase, progressMsg));
    }

    public void ResetReportedErrors()
    {
      this.reportedErrors.Clear();
    }

    public void Register(ILogger logger)
    {
      this.loggers.Add(logger);
    }

    public void Unregister(ILogger logger)
    {
      this.loggers.Remove(logger);
    }

    public void Log(string format, params object[] args)
    {
      this.Log(String.Format(format, args));
    }

    public void Error(string msg)
    {
      this.Log(msg, LogKind.Error);
    }

    public void Error(string format, params object[] args)
    {
      this.Log(String.Format(format, args), LogKind.Error);
    }

    public void Warning(string msg)
    {
      this.Log(msg, LogKind.Warning);
    }

    public void Warning(string format, params object[] args)
    {
      this.Log(String.Format(format, args), LogKind.Warning);
    }

    private void DoForAll(Action<ILogger> logAction)
    {
      foreach (var logger in this.loggers) {
        logAction(logger);
      }
    }

    public void Dispose()
    {
      this.DoForAll(logger => logger.Dispose());
    }

    public static Logger Instance
    {
      get { return instance.Value; }
    }
  }
}