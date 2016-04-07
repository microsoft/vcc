using System;
using System.Collections.Generic;
using System.Text;
using System.Xml;
using System.IO;
using System.Xml.Linq;

namespace Microsoft.Research.Vcc 
{
    class XmlLogger : ILogger
    {

        private readonly XmlWriter xwr;

        private bool inVerificatioBlock;

        public const string LogFileNamespace = "http://vcc.codeplex.com/logfile/1.0";

        public XmlLogger(Stream os)
        {
            System.Text.UTF8Encoding encoding = new UTF8Encoding(false);
            XmlWriterSettings settings = 
                new XmlWriterSettings
                    {
                        CloseOutput = true, Indent = true, IndentChars = "  ", Encoding = encoding
                    };
            this.xwr = XmlWriter.Create(os, settings);
            this.xwr.WriteStartDocument();
            this.xwr.WriteStartElement("logfile", LogFileNamespace);
            this.xwr.WriteElementString("timestamp", LogFileNamespace, GetTimestamp());
        }

        #region ILogger Members

        public void Log(string msg, LogKind kind)
        {
            this.xwr.WriteStartElement("message", LogFileNamespace);
            switch (kind)
            {
                case LogKind.Error:
                    this.xwr.WriteAttributeString("kind", "error");
                    break;
                case LogKind.Warning:
                    this.xwr.WriteAttributeString("kind", "warning");
                    break;
            }
            
            this.xwr.WriteString(msg);
            this.xwr.WriteEndElement();
        }

        public void LogFileSummary(string fileName, int errorCount, IEnumerable<Tuple<string, double>> timers)
        {
            this.CloseVerificationBlockIfNecessary();
            this.xwr.WriteStartElement("summary", LogFileNamespace);
            this.xwr.WriteAttributeString("file", fileName);
            this.xwr.WriteElementString("errors", LogFileNamespace, errorCount.ToString());
            if (timers != null)
            {
                this.xwr.WriteStartElement("timers", LogFileNamespace);
                foreach (var timer in timers)
                {
                    this.xwr.WriteStartElement("timer", LogFileNamespace);
                    this.xwr.WriteAttributeString("name", timer.Item1);
                    this.xwr.WriteAttributeString("value", timer.Item2.ToString("0.00"));
                    this.xwr.WriteEndElement();
                }
                this.xwr.WriteEndElement();
            }
            this.xwr.WriteEndElement();
        }

        public void LogMethodStart(string methodName)
        {
        }

        public void LogMethodSummary(string methodName, Location loc, Outcome outcome, string additionalInfo, double time)
        {
            this.CloseVerificationBlockIfNecessary();
            this.xwr.WriteStartElement("verification", LogFileNamespace);
            this.xwr.WriteAttributeString("method", methodName);
            this.xwr.WriteAttributeString("result", OutcomeToString(outcome));
            this.xwr.WriteAttributeString("time", time.ToString("0.00"));
            this.WriteLocation(loc);
            if (!String.IsNullOrEmpty(additionalInfo))
            {
                this.xwr.WriteElementString("info", LogFileNamespace, additionalInfo);
            }

            this.inVerificatioBlock = true;
        }

        public void LogWithLocation(string code, string msg, Location loc, LogKind kind, bool isRelated)
        {
            this.xwr.WriteStartElement("message", LogFileNamespace);
            switch (kind) {
                case LogKind.Error:
                    this.xwr.WriteAttributeString("kind", "error");
                    break;
                case LogKind.Warning:
                    this.xwr.WriteAttributeString("kind", "warning");
                    break;
            }

            if (isRelated)
            {
                this.xwr.WriteAttributeString("isRelated", "true");
            }

            if (!String.IsNullOrEmpty(code))
            {
                this.xwr.WriteAttributeString("code", code);
            }

            this.WriteLocation(loc);
            this.xwr.WriteString(msg);
            this.xwr.WriteEndElement();            
        }

        public void LogProgress(string methodName, string phase, string progressMsg)
        {
        }

        public void NewLine()
        {
        }

        #endregion

        #region IDisposable Members

        public void Dispose()
        {
            this.CloseVerificationBlockIfNecessary();
            this.xwr.WriteElementString("timestamp", LogFileNamespace, GetTimestamp());
            this.xwr.WriteEndDocument();
            this.xwr.Close();
        }

        #endregion

        private static string GetTimestamp()
        {
            XElement now = new XElement("Now", DateTime.Now);
            return now.Value;
        }

        private static string OutcomeToString(Outcome outcome)
        {
            switch (outcome)
            {
                case Outcome.Correct:
                    return "success";
                case Outcome.Errors:
                    return "errors";
                case Outcome.Inconclusive:
                    return "inconclusive";
                case Outcome.OutOfMemory:
                    return "out of memory";
                case Outcome.ReachedBound:
                    return "bound reached";
                case Outcome.TimedOut:
                    return "timeout";
                default:
                    throw new ArgumentException();
            }
        }

        private void CloseVerificationBlockIfNecessary()
        {
            if (this.inVerificatioBlock)
            {
                this.xwr.WriteEndElement();
                this.inVerificatioBlock = false;
            }
        }

        private void WriteLocation(Location loc)
        {
            this.xwr.WriteStartElement("location", LogFileNamespace);
            this.xwr.WriteAttributeString("file", loc.FileName);
            this.xwr.WriteAttributeString("line", loc.Line.ToString());
            this.xwr.WriteAttributeString("column", loc.Column.ToString());
            this.xwr.WriteEndElement();
        }
    }
}
