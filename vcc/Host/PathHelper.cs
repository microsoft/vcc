//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------

using System;
using System.IO;

namespace Microsoft.Research.Vcc
{
  static class PathHelper
  {
    private static string Quote(string path)
    {
      return path.Contains(" ") ? "\"" + path + "\"" : path;
    }

    private static readonly Lazy<DirectoryInfo> cachedVccHeaderDirectory = new Lazy<DirectoryInfo>(
      () =>
        {
          var dir = BinariesDirectory;
          while (dir != null && dir.Exists)
          {
            foreach (var subdir in dir.GetDirectories("headers"))
            {
              if (subdir.GetFiles("vcc.h").Length > 0)
                return subdir;
            }
            dir = dir.Parent;
          }
          return null;
        }
      );

    public static string/*?*/ GetVccHeaderDir(bool quoteResult) {

      if (cachedVccHeaderDirectory.Value == null) return null;

      if (quoteResult)
        return Quote(cachedVccHeaderDirectory.Value.FullName);
      
      return cachedVccHeaderDirectory.Value.FullName;
    }

    private static DirectoryInfo BinariesDirectory
    {
      get { return new FileInfo(typeof(PathHelper).Assembly.Location).Directory; }
    }

    public static string InspectorOption
    {
      get
      {        
        return "/proverOpt:INSPECTOR=" + Quote(Path.Combine(BinariesDirectory.FullName, "Z3Inspector.exe"));
      }
    }

    public static string/*?*/ PluginDir {
      get {
        GetVccHeaderDir(false);
        if (cachedVccHeaderDirectory == null || cachedVccHeaderDirectory.Value.Parent == null) return null;
        DirectoryInfo[] candidates = cachedVccHeaderDirectory.Value.Parent.GetDirectories("Plugins");
        if (candidates.Length > 0) return candidates[0].FullName;
        return null;
      }
    }

    public static string PreludePath(string basename)
    {
      if (basename.IndexOf(Path.DirectorySeparatorChar) >= 0)
        return basename;
      
      string headersDir = GetVccHeaderDir(false);
      if (headersDir != null) return Path.Combine(headersDir, basename);
      return null;
    }
  }
}
