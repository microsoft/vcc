//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System.Collections.Generic;
using System.ComponentModel.Composition;
using System.ComponentModel.Composition.Hosting;

namespace Microsoft.Research.Vcc
{
  class PluginManager
  {
    [Import]
    public IEnumerable<Plugin> Plugins { get; set; }
    [Import]
    public IEnumerable<VCGenPlugin> VCGenPlugins { get; set; }

    public PluginManager(VccOptions options)
    {
      List<string> dirs;
      if (options.PluginOptions.TryGetValue("dir", out dirs)) {
        foreach (var d in dirs)
          AddPluginDirectory(d);
      }
    }

    readonly AggregateCatalog directories = new AggregateCatalog();
    public void AddPluginDirectory(string dir)
    {
      directories.Catalogs.Add(new DirectoryCatalog(dir));
    }

    public void Discover()
    {
      this.Compose();
    }

    private void Compose()
    {
      var container = new CompositionContainer(directories);
      var batch = new CompositionBatch();
      batch.AddPart(this);
      container.Compose(batch);
    }
  }
}
