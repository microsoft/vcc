using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Research.Vcc
{
  class VccOptionWrapper : Microsoft.Research.Vcc.Helper.Options
  {
    private readonly VccOptions options;

    public VccOptionWrapper(VccOptions options)
    {
      this.options = options;
    }

    public VccOptions VccOptions
    {
      get { return this.options; }
    }

    public override int DefExpansionLevel
    {
      get { return this.options.DefExpansionLevel; }
    }

    public override bool DeterminizeOutput
    {
      get { return this.options.DeterminizeOutput; }
    }

    public override bool OpsAsFunctions
    {
      get { return this.options.OpsAsFunctions; }
    }

    public override IEnumerable<string> PipeOperations
    {
      get { return this.options.PipeOperations; }
    }

    public override bool TerminationForAll
    {
      get { return this.options.TerminationForAll; }
    }

    public override bool TerminationForGhost
    {
      get { return this.options.TerminationForGhost; }
    }

    public override bool TerminationForPure
    {
      get { return this.options.TerminationForPure; }
    }

    public override bool YarraMode
    {
      get { return this.options.YarraMode; }
    }

    public override int DumpTriggers
    {
      get { return this.options.DumpTriggers; }
    }

    public override bool ExplicitTargetsGiven
    {
      get { return this.options.ExplicitTargetsGiven; }
    }

    public override bool PrintCEVModel
    {
      get { return this.options.PrintCEVModel; }
    }

    public override bool AggressivePruning
    {
      get { return this.options.AggressivePruning; }
    }

    public override IEnumerable<string> Functions
    {
      get { return this.options.Functions; }
    }

    public override IEnumerable<string> WeightOptions
    {
      get { return this.options.WeightOptions; }
    }
  }

}
