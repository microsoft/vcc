//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System.Collections.Generic;
using Microsoft.Cci;

namespace Microsoft.Research.Vcc
{
  public static class VisitorHelper
  {
    public class DeferredToken
    {
      private readonly IEnumerable<ILocation> locations;

      public DeferredToken(IEnumerable<ILocation> locations) {
        this.locations = locations;
      }

      public Token GetToken()
      {
          foreach (ILocation loc in locations)
          {
              IPrimarySourceLocation/*?*/ sloc = loc as IPrimarySourceLocation;
              if (sloc != null) return new SourceLocationWrapper(sloc, sloc, () => sloc.Source);
              IDerivedSourceLocation/*?*/ dloc = loc as IDerivedSourceLocation;
              if (dloc != null)
              {
                  IPrimarySourceLocation fLoc = null, lLoc = null;
                  foreach (IPrimarySourceLocation ploc in dloc.PrimarySourceLocations)
                  {
                      if (fLoc == null) fLoc = ploc;
                      lLoc = ploc;
                  }
          
                  if (fLoc != null)
                  {
                      return new SourceLocationWrapper(fLoc, lLoc, () => dloc.Source);
                  }
              }
          }

          return Token.NoToken;
      }
    }

    public static Token GetTokenFor(IEnumerable<ILocation> locations)
    {
      if (IteratorHelper.EnumerableIsEmpty(locations)) return Token.NoToken;
      return LazyToken.Create(new DeferredToken(locations).GetToken);
    }

    public static ISourceLocation LocationFromToken(Token tok)
    {
      SourceLocationWrapper wrap = tok as SourceLocationWrapper;
      if (wrap != null) return wrap.firstSourceLocation;
      ForwardingToken fwd = tok as ForwardingToken;
      if (fwd != null) return LocationFromToken(fwd.WrappedToken);
      LazyToken lazyToken = tok as LazyToken;
      if (lazyToken != null) return LocationFromToken(lazyToken.DelayedToken);
      return SourceDummy.SourceLocation;
    }
  }
}
