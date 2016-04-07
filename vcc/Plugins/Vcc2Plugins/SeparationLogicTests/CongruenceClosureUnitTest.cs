using System;
using System.Text;
using System.Collections.Generic;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Microsoft.Research.Vcc2;
using Microsoft.FSharp.Core;

namespace SymEvalTests
{
    [TestClass]
    public class CongruenceClosureUnitTest
    {
        [TestMethod]
        public void NelsonOppenExample1()
        {
            SepProver.out_form f = 
                SepProver.out_form.Pred("==",
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.Fun("f", 
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.String("(i4,i4)i4"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.PVar("i4:a"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.PVar("i4:b"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty)))),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.PVar("i4:a"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty)));

            Microsoft.FSharp.Collections.List<SepProver.out_term> ts =
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.PVar("i4:a"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.PVar("i4:b"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.Fun("f", 
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.String("(i4,i4)i4"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.PVar("i4:a"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.PVar("i4:b"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty)))),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.Fun("f", 
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.String("(i4,i4)i4"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.Fun("f", 
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.String("(i4,i4)i4"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.PVar("i4:a"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.PVar("i4:b"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty)))),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.PVar("i4:b"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty)))),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty))));

            PureProver.debug = true;
            var result = PureProver.congruence_closure(f, ts);
        }

        [TestMethod]
        public void ArithmeticExample1()
        {
            SepProver.out_form f =
                SepProver.out_form.TT;

            Microsoft.FSharp.Collections.List<SepProver.out_term> ts =
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.Fun("+", 
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.PVar("i4:x"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.Fun("*", 
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.Fun("int", 
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.String("2"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty)),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.Fun("int", 
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.String("4"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty)),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty))),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty))),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.Fun("+",
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.Fun("int", 
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.String("8"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty)),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.PVar("i4:x"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty))),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty));

            PureProver.debug = true;
            var result = PureProver.congruence_closure(f, ts);
        }

    }
}
