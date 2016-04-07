using System;
using System.Text;
using System.Collections.Generic;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Microsoft.Research.Vcc2;
using Microsoft.FSharp.Core;

namespace SymEvalTests
{
    [TestClass]
    public class PureProverUnitTest
    {
        private SepProver.out_form mkBool(string b)
        {
            return SepProver.out_form.Pred("bool",
              Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.String(b),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty));
        }

        private SepProver.out_term mkInt(string i)
        {
            return SepProver.out_term.Fun("int",
              Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.String(i),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty));
        }

        [TestMethod]
        public void TestTrueImpliesTrue()
        {
            bool result = PureProver.implies(mkBool("true"), mkBool("true"));
            Assert.AreEqual(true, result);
        }

        [TestMethod]
        public void TestConstantsAddition1()
        {
            var form = SepProver.out_form.EQ(
              SepProver.out_term.Fun("+",
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                  mkInt("1"),
                  Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                  mkInt("1"),
                  Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty))),
              mkInt("2"));
            bool result = PureProver.implies(mkBool("true"), form);
            Assert.AreEqual(true, result);
        }

        [TestMethod]
        public void TestConstantsAddition2()
        {
            var form = SepProver.out_form.Pred("==",
              Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                SepProver.out_term.Fun("+",
                  Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                    mkInt("1"),
                    Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                    mkInt("1"),
                    Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty))),
              Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                mkInt("2"),
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty)));
            bool result = PureProver.implies(mkBool("true"), form);
            Assert.AreEqual(true, result);
        }

        [TestMethod]
        public void TestVariablesAddition()
        {
            var addForm = SepProver.out_form.EQ(
              SepProver.out_term.Fun("+",
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                  SepProver.out_term.PVar("i4:x"),
                  Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                  SepProver.out_term.PVar("i4:y"),
                  Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty))),
              SepProver.out_term.PVar("i4:z"));
            var valForm = SepProver.out_form.And(
              SepProver.out_form.EQ(SepProver.out_term.PVar("i4:x"), mkInt("1")),
              SepProver.out_form.And(
                SepProver.out_form.EQ(SepProver.out_term.PVar("i4:y"), mkInt("1")),
                SepProver.out_form.EQ(SepProver.out_term.PVar("i4:z"), mkInt("2"))));
            var form = SepProver.out_form.And(addForm, valForm);
            bool result = PureProver.implies(mkBool("true"), form);
            Assert.AreEqual(true, result);
        }

        [TestMethod]
        public void TestVariablesAdditionNoTypes()
        {
            var addForm = SepProver.out_form.EQ(
              SepProver.out_term.Fun("+",
                Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                  SepProver.out_term.PVar("x"),
                  Microsoft.FSharp.Collections.List<SepProver.out_term>.Cons(
                  SepProver.out_term.PVar("y"),
                  Microsoft.FSharp.Collections.List<SepProver.out_term>.Empty))),
              SepProver.out_term.PVar("z"));
            var valForm = SepProver.out_form.And(
              SepProver.out_form.EQ(SepProver.out_term.PVar("x"), mkInt("1")),
              SepProver.out_form.And(
                SepProver.out_form.EQ(SepProver.out_term.PVar("y"), mkInt("1")),
                SepProver.out_form.EQ(SepProver.out_term.PVar("z"), mkInt("2"))));
            var form = SepProver.out_form.And(addForm, valForm);
            bool result = PureProver.implies(mkBool("true"), form);
            Assert.AreEqual(true, result);
        }
    }
}
