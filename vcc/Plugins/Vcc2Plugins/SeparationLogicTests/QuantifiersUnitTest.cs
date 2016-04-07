using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Microsoft.Research.Vcc2;
using Microsoft.FSharp.Core;
using Microsoft.Z3;

namespace SymEvalTests
{
    [TestClass]
    public class QuantifiersUnitTest
    {
        private TermAst CreateQuantifedFormula1(TypeSafeContext z3)
        {
            var x = z3.MkConst("x", z3.MkIntType());
            var y = z3.MkConst("y", z3.MkIntType());
            var z = z3.MkConst("z", z3.MkIntType());
            return
              z3.MkForall(0, new TermAst[] { x, y }, new PatternAst[] { },
                z3.MkImplies(
                  z3.MkEq(x, y),
                  z3.MkExists(0, new TermAst[] { z }, new PatternAst[] { },
                    z3.MkNot(z3.MkEq(x, z)))));
        }

        private TermAst CreateQuantifedFormula2(TypeSafeContext z3)
        {
            var x2 = z3.MkBound(2, z3.MkIntType());
            var x1 = z3.MkBound(1, z3.MkIntType());
            var y = z3.MkBound(0, z3.MkIntType());
            var z = z3.MkBound(0, z3.MkIntType());
            return
              z3.MkForall(0, new PatternAst[] { }, new TypeAst[] { z3.MkIntType(), z3.MkIntType() }, new Symbol[] { z3.MkSymbol("x"), z3.MkSymbol("y") },
                z3.MkImplies(
                  z3.MkEq(x1, y),
                  z3.MkExists(0, new PatternAst[] { }, new TypeAst[] { z3.MkIntType() }, new Symbol[] { z3.MkSymbol("z") },
                    z3.MkNot(z3.MkEq(x2, z)))));
        }

        private TypeSafeContext CreateContext()
        {
            Config config = new Config();
            config.SetParamValue("MODEL", "true");
            TypeSafeContext z3 = new TypeSafeContext(config);
            config.Dispose();
            return z3;
        }

        private void Prove(TypeSafeContext z3, TermAst p)
        {
            Console.WriteLine("To PROVE: {0}", z3.ToString(z3.MkNot(p)));
            z3.AssertCnstr(z3.MkNot(p));
            z3.Display(System.Console.Out);
            TypeSafeModel model = null;
            LBool result = z3.CheckAndGetModel(ref model);
            switch (result)
            {
                case LBool.True:
                    Console.WriteLine("false");
                    model.Display(System.Console.Out);
                    model.Dispose();
                    break;
                case LBool.False:
                    Console.WriteLine("true");
                    break;
                case LBool.Undef:
                    Console.WriteLine("unknown");
                    break;
            }
        }

        [TestMethod]
        public void TestQuantifiers1()
        {
            var z3 = CreateContext();
            Prove(z3, CreateQuantifedFormula1(z3));
        }

        [TestMethod]
        public void TestQuantifiers2()
        {
            var z3 = CreateContext();
            Prove(z3, CreateQuantifedFormula2(z3));
        }
    }
}
