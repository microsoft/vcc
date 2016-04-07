using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Research.Vcc2;
using Microsoft.FSharp.Core;
using Microsoft.Z3;

namespace Tests
{
    class UnitTestRunner
    {
        static void RunCongruenceClosureUnitTest()
        {
            var test = new SymEvalTests.CongruenceClosureUnitTest();
            test.NelsonOppenExample1();
            test.ArithmeticExample1();
        }

        static void RunPureProverUnitTest()
        {
            var test = new SymEvalTests.PureProverUnitTest();
            test.TestTrueImpliesTrue();
            test.TestConstantsAddition1();
            test.TestConstantsAddition2();
            test.TestVariablesAddition();
            test.TestVariablesAdditionNoTypes();
        }

        static void RunTypeCodingUnitTest()
        {
            var test = new SymEvalTests.TypeCodingUnitTest();
            test.TestVariableTypeCoding();
            test.TestFunctionTypeCoding();
        }

        static void RunQuantifiersTests()
        {
            var test = new SymEvalTests.QuantifiersUnitTest();
            test.TestQuantifiers1();
            test.TestQuantifiers2();
        }

        static void Main(string[] args)
        {
            RunTypeCodingUnitTest();
            //RunPureProverUnitTest();
            //RunQuantifiersTests();
            //RunCongruenceClosureUnitTest();
        }
    }
}
