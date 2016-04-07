using System;
using System.Text;
using System.Collections.Generic;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Microsoft.Research.Vcc2;
using Microsoft.FSharp.Core;

namespace SymEvalTests
{
    [TestClass]
    public class TypeCodingUnitTest
    {
        private String doVariableTypeCoding(String type)
        {
            return TypeCoding.encodeVarType((TypeCoding.decodeVarType(type))._Some1);
        }

        private String doFunctionTypeCoding(String type)
        {
            var decoded = (TypeCoding.decodeFunctionType(type))._Some1;
            return TypeCoding.encodeFunctionType(decoded.Item1, decoded.Item2);
        }

        [TestMethod]
        public void TestVariableTypeCoding()
        {
            Assert.AreEqual("bool:", doVariableTypeCoding("bool"));
            Assert.AreEqual("i1:", doVariableTypeCoding("i1"));
            Assert.AreEqual("i4:", doVariableTypeCoding("i4"));
            Assert.AreEqual("i8:", doVariableTypeCoding("i8"));
            Assert.AreEqual("u1:", doVariableTypeCoding("u1"));
            Assert.AreEqual("u2:", doVariableTypeCoding("u2"));
            Assert.AreEqual("u4:", doVariableTypeCoding("u4"));
            Assert.AreEqual("u8:", doVariableTypeCoding("u8"));
            Assert.AreEqual("f4:", doVariableTypeCoding("f4"));
            Assert.AreEqual("f8:", doVariableTypeCoding("f8"));
            Assert.AreEqual("void:", doVariableTypeCoding("void"));
            Assert.AreEqual("$typeid_t:", doVariableTypeCoding("$typeid_t"));
            Assert.AreEqual("*i4:", doVariableTypeCoding("*i4"));
            Assert.AreEqual("**u8:", doVariableTypeCoding("**u8"));
            Assert.AreEqual("[10]i4:", doVariableTypeCoding("[10]i4"));
            Assert.AreEqual("$map_t[u4]bool:", doVariableTypeCoding("$map_t[u4]bool"));
            Assert.AreEqual("^A:", doVariableTypeCoding("^A"));
        }

        [TestMethod]
        public void TestFunctionTypeCoding()
        {
            Assert.AreEqual("()void", doFunctionTypeCoding("()void"));
            Assert.AreEqual("(i4)bool", doFunctionTypeCoding("(i4)bool"));
            Assert.AreEqual("(bool,bool)u4", doFunctionTypeCoding("(bool,bool)u4"));
        }
    }
}
