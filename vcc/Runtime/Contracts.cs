//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System.Collections.Generic;

namespace System.Diagnostics.Contracts
{

  public static partial class CodeContract
  {
    public class Pair<A, B>
    {
      public A a;
      public B b;
    }

    public static bool InLambda<V>(bool cond, V res) {
      return true;
    }

    public static Map<K, V> Lambda<K, V>(Predicate<K> P) {
      return null;
    }

    public abstract class Map<Key, Value>
    {
      abstract public Value this[Key k] {
        get;
        set;
      }
    }

    public abstract class BigInt
    {
      Int64 dummy; // ensures that sizeof(BigInt) == 8
      // get rid of the warning about the variable above
      private void Dummy() { dummy++; }

      public static bool operator ==(BigInt b1, BigInt b2)
      {
        throw new NotImplementedException();
      }

      public static bool operator !=(BigInt b1, BigInt b2)
      {
        throw new NotImplementedException();
      }

      public static bool operator <(BigInt b1, BigInt b2)
      {
        throw new NotImplementedException();
      }

      public static bool operator >(BigInt b1, BigInt b2)
      {
        throw new NotImplementedException();
      }

      public static bool operator <=(BigInt b1, BigInt b2)
      {
        throw new NotImplementedException();
      }

      public static bool operator >=(BigInt b1, BigInt b2)
      {
        throw new NotImplementedException();
      }

      public static implicit operator BigInt(BigNat n)
      {
        throw new NotImplementedException();
      }
    
      public static implicit operator BigInt(ushort n) {
        throw new NotImplementedException();
      }

      public static implicit operator BigInt(short n) {
        throw new NotImplementedException();
      }

      public static implicit operator BigInt(int n)
      {
        throw new NotImplementedException();
      }

      public static implicit operator BigInt(uint n)
      {
        throw new NotImplementedException();
      }

      public static implicit operator BigInt(long n)
      {
        throw new NotImplementedException();
      }

      public static implicit operator BigInt(ulong n)
      {
        throw new NotImplementedException();
      }

      public static implicit operator BigInt(byte n)
      {
        throw new NotImplementedException();
      }

      public static implicit operator BigInt(sbyte n)
      {
        throw new NotImplementedException();
      }

      public static explicit operator int(BigInt n)
      {
        throw new NotImplementedException();
      }

      public static explicit operator uint(BigInt n)
      {
        throw new NotImplementedException();
      }

      public static explicit operator long(BigInt n)
      {
        throw new NotImplementedException();
      }

      public static explicit operator ulong(BigInt n)
      {
        throw new NotImplementedException();
      }

      public static explicit operator byte(BigInt n)
      {
        throw new NotImplementedException();
      }

      public static explicit operator sbyte(BigInt n)
      {
        throw new NotImplementedException();
      }

      public static BigInt operator +(BigInt b1, BigInt b2)
      {
        throw new NotImplementedException();
      }

      public static BigInt operator -(BigInt b1, BigInt b2)
      {
        throw new NotImplementedException();
      }

      public static BigInt operator *(BigInt b1, BigInt b2)
      {
        throw new NotImplementedException();
      }

      public static BigInt operator /(BigInt b1, BigInt b2)
      {
        throw new NotImplementedException();
      }

      public static BigInt operator %(BigInt b1, BigInt b2)
      {
        throw new NotImplementedException();
      }

      public static BigInt operator <<(BigInt b1, int b2)
      {
        throw new NotImplementedException();
      }
      public static BigInt operator >>(BigInt b1, int b2)
      {
        throw new NotImplementedException();
      }

      public static BigInt operator &(BigInt b1, BigInt b2)
      {
        throw new NotImplementedException();
      }
      public static BigInt operator |(BigInt b1, BigInt b2)
      {
        throw new NotImplementedException();
      }
      public static BigInt operator ^(BigInt b1, BigInt b2)
      {
        throw new NotImplementedException();
      }
      public static BigInt operator ~(BigInt b1)
      {
        throw new NotImplementedException();
      }

      public static BigInt operator -(BigInt b)
      {
        throw new NotImplementedException();
      }

      public override int GetHashCode()
      {
        throw new NotImplementedException();
      }

      public override bool Equals(object obj)
      {
        throw new NotImplementedException();
      }
    }

    public abstract class BigNat
    {
      UInt64 dummy; // ensures that sizeof(BigNat) == 8
      // get rid of the warning about the variable above
      private void Dummy() { dummy++; }

      public static bool operator ==(BigNat b1, BigNat b2)
      {
        throw new NotImplementedException();
      }

      public static bool operator !=(BigNat b1, BigNat b2)
      {
        throw new NotImplementedException();
      }

      public static bool operator <(BigNat b1, BigNat b2)
      {
        throw new NotImplementedException();
      }

      public static bool operator >(BigNat b1, BigNat b2)
      {
        throw new NotImplementedException();
      }

      public static bool operator <=(BigNat b1, BigNat b2)
      {
        throw new NotImplementedException();
      }

      public static bool operator >=(BigNat b1, BigNat b2)
      {
        throw new NotImplementedException();
      }

      public static explicit operator BigNat(BigInt n)
      {
        throw new NotImplementedException();
      }

      public static explicit operator BigNat(int n)
      {
        throw new NotImplementedException();
      }

      public static implicit operator BigNat(uint n)
      {
        throw new NotImplementedException();
      }

      public static explicit operator BigNat(long n)
      {
        throw new NotImplementedException();
      }

      public static implicit operator BigNat(ulong n)
      {
        throw new NotImplementedException();
      }

      public static implicit operator BigNat(byte n)
      {
        throw new NotImplementedException();
      }

      public static explicit operator BigNat(sbyte n)
      {
        throw new NotImplementedException();
      }

      public static explicit operator int(BigNat n)
      {
        throw new NotImplementedException();
      }

      public static explicit operator uint(BigNat n)
      {
        throw new NotImplementedException();
      }

      public static explicit operator long(BigNat n)
      {
        throw new NotImplementedException();
      }

      public static explicit operator ulong(BigNat n)
      {
        throw new NotImplementedException();
      }

      public static explicit operator byte(BigNat n)
      {
        throw new NotImplementedException();
      }

      public static explicit operator sbyte(BigNat n)
      {
        throw new NotImplementedException();
      }

      public static BigNat operator +(BigNat b1, BigNat b2)
      {
        throw new NotImplementedException();
      }

      public static BigNat operator -(BigNat b1, BigNat b2)
      {
        throw new NotImplementedException();
      }

      public static BigNat operator *(BigNat b1, BigNat b2)
      {
        throw new NotImplementedException();
      }

      public static BigNat operator /(BigNat b1, BigNat b2)
      {
        throw new NotImplementedException();
      }

      public static BigNat operator %(BigNat b1, BigNat b2)
      {
        throw new NotImplementedException();
      }

      public static BigNat operator <<(BigNat b1, int b2)
      {
        throw new NotImplementedException();
      }
      public static BigNat operator >>(BigNat b1, int b2)
      {
        throw new NotImplementedException();
      }

      public static BigNat operator &(BigNat b1, BigNat b2)
      {
        throw new NotImplementedException();
      }
      public static BigNat operator |(BigNat b1, BigNat b2)
      {
        throw new NotImplementedException();
      }
      public static BigNat operator ^(BigNat b1, BigNat b2)
      {
        throw new NotImplementedException();
      }
      public static BigNat operator ~(BigNat b1)
      {
        throw new NotImplementedException();
      }

      public override int GetHashCode()
      {
        throw new NotImplementedException();
      }

      public override bool Equals(object obj)
      {
        throw new NotImplementedException();
      }
    }

    unsafe public struct TypedPtr
    {
      void* ptr;

      public TypedPtr(void* p) {
        ptr = p;
      }

      public static bool operator ==(TypedPtr p1, TypedPtr p2) {
        throw new NotImplementedException();
      }

      public static bool operator !=(TypedPtr p1, TypedPtr p2) {
        throw new NotImplementedException();
      }

      public override int GetHashCode() {
        throw new NotImplementedException(); // is only here to suppress warnings
      }

      public override bool Equals(object obj) {
        throw new NotImplementedException(); // is only here to suppress warnings
      }
    }
   
    public abstract class Objset
    {
      // ensure the size is non-zero
      byte dummy;
      private Objset() { dummy++; }

      public static bool operator <=(TypedPtr elem, Objset set) {
        throw new NotImplementedException();
      }

      public static bool operator >=(TypedPtr elem, Objset set) {
        throw new NotImplementedException();
      }

      public static bool operator <(TypedPtr elem, Objset set) {
        throw new NotImplementedException();
      }

      public static bool operator >(TypedPtr elem, Objset set) {
        throw new NotImplementedException();
      }

      public static Objset operator |(Objset s1, Objset s2) {
        throw new NotImplementedException();
      }

      public static Objset operator &(Objset s1, Objset s2) {
        throw new NotImplementedException();
      }

      public static Objset operator ^(Objset s1, Objset s2) {
        throw new NotImplementedException();
      }

      public static Objset operator -(Objset s, TypedPtr o) {
        throw new NotImplementedException();
      }

      public static Objset operator +(Objset s, TypedPtr o) {
        throw new NotImplementedException();
      }
    }

    [AttributeUsage(AttributeTargets.Method)]
    public sealed class IntBoogieAttr : Attribute
    {
      public IntBoogieAttr(string name, int val) {
      }
    }

    [AttributeUsage(AttributeTargets.Method)]
    public sealed class BoolBoogieAttr : Attribute
    {
      public BoolBoogieAttr(string name, int val) {
      }
    }

    [AttributeUsage(AttributeTargets.All)]
    public sealed class StringVccAttr : Attribute
    {
      public StringVccAttr(string name, string val) { }
    }
  }
}

namespace System.Diagnostics.Contracts {
  #region Attributes

  /// <summary>
  /// Methods and classes marked with this attribute can be used within calls to Contract methods. Such methods not make any visible state changes.
  /// </summary>
  //[AttributeUsage(AttributeTargets.Method | AttributeTargets.Property | AttributeTargets.Event | AttributeTargets.Class, AllowMultiple = false, Inherited = true)]
  //public sealed class PureAttribute : Attribute {
  //}

  /// <summary>
  /// Types marked with this attribute specify that a separate type contains the contracts for this type.
  /// </summary>
  [AttributeUsage(AttributeTargets.Class | AttributeTargets.Interface, AllowMultiple = false, Inherited = false)]
  public sealed class ContractClassAttribute : Attribute {
    private Type _typeWithContracts;

    public ContractClassAttribute (Type typeContainingContracts) {
      _typeWithContracts = typeContainingContracts;
    }

    public Type TypeContainingContracts {
      get { return _typeWithContracts; }
    }
  }

  /// <summary>
  /// Types marked with this attribute specify that they are a contract for the type that is the argument of the constructor.
  /// </summary>
  [AttributeUsage(AttributeTargets.Class, AllowMultiple = false, Inherited = false)]
  public sealed class ContractClassForAttribute : Attribute {
    private Type _typeIAmAContractFor;

    public ContractClassForAttribute (Type typeContractsAreFor) {
      _typeIAmAContractFor = typeContractsAreFor;
    }

    public Type TypeContractsAreFor {
      get { return _typeIAmAContractFor; }
    }
  }

  /// <summary>
  /// This attribute is used to mark a method as being the invariant
  /// method for a class. The method can have any name, but it must
  /// return "void" and take no parameters. The body of the method
  /// must consist solely of one or more calls to the method
  /// CodeContract.Invariant. A suggested name for the method is 
  /// "ObjectInvariant".
  /// </summary>
  [AttributeUsage(AttributeTargets.Method, AllowMultiple = false, Inherited = false)]
  public sealed class ContractInvariantMethodAttribute : Attribute {
  }

  /// <summary>
  /// Attribute that specifies that an assembly has runtime contract checks.
  /// </summary>
  [AttributeUsage(AttributeTargets.Assembly)]
  public sealed class RuntimeContractsAttribute : Attribute {
  }

#if FEATURE_SERIALIZATION
  [Serializable]
#endif
  internal enum Mutability {
    Unspecified,
    Immutable,    // read-only after construction, except for lazy initialization & caches
    // Do we need a "deeply immutable" value?
    Mutable,
    HasInitializationPhase,  // read-only after some point.  
    // Do we need a value for mutable types with read-only wrapper subclasses?
  }
  // Note: This hasn't been thought through in any depth yet.  Consider it experimental.
  [AttributeUsage(AttributeTargets.Class | AttributeTargets.Struct, AllowMultiple = false, Inherited = false)]
  internal sealed class MutabilityAttribute : Attribute {
    private Mutability _mutabilityMarker;

    public MutabilityAttribute (Mutability mutabilityMarker) {
      _mutabilityMarker = mutabilityMarker;
    }

    public Mutability Mutability {
      get { return _mutabilityMarker; }
    }
  }

  /// <summary>
  /// Instructs downstream tools whether to assume the correctness of this assembly, type or member without performing any verification or not.
  /// Can use [ContractVerification(false)] to explicitly mark assembly, type or member as one to *not* have verification performed on it.
  /// Most specific element found (member, type, then assembly) takes precedence.
  /// (That is useful if downstream tools allow a user to decide which polarity is the default, unmarked case.)
  /// </summary>
  /// <remarks>
  /// Apply this attribute to a type to apply to all members of the type, including nested types.
  /// Apply this attribute to an assembly to apply to all types and members of the assembly.
  /// Apply this attribute to a property to apply to both the getter and setter.
  /// </remarks>
  [AttributeUsage(AttributeTargets.Assembly | AttributeTargets.Class | AttributeTargets.Struct | AttributeTargets.Method | AttributeTargets.Constructor | AttributeTargets.Property)]
  public sealed class ContractVerificationAttribute : Attribute {
    private bool _value;

    public ContractVerificationAttribute (bool value) { _value = value; }

    public bool Value {
      get { return _value; }
    }
  }

  /// <summary>
  /// Allows a field f to be used in the method contracts for a method m when f has less visibility than m.
  /// For instance, if the method is public, but the field is private.
  /// </summary>
  [Conditional("CONTRACTS_FULL")]
  [AttributeUsage(AttributeTargets.Field)]
  public sealed class ContractPublicPropertyNameAttribute : Attribute {
    private String _publicName;

    public ContractPublicPropertyNameAttribute (String name) {
      _publicName = name;
    }

    public String Name {
      get { return _publicName; }
    }
  }

  #endregion Attributes

  /// <summary>
  /// Contains static methods for representing program contracts such as preconditions, postconditions, and invariants.
  /// </summary>
  /// <remarks>
  /// WARNING: A binary rewriter must be used to insert runtime enforcement of these contracts.
  /// Otherwise some contracts like Ensures can only be checked statically and will not throw exceptions during runtime when contracts are violated.
  /// Please note this class uses conditional compilation to help avoid easy mistakes.  Defining the preprocessor
  /// symbol CONTRACTS_PRECONDITIONS will include all preconditions expressed using Contract.Requires in your 
  /// build.  The symbol CONTRACTS_FULL will include postconditions and object invariants, and requires the binary rewriter.
  /// </remarks>
  public static partial class CodeContract {

    #region Private Methods
    //[System.Security.SecuritySafeCritical]  // auto-generated
    private static void AssertImpl (String message) {
      // @TODO: Managed Debugging Assistant (MDA).  
      // @TODO: Consider converting expression to a String, then passing that as the second parameter.
      StackTrace stack = new StackTrace(1, true);
      String stackString = stack.ToString();
      Debug.Assert(false, message, "Stack trace: " + Environment.NewLine + stackString);
    }
    // Need a way to terminate execution that works for the desktop, hosted server (aka SQL), 
    // and Silverlight browser scenarios, where we are happy allowing partially trusted code
    // to halt execution in some manner.
    //[System.Security.SecuritySafeCritical]
    private static void FailImpl (String message) {
      try {
        AssertImpl(message);
      } finally {
#if FEATURE_CORECLR
        // @TODO: Figure out what Jolt is prepared to accept.  Tearing down the browser process is 
        // wrong.  Unloading the appdomain may be acceptable, if Jolt is prepared for it.  Aborting
        // the thread may also be surprising to Jolt - we just don't know yet.
        throw new SystemException("Encountered a developer error.  We don't want to continue execution, but we're being ultra polite about it.");
#else
        // Will trigger escalation policy, if hosted.  Otherwise, exits the process.
        Environment.FailFast(message);
#endif
      }
    }

    #endregion Private Methods

    #region User Methods

    #region Assume

    /// <summary>
    /// Instructs code analysis tools to assume the expression <paramref name="condition"/> is true even if it can not be statically proven to always be true.
    /// </summary>
    /// <param name="condition">Expression to assume will always be true.</param>
    /// <remarks>
    /// At runtime this is equivalent to an <seealso cref="System.Diagnostics.Contracts.CodeContract.Assert(bool)"/>.
    /// </remarks>
    [Pure]
    [Conditional("DEBUG")]
    [Conditional("CONTRACTS_FULL")]
    public static void Assume (bool condition) {
      if (!condition) {
        AssertImpl("Assumption failed");
      }
    }
    /// <summary>
    /// Instructs code analysis tools to assume the expression <paramref name="condition"/> is true even if it can not be statically proven to always be true.
    /// </summary>
    /// <param name="condition">Expression to assume will always be true.</param>
    /// <param name="message">If it is not a constant string literal, then the contract may not be understood by tools.</param>
    /// <remarks>
    /// At runtime this is equivalent to an <seealso cref="System.Diagnostics.Contracts.CodeContract.Assert(bool)"/>.
    /// </remarks>
    [Pure]
    [Conditional("DEBUG")]
    [Conditional("CONTRACTS_FULL")]
    public static void Assume (bool condition, String message) {
      if (!condition) {
        AssertImpl("Assumption failed: " + message);
      }
    }

    #endregion Assume

    #region Assert

    /// <summary>
    /// In debug builds, perform a runtime check that <paramref name="condition"/> is true.
    /// </summary>
    /// <param name="condition">Expression to check to always be true.</param>
    [Pure]
    [Conditional("DEBUG")]
    [Conditional("CONTRACTS_FULL")]
    public static void Assert (bool condition) {
      if (!condition)
        AssertImpl("Assertion failed");
    }
    /// <summary>
    /// In debug builds, perform a runtime check that <paramref name="condition"/> is true.
    /// </summary>
    /// <param name="condition">Expression to check to always be true.</param>
    /// <param name="message">If it is not a constant string literal, then the contract may not be understood by tools.</param>
    [Pure]
    [Conditional("DEBUG")]
    [Conditional("CONTRACTS_FULL")]
    public static void Assert (bool condition, String message) {
      if (!condition)
        AssertImpl("Assertion failed: " + message);
    }

    #endregion Assert

    #region Requires

    /// <summary>
    /// Specifies a contract such that the expression <paramref name="condition"/> must be true before the enclosing method or property is invoked.
    /// </summary>
    /// <param name="condition">Boolean expression representing the contract.</param>
    /// <remarks>
    /// This call must happen at the beginning of a method or property before any other code.
    /// This contract is exposed to clients so must only reference members at least as visible as the enclosing method.
    /// Use this form when backward compatibility does not force you to throw a particular exception.
    /// </remarks>
    [Pure]
    [Conditional("CONTRACTS_FULL")]
    [Conditional("CONTRACTS_PRECONDITIONS")]
    public static void Requires (bool condition) {
      if (!condition)
        FailImpl("Precondition failed");
    }

    /// <summary>
    /// Specifies a contract such that the expression <paramref name="condition"/> must be true before the enclosing method or property is invoked.
    /// </summary>
    /// <param name="condition">Boolean expression representing the contract.</param>
    /// <param name="message">If it is not a constant string literal, then the contract may not be understood by tools.</param>
    /// <remarks>
    /// This call must happen at the beginning of a method or property before any other code.
    /// This contract is exposed to clients so must only reference members at least as visible as the enclosing method.
    /// Use this form when backward compatibility does not force you to throw a particular exception.
    /// </remarks>
    [Pure]
    [Conditional("CONTRACTS_FULL")]
    [Conditional("CONTRACTS_PRECONDITIONS")]
    public static void Requires (bool condition, String message) {
      if (!condition)
        FailImpl("Precondition failed: " + message);
    }

    /// <summary>
    /// Specifies a contract such that the expression <paramref name="condition"/> must be true before the enclosing method or property is invoked.
    /// </summary>
    /// <param name="condition">Boolean expression representing the contract.</param>
    /// <remarks>
    /// This call must happen at the beginning of a method or property before any other code.
    /// This contract is exposed to clients so must only reference members at least as visible as the enclosing method.
    /// Use this form when you want a check in the release build and backward compatibility does not
    /// force you to throw a particular exception.  This is recommended for security-sensitive checks.
    /// </remarks>
    [Pure]
    public static void RequiresAlways (bool condition) {
      if (!condition)
        FailImpl("Precondition failed");
    }
    /// <summary>
    /// Specifies a contract such that the expression <paramref name="condition"/> must be true before the enclosing method or property is invoked.
    /// </summary>
    /// <param name="condition">Boolean expression representing the contract.</param>
    /// <param name="message">If it is not a constant string literal, then the contract may not be understood by tools.</param>
    /// <remarks>
    /// This call must happen at the beginning of a method or property before any other code.
    /// This contract is exposed to clients so must only reference members at least as visible as the enclosing method.
    /// Use this form when you want a check in the release build and backward compatibility does not
    /// force you to throw a particular exception.  This is recommended for security-sensitive checks.
    /// </remarks>
    [Pure]
    public static void RequiresAlways (bool condition, String message) {
      if (!condition)
        FailImpl("Precondition failed: " + message);
    }

    #endregion Requires

    #region Ensures

    /// <summary>
    /// Specifies a public contract such that the expression <paramref name="condition"/> will be true when the enclosing method or property returns normally.
    /// </summary>
    /// <param name="condition">Boolean expression representing the contract.  May include <seealso cref="Old"/> and <seealso cref="Result"/>.</param>
    /// <remarks>
    /// This call must happen at the beginning of a method or property before any other code.
    /// This contract is exposed to clients so must only reference members at least as visible as the enclosing method.
    /// The contract rewriter must be used for runtime enforcement of this postcondition.
    /// </remarks>
    [Pure]
    [Conditional("CONTRACTS_FULL")]
    public static void Ensures (bool condition) {
      AssertImpl("This assembly must be rewritten using the binary rewriter or else postconditions will be incorrectly evaluated.");
    }
    /// <summary>
    /// Specifies a public contract such that the expression <paramref name="condition"/> will be true when the enclosing method or property returns normally.
    /// </summary>
    /// <param name="condition">Boolean expression representing the contract.  May include <seealso cref="Old"/> and <seealso cref="Result"/>.</param>
    /// <param name="message">If it is not a constant string literal, then the contract may not be understood by tools.</param>
    /// <remarks>
    /// This call must happen at the beginning of a method or property before any other code.
    /// This contract is exposed to clients so must only reference members at least as visible as the enclosing method.
    /// The contract rewriter must be used for runtime enforcement of this postcondition.
    /// </remarks>
    [Pure]
    [Conditional("CONTRACTS_FULL")]
    public static void Ensures (bool condition, String message) {
      AssertImpl("This assembly must be rewritten using the binary rewriter or else postconditions will be incorrectly evaluated.");
    }

    /// <summary>
    /// Specifies a contract such that an exception of type <typeparamref name="TException"/> may be thrown.
    /// </summary>
    /// <typeparam name="TException">Type of exception that may be thrown.</typeparam>
    /// <remarks>
    /// This call must happen at the beginning of a method or property before any other code.
    /// This contract is exposed to clients so must only reference types at least as visible as the enclosing method.
    /// </remarks>
    [Pure]
    [Conditional("CONTRACTS_FULL")]
    public static void Throws<TException> () where TException : Exception {
    }

    /// <summary>
    /// Specifies a contract such that if an exception of type <typeparamref name="TException"/> is thrown then the expression <paramref name="condition"/> will be true when the enclosing method or property terminates abnormally.
    /// </summary>
    /// <typeparam name="TException">Type of exception related to this postcondition.</typeparam>
    /// <param name="condition">Boolean expression representing the contract.  May include <seealso cref="Old"/> and <seealso cref="Result"/>.</param>
    /// <remarks>
    /// This call must happen at the beginning of a method or property before any other code.
    /// This contract is exposed to clients so must only reference types and members at least as visible as the enclosing method.
    /// The contract rewriter must be used for runtime enforcement of this postcondition.
    /// </remarks>
    [Pure]
    [Conditional("CONTRACTS_FULL")]
    public static void EnsuresOnThrow<TException> (bool condition) where TException : Exception {
      AssertImpl("This assembly must be rewritten using the binary rewriter or else postconditions will be incorrectly evaluated.");
    }
    /// <summary>
    /// Specifies a contract such that if an exception of type <typeparamref name="TException"/> is thrown then the expression <paramref name="condition"/> will be true when the enclosing method or property terminates abnormally.
    /// </summary>
    /// <typeparam name="TException">Type of exception related to this postcondition.</typeparam>
    /// <param name="condition">Boolean expression representing the contract.  May include <seealso cref="Old"/> and <seealso cref="Result"/>.</param>
    /// <param name="message">If it is not a constant string literal, then the contract may not be understood by tools.</param>
    /// <remarks>
    /// This call must happen at the beginning of a method or property before any other code.
    /// This contract is exposed to clients so must only reference types and members at least as visible as the enclosing method.
    /// The contract rewriter must be used for runtime enforcement of this postcondition.
    /// </remarks>
    [Pure]
    [Conditional("CONTRACTS_FULL")]
    public static void EnsuresOnThrow<TException> (bool condition, String message) where TException : Exception {
      AssertImpl("This assembly must be rewritten using the binary rewriter or else postconditions will be incorrectly evaluated.");
    }

    #region Old, Result, and Out Parameters

    /// <summary>
    /// Represents the result (a.k.a. return value) of a method or property.
    /// </summary>
    /// <typeparam name="T">Type of return value of the enclosing method or property.</typeparam>
    /// <returns>Return value of the enclosing method or property.</returns>
    /// <remarks>
    /// This method can only be used within the argument to the <seealso cref="Ensures"/> contract.
    /// </remarks>
    [Pure]
    public static T Result<T> () { return default(T); }

    /// <summary>
    /// Represents the final (output) value of an out parameter when returning from a method.
    /// </summary>
    /// <typeparam name="T">Type of the out parameter.</typeparam>
    /// <param name="value">The out parameter.</param>
    /// <returns>The output value of the out parameter.</returns>
    /// <remarks>
    /// This method can only be used within the argument to the <seealso cref="Ensures"/> contract.
    /// </remarks>
    [Pure]
    public static T ValueAtReturn<T> (out T value) { value = default(T); return value; }

    /// <summary>
    /// Represents the value of <paramref name="value"/> as it was at the start of the method or property.
    /// </summary>
    /// <typeparam name="T">Type of <paramref name="value"/>.  This can be inferred.</typeparam>
    /// <param name="value">Value to represent.  This must be a field or parameter.</param>
    /// <returns>Value of <paramref name="value"/> at the start of the method or property.</returns>
    /// <remarks>
    /// This method can only be used within the argument to the <seealso cref="Ensures"/> contract.
    /// </remarks>
    [Pure]
    public static T OldValue<T> (T value) { return default(T); }

    #endregion Old, Result, and Out Parameters

    #endregion Ensures

    #region Invariant

    /// <summary>
    /// Specifies a contract such that the expression <paramref name="condition"/> will be true after every method or property on the enclosing class.
    /// </summary>
    /// <param name="condition">Boolean expression representing the contract.</param>
    /// <remarks>
    /// This contact can only be specified in a dedicated invariant method declared on a class.
    /// This contract is not exposed to clients so may reference members less visible as the enclosing method.
    /// The contract rewriter must be used for runtime enforcement of this invariant.
    /// </remarks>
    [Pure]
    [Conditional("CONTRACTS_FULL")]
    public static void Invariant (bool condition) {
      AssertImpl("This assembly must be rewritten using the binary rewriter.");
    }
    /// <summary>
    /// Specifies a contract such that the expression <paramref name="condition"/> will be true after every method or property on the enclosing class.
    /// </summary>
    /// <param name="condition">Boolean expression representing the contract.</param>
    /// <param name="message">If it is not a constant string literal, then the contract may not be understood by tools.</param>
    /// <remarks>
    /// This contact can only be specified in a dedicated invariant method declared on a class.
    /// This contract is not exposed to clients so may reference members less visible as the enclosing method.
    /// The contract rewriter must be used for runtime enforcement of this invariant.
    /// </remarks>
    [Pure]
    [Conditional("CONTRACTS_FULL")]
    public static void Invariant (bool condition, String message) {
      AssertImpl("This assembly must be rewritten using the binary rewriter.");
    }

    #endregion Invariant

    #region Quantifiers

    #region ForAll

    /// <summary>
    /// Returns whether the <paramref name="predicate"/> returns <c>true</c> 
    /// for all integers starting from <paramref name="inclusiveLowerBound"/> to <paramref name="exclusiveUpperBound"/> - 1.
    /// </summary>
    /// <param name="inclusiveLowerBound">First integer to pass to <paramref name="predicate"/>.</param>
    /// <param name="exclusiveUpperBound">One greater than the last integer to pass to <paramref name="predicate"/>.</param>
    /// <param name="predicate">Function that is evaluated from <paramref name="inclusiveLowerBound"/> to <paramref name="exclusiveUpperBound"/> - 1.</param>
    /// <returns><c>true</c> if <paramref name="predicate"/> returns <c>true</c> for all integers 
    /// starting from <paramref name="lo"/> to <paramref name="hi"/> - 1.</returns>
    /// <seealso cref="System.Collections.Generic.List.TrueForAll"/>
    [Pure]
    public static bool ForAll (int inclusiveLowerBound, int exclusiveUpperBound, Predicate<int> predicate) {
      CodeContract.RequiresAlways(inclusiveLowerBound <= exclusiveUpperBound);
      CodeContract.RequiresAlways(predicate != null);

      for (int i = inclusiveLowerBound; i < exclusiveUpperBound; i++)
        if (!predicate(i)) return false;
      return true;
    }
    /// <summary>
    /// Returns whether the <paramref name="predicate"/> returns <c>true</c> 
    /// for all elements in the <paramref name="collection"/>.
    /// </summary>
    /// <param name="collection">The collection from which elements will be drawn from to pass to <paramref name="predicate"/>.</param>
    /// <param name="predicate">Function that is evaluated on elements from <paramref name="collection"/>.</param>
    /// <returns><c>true</c> if and only if <paramref name="predicate"/> returns <c>true</c> for all elements in
    /// <paramref name="collection"/>.</returns>
    /// <seealso cref="System.Collections.Generic.List.TrueForAll"/>
    /// <remarks>
    /// Once C# v3 is released, the first parameter will have the "this" marking
    /// so the method can be used as if it is an instance method on the <paramref name="collection"/>.
    /// </remarks>
    [Pure]
    public static bool ForAll<T> (/*this*/ IEnumerable<T> collection, Predicate<T> predicate) {
      CodeContract.RequiresAlways(collection != null);
      CodeContract.RequiresAlways(predicate != null);
      foreach (T t in collection)
        if (!predicate(t)) return false;
      return true;
    }
    /// <summary>
    /// Returns whether the <paramref name="predicate"/> returns <c>true</c> 
    /// for all values of type T.
    /// </summary>
    /// <param name="predicate">Function that is evaluated on elements of type T.</param>
    /// <returns><c>true</c> if and only if <paramref name="predicate"/> returns <c>true</c> for all elements of type T.</returns>
    [Pure]
    public static bool ForAll<T> (Predicate<T> predicate) {
      CodeContract.RequiresAlways(predicate != null);
      return true;
    }

    #endregion ForAll

    #region Exists

    /// <summary>
    /// Returns whether the <paramref name="predicate"/> returns <c>true</c> 
    /// for any integer starting from <paramref name="inclusiveLowerBound"/> to <paramref name="exclusiveUpperBound"/> - 1.
    /// </summary>
    /// <param name="inclusiveLowerBound">First integer to pass to <paramref name="predicate"/>.</param>
    /// <param name="exclusiveUpperBoundi">One greater than the last integer to pass to <paramref name="predicate"/>.</param>
    /// <param name="predicate">Function that is evaluated from <paramref name="inclusiveLowerBound"/> to <paramref name="exclusiveUpperBound"/> - 1.</param>
    /// <returns><c>true</c> if <paramref name="predicate"/> returns <c>true</c> for any integer
    /// starting from <paramref name="inclusiveLowerBound"/> to <paramref name="exclusiveUpperBound"/> - 1.</returns>
    /// <seealso cref="System.Collections.Generic.List.Exists"/>
    [Pure]
    public static bool Exists (int inclusiveLowerBound, int exclusiveUpperBound, Predicate<int> predicate) {
      CodeContract.RequiresAlways(inclusiveLowerBound <= exclusiveUpperBound);
      CodeContract.RequiresAlways(predicate != null);

      for (int i = inclusiveLowerBound; i < exclusiveUpperBound; i++)
        if (predicate(i)) return true;
      return false;
    }
    /// <summary>
    /// Returns whether the <paramref name="predicate"/> returns <c>true</c> 
    /// for any element in the <paramref name="collection"/>.
    /// </summary>
    /// <param name="collection">The collection from which elements will be drawn from to pass to <paramref name="predicate"/>.</param>
    /// <param name="predicate">Function that is evaluated on elements from <paramref name="collection"/>.</param>
    /// <returns><c>true</c> if and only if <paramref name="predicate"/> returns <c>true</c> for an element in
    /// <paramref name="collection"/>.</returns>
    /// <seealso cref="System.Collections.Generic.List.Exists"/>
    /// <remarks>
    /// Once C# v3 is released, the first parameter will have the "this" marking
    /// so the method can be used as if it is an instance method on the <paramref name="collection"/>.
    /// </remarks>
    [Pure]
    public static bool Exists<T> (/*this*/ IEnumerable<T> collection, Predicate<T> predicate) {
      CodeContract.RequiresAlways(collection != null);
      CodeContract.RequiresAlways(predicate != null);
      foreach (T t in collection)
        if (predicate(t)) return true;
      return false;
    }
    /// <summary>
    /// Returns whether the <paramref name="predicate"/> returns <c>true</c> 
    /// for some value of type T.
    /// </summary>
    /// <param name="predicate">Function that is evaluated on elements of type T.</param>
    /// <returns><c>true</c> if and only if <paramref name="predicate"/> returns <c>true</c> for some value of type T.</returns>
    [Pure]
    public static bool Exists<T> (Predicate<T> predicate) {
      CodeContract.RequiresAlways(predicate != null);
      return true;
    }

    #endregion Exists

    #endregion Quantifiers

    #region Pointers

    /// <summary>
    /// Runtime checking for pointer bounds is not currently feasible. Thus, at runtime, we just return
    /// a very long extent for each pointer that is writable. As long as assertions are of the form
    /// WritableBytes(ptr) >= ..., the runtime assertions will not fail.
    /// The runtime value is 2^64 - 1 or 2^32 - 1.
    /// </summary>
    static readonly ulong MaxWritableExtent = (UIntPtr.Size == 4) ? UInt32.MaxValue : UInt64.MaxValue;

    /// <summary>
    /// Allows specifying a writable extent for a UIntPtr, similar to SAL's writable extent.
    /// NOTE: this is for static checking only. No useful runtime code can be generated for this
    /// at the moment.
    /// </summary>
    /// <param name="startAddress">Start of memory region</param>
    /// <returns>The result is the number of bytes writable starting at <paramref name="startAddress"/></returns>
    [Pure]
    public static ulong WritableBytes (UIntPtr startAddress) { return MaxWritableExtent; }

    /// <summary>
    /// Allows specifying a writable extent for a UIntPtr, similar to SAL's writable extent.
    /// NOTE: this is for static checking only. No useful runtime code can be generated for this
    /// at the moment.
    /// </summary>
    /// <param name="startAddress">Start of memory region</param>
    /// <returns>The result is the number of bytes writable starting at <paramref name="startAddress"/></returns>
    [Pure]
    public static ulong WritableBytes (IntPtr startAddress) { return MaxWritableExtent; }

    /// <summary>
    /// Allows specifying a writable extent for a UIntPtr, similar to SAL's writable extent.
    /// NOTE: this is for static checking only. No useful runtime code can be generated for this
    /// at the moment.
    /// </summary>
    /// <param name="startAddress">Start of memory region</param>
    /// <returns>The result is the number of bytes writable starting at <paramref name="startAddress"/></returns>
    [Pure]
    unsafe public static ulong WritableBytes (void* startAddress) { return MaxWritableExtent; }

    /// <summary>
    /// Allows specifying a readable extent for a UIntPtr, similar to SAL's readable extent.
    /// NOTE: this is for static checking only. No useful runtime code can be generated for this
    /// at the moment.
    /// </summary>
    /// <param name="startAddress">Start of memory region</param>
    /// <returns>The result is the number of bytes readable starting at <paramref name="startAddress"/></returns>
    [Pure]
    public static ulong ReadableBytes (UIntPtr startAddress) { return MaxWritableExtent; }

    /// <summary>
    /// Allows specifying a readable extent for a UIntPtr, similar to SAL's readable extent.
    /// NOTE: this is for static checking only. No useful runtime code can be generated for this
    /// at the moment.
    /// </summary>
    /// <param name="startAddress">Start of memory region</param>
    /// <returns>The result is the number of bytes readable starting at <paramref name="startAddress"/></returns>
    [Pure]
    public static ulong ReadableBytes (IntPtr startAddress) { return MaxWritableExtent; }

    /// <summary>
    /// Allows specifying a readable extent for a UIntPtr, similar to SAL's readable extent.
    /// NOTE: this is for static checking only. No useful runtime code can be generated for this
    /// at the moment.
    /// </summary>
    /// <param name="startAddress">Start of memory region</param>
    /// <returns>The result is the number of bytes readable starting at <paramref name="startAddress"/></returns>
    [Pure]
    unsafe public static ulong ReadableBytes (void* startAddress) { return MaxWritableExtent; }

    #endregion

    #region Misc.

    /// <summary>
    /// Marker to indicate the end of the contract section of a method.
    /// </summary>
    [Conditional("CONTRACTS_FULL")]
    [Conditional("CONTRACTS_PRECONDITIONS")]
    public static void EndContractBlock () { }

    #endregion

    #endregion User Methods

  }

}