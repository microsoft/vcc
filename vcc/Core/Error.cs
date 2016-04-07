//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
namespace Microsoft.Research.Vcc {
  public enum Error {
    None=0,

    BadHexDigit,
    ConstantExpected,
    EmptyCharConst,
    EmptySwitch,
    EndOfPPLineExpected,
    ErrorDirective,
    ExpectedDoubleQuote,
    ExpectedExpression,
    ExpectedIdentifier,
    ExpectedLeftBrace,
    ExpectedRightBrace,
    ExpectedRightBracket,
    ExpectedRightParenthesis,
    ExpectedSemicolon,
    ExpectedSingleQuote,
    FloatOverflow,
    IllegalEscape,
    IllegalStatement,
    IntOverflow,
    InvalidExprTerm,
    InvalidLineNumber,
    InvalidPreprocExpr,
    LocalDuplicate,
    LowercaseEllSuffix,
    MissingPPFile,
    NewlineInConst,
    NoCommentEnd,
    PossibleMistakenNullStatement,
    PPDefFollowsToken,
    PPDirectiveExpected,
    ShiftCountOutOfRange,
    StmtNotInCase,
    SyntaxError,
    TooManyCharsInConst,
    UnescapedSingleQuote,
    UnexpectedToken,
    WarningDirective,
    ExpectedConstantExpression, 
    ArgumentShouldNotBePassedWithOutKeyword,
    ArgumentMustBePassedWithOutKeyword,
    IllegalIndirection,

    /// <summary>
    /// The declaration of function '{0}' already specifies contracts. Discarding the contracts of the definition.
    /// </summary>
    DiscardedContractAtDefinition,
    
    /// <summary>
    /// '&amp;' on bit field ignored
    /// </summary>
    AddressOfBitField,

    /// <summary>
    /// Equality '==' binds stronger than '&amp;&amp;' and '||' which is possibly not what you wanted;  use '&lt;==&gt;' or parenthesize the equality.
    /// </summary>
    PotentialPrecedenceErrorInLogicalExpression,

    /// <summary>
    /// redefinition of formal parameter '{0}'
    /// </summary>
    RedefinitionOfFormalParameter,

    /// <summary>
    /// The size of '{0}' is unknown in the current context.
    /// </summary>
    SizeOfUnknown,

    /// <summary>
    /// Cannot use 'this' in this context.
    /// </summary>
    ThisNotAllowedHere,

    /// <summary>
    /// '{0}' : unknown element size
    /// </summary>
    UnknownElementSize,

    MissingSemicolonAfterStruct,

    /// <summary>
    /// subscript is not of integral type
    /// </summary>
    SubscriptNotOfIntegralType,

    /// <summary>
    /// illegal index
    /// </summary>
    IllegalIndex,

    /// <summary>
    /// Illegal update of map '{0}'
    /// </summary>
    IllegalMapUpdate,

    /// <summary>
    /// '{0}' is a reserved name and cannot be used as {1}.
    /// </summary>
    ReservedName,

    /// <summary>
    /// left of .{0} must have struct/union type
    /// </summary>
    StructRequiredForDot,

    /// <summary>
    /// Cannot determine initializer's type from context.
    /// </summary>
    UnableToDetermineTypeOfInitializer,

    /// <summary>
    /// Type member '{0}' in type '{1}' causes a cycle in the type layout.
    /// </summary>
    ValueTypeLayoutCycle,

    /// <summary>
    /// Cannot use local variable '{0}' before it is declared.
    /// </summary>
    LocalUsedBeforeDeclaration,

    /// <summary>
    /// A map access cannot be passed as an out parameter.
    /// </summary>
    MapAccessAsOutArgument,

    /// <summary>
    /// Did not expect VCC specification keyword '{0}'.
    /// </summary>
    UnexpectedVccKeyword,

    /// <summary>
    /// Could not find built-in types and functions. Missing #include &lt;vcc.h&gt;?
    /// </summary>
    MissingIncludeOfVccH,

    /// <summary>
    /// The parameter name '{0}' is a duplicate.
    /// </summary>
    DuplicateParameterName,

    /// <summary>
    /// Cannot declare array of type '{0}' because it has size 0.
    /// </summary>
    ArrayOfEmptyType,

    /// <summary>
    /// Illegal type '{0}' in map {1}.
    /// </summary>
    IllegalTypeInMap,

    /// <summary>
    /// Incompatible redefinition of type '{0}' from '{1}' to '{2}'.
    /// </summary>
    DuplicateTypedef,

    /// <summary>
    /// '{0}' : illegal use of undefined type '{1}'.
    /// </summary>
    IllegalUseOfUndefinedType,

    /// <summary>
    /// Quantifier without variables.
    /// </summary>
    NoQuantifiedVariables,

    /// <summary>
    /// Calling function {0}, which with variable arguments, is not supported.
    /// </summary>
    VarArgsNotSupported,

    /// <summary>
    /// This loop body contains only specification code.
    /// </summary>
    LoopWithOnlySpecStatements,

    /// <summary>
    /// Cannot use '\result' in this context.
    /// </summary>
    ResultNotAllowedHere,


  }
}
