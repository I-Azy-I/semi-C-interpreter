use crate::memory::MemoryValue;

#[derive(Debug, Clone)]
pub enum ErrorInterpreter{
    NotImplemented,
    TypeConversion,
    NotAFunction,
    UnreachableReached,
    // MissingArgumentsFunction,
    SpecifierNotImplemented,
    ParsingError,
    FunctionNotFounded(String),
    IncorrectNumberOfArguments(String),
    IdentifierNotFoundInMemory(String),
    IncorrectTypeOfArguments(String),
    IncorrectTypeDeclaration(String),
    IncorrectTypeBinaryOperation(String),
    InvalidMultiplication,
    IndexOutOfBounds,
    ModuloByZero,
    DivisionByZero,
    InvalidDivision,
    InvalidModulo,
    InvalidAddition,
    InvalidSubtraction,
    InvalidBitShift,
    InvalidComparison,
    InvalidBitwiseOperation,
    InvalidLogicalOperation,
    BaseNotSupported,
    InvalidType(String),
    InvalidInt,
    InvalidPlusOperator,
    InvalidMinusOperator,
    InvalidNegateOperator,
    NoIndexHasBeenProvidedForArray,
    InvalidValueForArraySize,
    InvalidDefaultSpecifierValueConversion,
    InitializationArrayAndPointerImpossible,
    MultipleDimensionArrayNotImplemented,
    MultiplePointerNotImplemented,
    NoIdentifierCanBeExtract,
    NotAPointer,
    HasToBeAIntOrFloatForBooleanEvaluation,
    ImpossibleToIncrement,
    ArraySizeLessThanOne,
    ForConditionNotDefined,
    ForStepNotDefined,
    ReturnCalled(MemoryValue), //not real error but used to stop flow
    BreakCalled, //not real error but used to stop flow
    NotTypeSpecifierInTypeName,
    ImpossibleToCastIntoThisType(String),
    StringUsedAsValue,
    InvalidNumberArgumentPrintf,
    InvalidArgumentsForPrintf,
    EmptyDeclarationArray,
    ConversionValueSpecifierNotImplement,
    NotSameSizeArrayAndDeclarationOfArray,
    FunctionReturnWrongType(String),
    IndirectionOnNonPointer,
    WhatHaveYouDone,
    ImpossibleToAssignValueToAddress,
    ImpossibleToGetValueFromAddress,
    ImpossibleToGetAddressOfAValue,
    VariableAlreadyExist
}
impl ErrorInterpreter{
    pub fn error_message(&self) -> String {
        use ErrorInterpreter::*;
        match self {
            NotImplemented => "This feature is not implemented yet".to_string(),
            TypeConversion => "Unable to perform type conversion".to_string(),
            NotAFunction => "This identifier is not a function".to_string(),
            UnreachableReached => "Reached unreachable code".to_string(),
            SpecifierNotImplemented => "This specifier is not implemented".to_string(),
            ParsingError => "Error occurred while parsing".to_string(),
            FunctionNotFounded(name) => format!("Function '{}' not found", name),
            IncorrectNumberOfArguments(msg) => format!("Incorrect number of arguments: {}", msg),
            IdentifierNotFoundInMemory(id) => format!("Identifier '{}' not found in memory", id),
            IncorrectTypeOfArguments(msg) => format!("Incorrect type of arguments: {}", msg),
            IncorrectTypeDeclaration(msg) => format!("Incorrect type declaration: {}", msg),
            IncorrectTypeBinaryOperation(msg) => format!("Incorrect type in binary operation: {}", msg),
            InvalidMultiplication => "Invalid multiplication operation".to_string(),
            IndexOutOfBounds => "Array index out of bounds".to_string(),
            ModuloByZero => "Cannot perform modulo by zero".to_string(),
            DivisionByZero => "Cannot divide by zero".to_string(),
            InvalidDivision => "Invalid division operation".to_string(),
            InvalidModulo => "Invalid modulo operation".to_string(),
            InvalidAddition => "Invalid addition operation".to_string(),
            InvalidSubtraction => "Invalid subtraction operation".to_string(),
            InvalidBitShift => "Invalid bit shift operation".to_string(),
            InvalidComparison => "Invalid comparison operation".to_string(),
            InvalidBitwiseOperation => "Invalid bitwise operation".to_string(),
            InvalidLogicalOperation => "Invalid logical operation".to_string(),
            BaseNotSupported => "This numerical base is not supported".to_string(),
            InvalidType(t) => format!("Invalid type: {}", t),
            InvalidInt => "Invalid integer value".to_string(),
            InvalidPlusOperator => "Invalid use of plus operator".to_string(),
            InvalidMinusOperator => "Invalid use of minus operator".to_string(),
            InvalidNegateOperator => "Invalid use of negation operator".to_string(),
            NoIndexHasBeenProvidedForArray => "No index provided for array access".to_string(),
            InvalidValueForArraySize => "Invalid value for array size".to_string(),
            InvalidDefaultSpecifierValueConversion => "Invalid default specifier value conversion".to_string(),
            InitializationArrayAndPointerImpossible => "Cannot initialize array and pointer simultaneously".to_string(),
            MultipleDimensionArrayNotImplemented => "Multiple dimension arrays are not implemented".to_string(),
            MultiplePointerNotImplemented => "Multiple pointers are not implemented".to_string(),
            NoIdentifierCanBeExtract => "No identifier can be extracted".to_string(),
            NotAPointer => "This variable is not a pointer".to_string(),
            HasToBeAIntOrFloatForBooleanEvaluation => "Boolean evaluation requires integer or float".to_string(),
            ImpossibleToIncrement => "Cannot increment this value".to_string(),
            ArraySizeLessThanOne => "Array size must be greater than zero".to_string(),
            ForConditionNotDefined => "For loop condition not defined".to_string(),
            ForStepNotDefined => "For loop step not defined".to_string(),
            ReturnCalled(_) => "This is not an error, it should never be print in this function".to_string(),
            BreakCalled => "This is not an error, it should never be print in this function".to_string(),
            NotTypeSpecifierInTypeName => "No type specifier in type name".to_string(),
            ImpossibleToCastIntoThisType(msg) => format!("Cannot cast into type: {}", msg),
            StringUsedAsValue => "String used as value".to_string(),
            InvalidNumberArgumentPrintf => "Invalid number of arguments for printf".to_string(),
            InvalidArgumentsForPrintf => "Invalid arguments for printf".to_string(),
            EmptyDeclarationArray => "Empty array declaration".to_string(),
            ConversionValueSpecifierNotImplement => "Conversion value specifier not implemented".to_string(),
            NotSameSizeArrayAndDeclarationOfArray => "Array size doesn't match declaration".to_string(),
            FunctionReturnWrongType(msg) => format!("Function returned wrong type: {}", msg),
            IndirectionOnNonPointer => "Attempted indirection on non-pointer".to_string(),
            WhatHaveYouDone => "Unexpected error occurred".to_string(),
            ImpossibleToAssignValueToAddress => "Cannot assign value to this address".to_string(),
            ImpossibleToGetValueFromAddress => "Cannot get value from this address".to_string(),
            ImpossibleToGetAddressOfAValue => "Cannot get address of this value".to_string(),
            VariableAlreadyExist => "Variable already exists".to_string(),
        }
    }
}