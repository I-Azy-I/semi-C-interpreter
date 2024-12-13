use lang_c::driver::{parse, Config, Error, Parse};
use std::collections::HashMap;
use std::hash::Hash;
use lang_c::span::{Node, Span};
use std::any::{Any, TypeId};
use std::cmp::PartialEq;
use std::path::Path;
use lang_c::ast;
use log::{debug, error, info, warn};
use lang_c::ast::{ArraySize, BinaryOperator, BinaryOperatorExpression, Constant, DerivedDeclarator, FloatBase, ForInitializer, IntegerBase, SpecifierQualifier, UnaryOperator};
use std::mem::discriminant;
use colored::Colorize;
use clap::Parser;
use std::{thread, time};
use std::io::stdin;
use crate::ErrorInterpreter::*;
use crate::SymbolTableKind::Restricted;

const PRINT_MEMORY: bool = false;
const STACK_SIZE: usize = 1000000;
#[derive(Debug, Clone)]
enum ErrorInterpreter{
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
    fn error_message(&self) -> String {
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
#[derive(Debug, Clone)]
enum MemoryValue {
    Int(i64),
    Float(f64),
    Char(char),
    Array(SpecifierInterpreter, Vec<MemoryValue>), // only used for declaration of arrays
    Pointer(SpecifierInterpreter,usize),
    String(String),
    Null,
    Unit
}

impl MemoryValue {
    fn get_string(&self) -> String {
        match self {
            MemoryValue::Int(value) => { format!("Int: {}", value) },
            MemoryValue::Float(value) => { format!("Float: {}", value) }
            MemoryValue::Char(value) => { format!("{}", value) }
            //MemoryValue::Array(type_array, array) => {format!("type: {:?}, content: {:?}", type_array, array)}
            MemoryValue::Pointer(type_pointer, pointer) => { format!("Pointer type: {:?}, address: {:?}", type_pointer, pointer) }
            MemoryValue::Null => { "null".to_string() },
            MemoryValue::Unit => { "unit".to_string() },
            MemoryValue::String(string) => { format!("String: {}", string) },
            MemoryValue::Array(_, _) => "array (should never be use)".to_string(),
        }
    }
    fn same_type_specifier(&self, specifier: &SpecifierInterpreter) -> bool {
        match (self, specifier) {
            (MemoryValue::Int(_), SpecifierInterpreter::Int) => true,
            (MemoryValue::Float(_), SpecifierInterpreter::Float) => true,
            (MemoryValue::Pointer(pointer_type_value,_), SpecifierInterpreter::Pointer(pointer_type_specifier)) => pointer_type_value.eq(pointer_type_specifier),
            (MemoryValue::Array(_,_), SpecifierInterpreter::Pointer(_)) => true,
            (MemoryValue::Unit, SpecifierInterpreter::Void) => true,
            _ => false
        }
    }
    fn evaluate_boolean_value(&self) -> Result<bool, ErrorInterpreter>{
        match self {
            MemoryValue::Int(value) => Ok(*value != 0),
            MemoryValue::Float(value) => Ok(*value != 0.0),
            _=> Err(HasToBeAIntOrFloatForBooleanEvaluation)
        }
    }
    fn get_specifier(&self) -> Result<SpecifierInterpreter, ErrorInterpreter> {
        match self {
            MemoryValue::Int(_) => Ok(SpecifierInterpreter::Int),
            MemoryValue::Float(_) => Ok(SpecifierInterpreter::Float),
            MemoryValue::Pointer(pointer_type_value,_) => Ok(SpecifierInterpreter::Pointer(Box::new(pointer_type_value.clone()))),
            MemoryValue::Array(_pointer_type_value, _) => unreachable!(),
            _ => Err(ConversionValueSpecifierNotImplement)
        }
    }
    fn cast(self, specifier: &SpecifierInterpreter) -> Result<MemoryValue, ErrorInterpreter> {
        match (self, specifier) {
            // Int conversions
            (MemoryValue::Int(value), SpecifierInterpreter::Int) => Ok(MemoryValue::Int(value)),
            (MemoryValue::Int(value), SpecifierInterpreter::Float) => Ok(MemoryValue::Float(value as f64)),
            (MemoryValue::Int(value), SpecifierInterpreter::Pointer(_)) => Ok(MemoryValue::Pointer(SpecifierInterpreter::Void, value as usize)),

            // Float conversions
            (MemoryValue::Float(value), SpecifierInterpreter::Int) => Ok(MemoryValue::Int(value as i64)),
            (MemoryValue::Float(value), SpecifierInterpreter::Float) => Ok(MemoryValue::Float(value)),

            // Char conversions
            (MemoryValue::Char(value), SpecifierInterpreter::Int) => Ok(MemoryValue::Int(value as i64)),
            (MemoryValue::Char(value), SpecifierInterpreter::Float) => Ok(MemoryValue::Float((value as i64) as f64)),

            // Pointer conversions
            (MemoryValue::Pointer(_, addr), SpecifierInterpreter::Int) => Ok(MemoryValue::Int(addr as i64)),
            (MemoryValue::Pointer(_, addr), SpecifierInterpreter::Pointer(new_type)) => Ok(MemoryValue::Pointer(*new_type.clone(), addr)),

            // Null conversions
            (MemoryValue::Null, SpecifierInterpreter::Int) => Ok(MemoryValue::Int(0)),
            (MemoryValue::Null, SpecifierInterpreter::Float) => Ok(MemoryValue::Float(0.0)),
            (MemoryValue::Null, SpecifierInterpreter::Pointer(_)) => Ok(MemoryValue::Pointer(SpecifierInterpreter::Void, 0)),

            // Unit conversions
            (MemoryValue::Unit, SpecifierInterpreter::Void) => Ok(MemoryValue::Unit),

            // Catch-all for impossible conversions
            (_, SpecifierInterpreter::Void) => Err(ImpossibleToCastIntoThisType(String::from("Void"))),
            (MemoryValue::Float(_), SpecifierInterpreter::Pointer(_)) => Err(ImpossibleToCastIntoThisType(String::from("Pointer"))),
            (MemoryValue::Char(_), SpecifierInterpreter::Pointer(_)) => Err(ImpossibleToCastIntoThisType(String::from("Pointer"))),
            (MemoryValue::Pointer(_, _), SpecifierInterpreter::Float) => Err(ImpossibleToCastIntoThisType(String::from("Float"))),
            (MemoryValue::Unit, specifier) => Err(ImpossibleToCastIntoThisType(match specifier {
                SpecifierInterpreter::Int => String::from("Int"),
                SpecifierInterpreter::Float => String::from("Float"),
                SpecifierInterpreter::Pointer(_) => String::from("Pointer"),
                SpecifierInterpreter::Void => unreachable!(),
            })),
            (_,_) => Err(ImpossibleToCastIntoThisType("String".parse().unwrap())),
        }
    }
}


#[derive(Debug, PartialEq, Clone)]
enum SpecifierInterpreter {
    Int,
    Float,
    Void,
    //Array(Box<SpecifierInterpreter>),
    Pointer(Box<SpecifierInterpreter>)
}


impl SpecifierInterpreter {
    fn default_value(&self) -> Result<MemoryValue,ErrorInterpreter> {
        match &self{
            &SpecifierInterpreter::Int => Ok(MemoryValue::Int(0)),
            &SpecifierInterpreter::Float => Ok(MemoryValue::Float(0.0)),
            &SpecifierInterpreter::Void => Ok(MemoryValue::Unit),
            &SpecifierInterpreter::Pointer(type_pointed) => {
                warn!("Pointer set to null because not initialized");
                Ok(MemoryValue::Pointer(*type_pointed.clone(), 0))
            }
        }
    }
    fn from_node(specifier: &Node<ast::TypeSpecifier>) -> Result<SpecifierInterpreter, ErrorInterpreter>{
        let specifier = &specifier.node;
        match specifier{
            &ast::TypeSpecifier::Int=>Ok(SpecifierInterpreter::Int),
            &ast::TypeSpecifier::Float=>Ok(SpecifierInterpreter::Float),
            &ast::TypeSpecifier::Void=>Ok(SpecifierInterpreter::Void),
            _=>Err(SpecifierNotImplemented)
        }
    }
    fn from_vec_declaration(declaration_specifiers: &Vec<Node<ast::DeclarationSpecifier>>) -> Result<SpecifierInterpreter, ErrorInterpreter>{
        if declaration_specifiers.len() != 1{
            warn!("Only 1 specifier can be use (no const, ..)")
        };
        let specifier = declaration_specifiers
            .iter()
            .find(|node| {
                match node.node {
                    ast::DeclarationSpecifier::TypeSpecifier(_) => true,
                    _ => false
                }
            });
        match specifier {
            Some(specifier) =>{
                let decl_specifier = &specifier.node;
                match decl_specifier {
                    ast::DeclarationSpecifier::TypeSpecifier(specifier) => {
                        Ok(SpecifierInterpreter::from_node(specifier))?
                    }
                    _ => {
                        warn!("Fetcher of specifier got a false positive");
                        Err(ErrorInterpreter::UnreachableReached)
                    }
                }
            }
            None => {
                warn!("Function return specifier not found in function definition");
                Err(ErrorInterpreter::TypeConversion)
            }
        }
    }
}
struct DeclaratorInterpreter {
    identifier: Identifier,
    array_sizes: Vec<Option<usize>>,
    n_pointers: usize,
}
impl DeclaratorInterpreter{
    fn to_specifier(&self, specifier: SpecifierInterpreter)-> Result<SpecifierInterpreter, ErrorInterpreter>{
        if !self.array_sizes.is_empty()  &&  self.n_pointers > 0 {
            return Err(InitializationArrayAndPointerImpossible);
        } else if self.array_sizes.len() > 1{
            return Err(MultipleDimensionArrayNotImplemented);
        }
        if self.array_sizes.len() == 1{
            Ok(SpecifierInterpreter::Pointer(Box::new(specifier)))
        }
        else if self.n_pointers > 0 {
            let mut specifier = specifier;
            for _ in 0 ..self.n_pointers{
                specifier = SpecifierInterpreter::Pointer(Box::new(specifier));
            };
            Ok(specifier)
        } else{
            Ok(specifier)
        }
    }
}
enum DerivedDeclaratorInterpreter{
    Pointer,
    Array(Option<usize>),
    Function,
}

type FunctionArgument = (Option<Identifier>, SpecifierInterpreter);
type Body = ast::Statement;
type FunctionData = (Identifier,SpecifierInterpreter, Vec<FunctionArgument>, Node<Body>);
type Identifier = String ;

#[derive(Debug, Clone)]
struct IdentifierData{
    identifier: Identifier,
    array_index: Option<usize>,
    depth: i32
}
impl IdentifierData{
    fn from_identifier(identifier: Identifier) -> Self{
        IdentifierData {
            identifier,
            array_index: None,
            depth: 0
        }
    }
}


type EnvFunction = HashMap<Identifier, FunctionData>;

type MemoryIndex = usize;
struct Memory<T: Clone> {
    memory: Vec<T>,
    stack_pointer: usize,
}
impl<T: Clone> Memory<T> {
    fn new(default_value: T) -> Memory<T> {
        Memory {
            memory: vec![default_value; STACK_SIZE],
            stack_pointer: 0,
        }
    }
    fn get_stack_pointer(&self) -> MemoryIndex {
        self.stack_pointer
    }
    fn free(&mut self, from: MemoryIndex){
        self.stack_pointer = from;
    }
    fn add(&mut self, value: T) -> MemoryIndex {
        if self.stack_pointer == self.memory.len(){
            // or throw error
            self.memory.push(value);
            self.stack_pointer+=1;
            self.memory.len()-1
        }else {
            self.memory[self.stack_pointer] = value;
            self.stack_pointer+=1;
            self.stack_pointer-1
        }
    }
    fn get(&self, memory: MemoryIndex)-> &T{
        &self.memory[memory]
    }
    fn change(&mut self, memory: MemoryIndex, value: T){
        self.memory[memory] = value;
    }
    fn get_mut(&mut self, memory: MemoryIndex) -> &mut T {
        &mut self.memory[memory]
    }
}

#[derive(Debug, Clone)]
struct SymbolTable<T, U> {
    start_pointer: MemoryIndex,
    kind: SymbolTableKind,
    current: HashMap<T, U>,
}

impl<'a, T: Hash + Eq, U> SymbolTable<T, U>{
    
    fn root() -> Self {
        SymbolTable{
            start_pointer: 0,
            kind: SymbolTableKind::Restricted,
            current: Default::default(),
        }
    }
    fn scoped(start_pointer: MemoryIndex) -> Self{
        SymbolTable{
            start_pointer,
            kind: SymbolTableKind::Scoped,
            current: Default::default(),
        }
    }
    
    fn restricted(start_pointer: MemoryIndex) -> Self{
        SymbolTable{
            start_pointer,
            kind: SymbolTableKind::Restricted,
            current: Default::default(),
        }
    }
    fn get_index(&self, key: &T) -> Option<&U>{
        self.current.get(&key)
    }
    fn save_key(&mut self, key: T, value: U){
        self.current.insert(key, value);
    }
}
#[derive(Debug, Clone)]
#[derive(PartialEq)]
enum SymbolTableKind {
    Restricted,
    Scoped
}

struct  MemoryManager{
    symbol_tables: Vec<SymbolTable<Identifier, MemoryIndex>>,
    memory: Memory<MemoryValue>,
}
impl MemoryManager{
    fn new() -> Self{
        let mut symbol_tables = Vec::new();
        symbol_tables.push(SymbolTable::root());
        MemoryManager{
            symbol_tables,
            memory: Memory::new(MemoryValue::Null)
        }
    }
    fn current_symbol_table(&self) -> &SymbolTable<Identifier, MemoryIndex> {
        self.symbol_tables.last().unwrap()
    }

    fn current_symbol_table_mut(&mut self) -> &mut SymbolTable<Identifier, MemoryIndex> {
        self.symbol_tables.last_mut().unwrap()
    }

    fn push_scope(&mut self, kind: SymbolTableKind) {
        let start_pointer = self.memory.get_stack_pointer();
        let new_table = match kind {
            SymbolTableKind::Scoped => SymbolTable::scoped(start_pointer),
            SymbolTableKind::Restricted => SymbolTable::restricted(start_pointer),
        };
        self.symbol_tables.push(new_table);
    }

    fn get_index(&self, key: &Identifier) -> Option<MemoryIndex>{
        for table in self.symbol_tables.iter().rev() {
            match table.get_index(key) {
                Some(index) => return Some(*index),
                None => match table.kind {
                    SymbolTableKind::Restricted => return None,
                    SymbolTableKind::Scoped => continue
                }
            }
        }
        None
    }
    fn get_value(&self, identifier: &Identifier) -> Option<MemoryValue> {
        debug!("MEMORY_STATE_BEFORE GET {:?}", identifier);
        debug!("{}", self.build_state());
        if let Some(index) = self.get_index(&identifier) {
            let value = self.memory.get(index);
            
            match value{
                /*
                MemoryValue::Array(type_element, array) => {
                    if let Some(array_index) = identifier.array_index {
                        Some(array[array_index].clone())
                    }else{
                        Some(value.clone())
                    }
                }*/
                _ => Some(value.clone())
            }
        }else{
            None
        }
    }

    fn create_value(&mut self, identifier: &Identifier, value: MemoryValue) -> Result<MemoryIndex, ErrorInterpreter>{
        debug!("MEMORY_STATE_BEFORE CREATE {:?} {:?}", identifier, value);
        self.print_state();
        if self.current_symbol_table().current.contains_key(&identifier.clone()){
            return Err(VariableAlreadyExist)
        }
        let memory_id = self.memory.add(value);
        self.current_symbol_table_mut().save_key(identifier.clone(), memory_id);
        debug!("MEMORY_STATE_AFTER CREATE");
        debug!("{}", self.build_state());
        debug!("SYMBOL TABLES");
        debug!("{:?}", self.symbol_tables);
        Ok(memory_id)
    }
    fn change_value(&mut self, identifier: &Identifier, value: MemoryValue) -> Result<MemoryValue, ErrorInterpreter> {
        debug!("MEMORY_STATE_BEFORE CHANGE {:?} {:?}", identifier, value);
        self.print_state();
        if let Some(index) = self.get_index(&identifier) {
            let old_mem_value = self.memory.get_mut(index);
            if discriminant(old_mem_value) != discriminant(&value){
                println!("ouaaah");
                Err(InvalidType(format!("Impossible to change {:?} with {:?}", old_mem_value, value)))
            }else{
                let _old_value = old_mem_value.clone();
                *old_mem_value = value;
                debug!("MEMORY_STATE_AFTER CHANGE");
                debug!("{}", self.build_state());
                Ok(_old_value)
            }
            
        } else {
            debug!("MEMORY_STATE_AFTER CHANGE");
            debug!("{}", self.build_state());
            Err(IdentifierNotFoundInMemory(format!("{:?}", identifier)))
        }
        
    }
    fn set_to_index(&mut self, memory_index: MemoryIndex, value: MemoryValue) { 
        debug!("MEMORY_STATE_BEFORE SET_INDEX {:?}", memory_index);
        debug!("{}", self.build_state());
        self.print_state();
        self.memory.change(memory_index, value);
        debug!("MEMORY_STATE_AFTER SET_INDEX");
        debug!("{}", self.build_state());
    }

    fn get_from_index(&mut self, memory_index: MemoryIndex) -> MemoryValue {
        debug!("MEMORY_STATE_BEFORE SET_INDEX {:?}", memory_index);
        debug!("{}", self.build_state());
        let v = self.memory.get(memory_index);
        debug!("MEMORY_STATE_AFTER SET_INDEX");
        debug!("{}", self.build_state());
        v.clone()
    }
    fn add_array(&mut self, values: &Vec<MemoryValue>) -> Result<MemoryIndex, ErrorInterpreter> {
        let size = values.len();
        if size== 0 {
            return  Err(ArraySizeLessThanOne)
        }
        let index = self.memory.add(values[0].clone());
        for i in 1..size{
            self.set_to_index(i + index, values[i].clone());
        };
        self.memory.stack_pointer += size-1;
        Ok(index)
    }
    
    fn add_array_default(&mut self, default_value: MemoryValue, size: usize) -> Result<MemoryIndex, ErrorInterpreter>{
        debug!("MEMORY_STATE_BEFORE ADD ARRAY {:?} {}", default_value, size);
        debug!("{}", self.build_state());
        if size == 0 {
            return  Err(ArraySizeLessThanOne)
        }
        let index = self.memory.add(default_value.clone());
        for i in 1..size{
            self.set_to_index(i + index, default_value.clone());
        };
        
        self.memory.stack_pointer += size-1;
        
        Ok(index)
    }

    fn free_scope(&mut self) {
        if self.symbol_tables.len() <= 1 {
            return; // Don't free the root scope
        }

        let current_table = self.symbol_tables.pop().unwrap();
        self.memory.free(current_table.start_pointer);
    }
    
    fn build_state(&self) -> String  {
        let mut res = String::new();
        for element in &self.memory.memory{
            res.push_str("|");
            let el: String = match element {
                MemoryValue::Int(value) => { format!("Int: {}", value) },
                MemoryValue::Float(value) => {format!("Float: {}", value)}
                MemoryValue::Char(value) => {format!("{}", value)}
                //MemoryValue::Array(type_array, array) => {format!("type: {:?}, content: {:?}", type_array, array)}
                MemoryValue::Pointer(type_pointer, pointer) => {format!("Pointer type: {:?}, address: {:?}", type_pointer, pointer)}
                MemoryValue::Null => { break },
                MemoryValue::Unit => { "unit".to_string()},
                MemoryValue::String(string) => { format!("String: {}", string) },
                MemoryValue::Array(_,_) => unreachable!(),
            };
            res.push_str(el.clone().as_str());
        }
        res.push_str("|");
        res
    }
    
    fn print_state(&self) {
        if !PRINT_MEMORY {
            return;
        }
        for table in self.symbol_tables.iter() {
            println!("{:?}", table);
        }
        println!("{}", self.build_state())
    }
}
fn convert_node_type<T: 'static, A: 'static>(node: &Node<T>) -> Result<&A, ErrorInterpreter> {
    if let Some(extracted_type) = (&node.node as &dyn Any).downcast_ref::<A>() {
        Ok(extracted_type)
    } else {
        Err(ErrorInterpreter::TypeConversion)
    }
}
fn _is_node_of_type<T: 'static, A: 'static>(_: &Node<T>) -> bool {
    println!("is_node_of_type");
    TypeId::of::<T>() == TypeId::of::<A>()
}

fn _is_node_of_correct_declaration<T: PartialEq + 'static, A: PartialEq + 'static>(node: &Node<T>, pattern: A) -> bool {
    if !_is_node_of_type::<T,A>(node){return false};
    let declaration= convert_node_type::<T,A>(node).expect("Could not convert node type, should never happen");
    declaration == &pattern
}

struct DebugInterpreter {
    memory_state: bool,
    source_span: bool,
    print_back: usize,
    sleep_time: usize,
    print_function_call: bool,
    auto: bool,
}
struct Interpreter  {
    functions: EnvFunction,
    memory_manager: MemoryManager,
    current_span: Span,
    source: String,
    debug: DebugInterpreter
}
impl Interpreter {
    fn new() -> Self {
        Interpreter { 
            functions: EnvFunction::new(),
            memory_manager: MemoryManager::new(),
            current_span: Span::none(),
            source: "".to_string(),
            debug: DebugInterpreter {memory_state: false, source_span: false, print_back: 0, sleep_time: 500, print_function_call: false, auto: true }
        }
    }
    fn source_highlight(&self) -> String {
        let (start, _middle) = self.source.split_at(self.current_span.start);
        let (middle, end) = _middle.split_at(self.current_span.end-self.current_span.start);
        let whole_string = format!("{}{}{}",start,middle.red(),end);
        let mut first_non_hash_found = false;
        let result: String = whole_string
            .lines()
            .filter(|line| {
                if first_non_hash_found {
                    true // Include lines after the first non-`#` line
                } else if !line.trim_start().starts_with('#') {
                    first_non_hash_found = true; // Found the first non-`#` line
                    true
                } else {
                    false // Skip lines starting with `#`
                }
            })
            .collect::<Vec<&str>>()
            .join("\n");
        result
    }
    fn state_memory(&mut self) -> String {
        let mut result = String::new();
        for (i, table) in self.memory_manager.symbol_tables.clone().iter().enumerate() {
            let mut line = format!("Symbol table {}{}:", i, if table.kind == Restricted {" restricted"} else {""});
            for (name, address) in table.current.clone() {
                line = format!("{} {}={:?} |",line, name, self.memory_manager.get_from_index(address));
            }
            result = format!("{}{}\n", result, line)
        };
        result
    }
    fn print_debug(&mut self) {
        if !self.debug.memory_state && !self.debug.source_span {return;}
        let mut debug_string = "".to_string();
        if self.debug.source_span {
            debug_string.push_str("=== SOURCE ===\n");
            debug_string.push_str(&self.source_highlight());
        }

        if self.debug.memory_state {
            debug_string.push_str("\n=== MEMORY STATE ===\n");
            debug_string.push_str(&self.state_memory());
        }
        debug_string.push_str("\n");
        if self.debug.auto {
            let duration = time::Duration::from_millis(self.debug.sleep_time as u64);
            thread::sleep(duration);
        } else {
            let mut _s = String::new();
            let _ = stdin().read_line(&mut _s);
            self.debug.print_back += 1;
        }
        print!("{}", "\x1b[A".repeat(self.debug.print_back));
        print!("{}", "                                                            \n".repeat(self.debug.print_back));
        print!("{}", "\x1b[A".repeat(self.debug.print_back));
        self.debug.print_back = debug_string.lines().count();
        print!("{}", debug_string);
    }
    fn update_span(&mut self, span: Span) {
        self.current_span = span;
        self.print_debug();
    }
    fn get_value_no_array(&self, identifier: &Identifier) -> Result<MemoryValue, ErrorInterpreter> {
        if let Some(value) = self.memory_manager.get_value(&identifier){
            Ok(value)
        }else{
            error!("Impossible to get variable {}", identifier.clone());
            Err(IdentifierNotFoundInMemory(identifier.clone()))
        }
    }
    fn get_value(&mut self, identifier: &IdentifierData) -> Result<MemoryValue, ErrorInterpreter> {
        debug!("get_value");
        if identifier.depth < 0{
            return Err(ImpossibleToGetValueFromAddress)
        };
        if identifier.array_index.is_some() && identifier.depth == 0 {
            if let Some(array_index) = identifier.array_index{
                let pointer = self.get_value_no_array(&identifier.identifier)?;
                match pointer {
                    MemoryValue::Pointer(type_pointer, address) => { Ok(MemoryValue::Pointer(type_pointer, address + array_index)) }
                    _ => Err(ImpossibleToGetValueFromAddress)
                }
            }else{
                unreachable!()
            }
        } else if identifier.depth > 0{
            if let Some(array_index) = identifier.array_index{
                self.get_value_from_pointer(&identifier.identifier, array_index, identifier.depth as usize)
            }else{
                self.get_value_from_pointer(&identifier.identifier, 0, identifier.depth as usize)
            }
        }else{
            self.get_value_no_array(&identifier.identifier)
        }
    }
    fn get_index(&mut self, identifier: &Identifier) -> Result<MemoryIndex, ErrorInterpreter> {
        if let Some(value) = self.memory_manager.get_index(&identifier){
            Ok(value)
        }else{
            error!("Impossible to get variable {}", identifier.clone());
            Err(IdentifierNotFoundInMemory(identifier.clone()))
        }
    }
    fn get_value_from_index(&mut self, index: usize, depth: usize) -> Result<MemoryValue, ErrorInterpreter>{
        assert!(depth > 0);
        let pointer = self.memory_manager.get_from_index(index);
        let pointer_address = match pointer{
            MemoryValue::Pointer(_, address) => address,
            _ => return Err(NotAPointer)
        };
        if depth == 1 {
            Ok(self.memory_manager.get_from_index(pointer_address ))
        }else {
            self.get_value_from_index(pointer_address, depth-1)
        }
    }
    fn get_value_from_pointer(&mut self, identifier: &Identifier, offset: usize, depth: usize) -> Result<MemoryValue, ErrorInterpreter> {
        let pointer = self.get_value_no_array(&identifier)?;
        let pointer_address = match pointer{
            MemoryValue::Pointer(_, address) => address,
            _ => return Err(NotAPointer)
        };
        if depth == 1 {
            Ok(self.memory_manager.get_from_index(pointer_address + offset))
        }else {
            self.get_value_from_index(pointer_address + offset, depth-1)
        }
    }
        
    
    fn set_value_at_index(&mut self, index: usize, value: MemoryValue, depth: usize) -> Result<MemoryValue, ErrorInterpreter> {
        assert!(depth > 0);
        let pointer = self.memory_manager.get_from_index(index);
        let pointer_address=  match pointer{
            MemoryValue::Pointer(type_pointer, address) => {
                if depth == 1 && !value.same_type_specifier(&type_pointer){
                    return  Err(InvalidType(format!("Impossible to change {:?} with {:?}", type_pointer, value)))
                };
                address},
            _ => return Err(NotAPointer)
        };
        if depth == 1 {
            self.memory_manager.set_to_index(pointer_address, value.clone());
            Ok(value)
        }else {
            self.set_value_at_index(pointer_address, value, depth-1)
        }
        
    }
    fn set_value_inside_pointer(&mut self, identifier: &Identifier, offset: usize, value: MemoryValue, depth: usize) -> Result<MemoryValue, ErrorInterpreter> {
        assert!(depth > 0);
        let pointer = self.get_value_no_array(identifier)?;
        let pointer_address = match pointer{
            MemoryValue::Pointer(type_pointer, address) => {
                if depth == 1 && !value.same_type_specifier(&type_pointer){
                    return  Err(InvalidType(format!("Impossible to change {:?} with {:?}", type_pointer, value)))
                };
                address},
            _ => return Err(NotAPointer)
        };
        if depth == 1 {
                self.memory_manager.set_to_index(pointer_address + offset, value.clone());
                Ok(value)
        }else { 
            self.set_value_at_index(pointer_address + offset, value, depth-1)
        }
       
    }
    fn change_value(&mut self, identifier: &IdentifierData, value: MemoryValue) -> Result<MemoryValue, ErrorInterpreter> {
        if identifier.depth< 0 ||(identifier.array_index.is_some() && identifier.depth == 0){
            return Err(ImpossibleToAssignValueToAddress)
        };
        if identifier.depth > 0 {
            if let Some(array_index) = identifier.array_index {
                self.set_value_inside_pointer(&identifier.identifier, array_index, value, identifier.depth as usize)
            }else {
                self.set_value_inside_pointer(&identifier.identifier, 0, value, identifier.depth as usize)
            }
        }else {
            self.memory_manager.change_value(&identifier.identifier, value)
        }
    }
    fn get_function_name(&mut self, function_def: &ast::FunctionDefinition) -> Result<Identifier, ErrorInterpreter>{
        let declarator = &function_def.declarator;
        self.update_span(declarator.span);
        Ok(self.declarator(&declarator)?.identifier)
    }

    fn get_function_arguments(&mut self, function_def: &ast::FunctionDefinition) -> Result<Vec<FunctionArgument>, ErrorInterpreter>{
        let declarator = &function_def.declarator.node;
        self.update_span(function_def.declarator.span);
        let nodes_arg = &declarator.derived;
        let nodes_arg = &nodes_arg.iter().find(
            |derived_decl_node|
                match derived_decl_node.node{
                    ast::DerivedDeclarator::Function(_) | ast::DerivedDeclarator::KRFunction(_) =>true,
                    _ => false
                }).expect("Function is empty, should not be possible, or I didn't understood anything").node;
        match nodes_arg {
            ast::DerivedDeclarator::Function(func_declarator) => {
                let func_declarator = &func_declarator.node;
                let parameters = &func_declarator.parameters;
                let mut function_args: Vec<FunctionArgument> = vec![];
                for parameter in parameters {
                    let parameter = &parameter.node;
                    let specifier = SpecifierInterpreter::from_vec_declaration(&parameter.specifiers)?;
                    let (identifier, specifier) = if let Some(declarator) = &parameter.declarator{
                        (Some(self.declarator(declarator)?.identifier) , self.declarator(declarator)?.to_specifier(specifier)?)
                    }else {
                        warn!("Function declarator does not have exactly an argument");
                        (None, specifier)
                    };
                    function_args.push((identifier, specifier))
                }
                Ok(function_args)
            }
            ast::DerivedDeclarator::KRFunction(identifiers) => {
                if ! identifiers.is_empty(){
                    warn!("Kr function not implemented");
                    Err(NotImplemented)
                }else{
                    Ok(Vec::new())
                }
            },
            _ => {
                warn!("Bad pattern founded while fetching arguments from function");
                Err(UnreachableReached)
            }
        }
    }
    fn get_function_body(&mut self, function_def: &ast::FunctionDefinition) -> Result<Node<Body>,ErrorInterpreter>{
        self.update_span(function_def.statement.span);
        Ok(function_def.statement.clone())
    }
    fn get_return_specifier(&mut self, function_def: &ast::FunctionDefinition ) -> Result<SpecifierInterpreter,ErrorInterpreter>{
        self.update_span(function_def.statement.span);
        let declarator = &function_def.declarator.node;
        let nodes_arg = &declarator.derived;
        let pointer_count = nodes_arg.iter().fold(0 as usize,
                                                  |acc, derived_decl_node|
                                                      match derived_decl_node.node{
                                                          DerivedDeclarator::Pointer(_) => {acc+1}
                                                          _=> acc
                                                      });
        let mut specifier = SpecifierInterpreter::from_vec_declaration(&function_def.specifiers)?;
        for _ in  0..pointer_count {
            specifier = SpecifierInterpreter::Pointer(Box::new(specifier));
        };
        Ok(specifier)
        
        
    }
    fn get_function_data<T: 'static>(&mut self, node: &Node<T>) -> Result<FunctionData, ErrorInterpreter> {
        match TypeId::of::<T>() {
            t if t == TypeId::of::<ast::ExternalDeclaration>() => {
                match convert_node_type::<T, ast::ExternalDeclaration>(node)? {
                    ast::ExternalDeclaration::Declaration(_) => {
                        Err(NotAFunction)
                    },
                    ast::ExternalDeclaration::FunctionDefinition(func) => {
                        let function_def = &func.node;
                        let name = self.get_function_name(function_def)?;
                        let arguments = self.get_function_arguments(function_def)?;
                        let body = self.get_function_body(function_def)?;
                        let return_specifier = self.get_return_specifier(function_def)?;
                        Ok((name, return_specifier, arguments, body))
                    },
                    ast::ExternalDeclaration::StaticAssert(_) => {
                        Err(NotAFunction)
                    }
                }
            }
            _ => Err(NotAFunction)
        }
    }
    fn gather_functions<T: 'static>(&mut self, nodes: &Vec<Node<T>>) -> Result<Vec<FunctionData>, ErrorInterpreter> {
        nodes.iter()
            .map(|node| self.get_function_data(&node))
            .collect::<Result<Vec<FunctionData>, ErrorInterpreter>>()
    }
    fn execute_functions(&mut self, function_identifier: Identifier, variables: Vec<MemoryValue>) -> Result<MemoryValue, ErrorInterpreter> {
        // fetch function data
        if self.debug.print_function_call {
            println!("=== Function call  ===");
            print!("Function: {}, ", function_identifier);
            print!("Arguments:");
            for variable in &variables {
                print!(" {:?} |", variable.get_string());
            }
            println!("");
        }
        let (return_specifier, body) = {
            let (_, return_specifier, function_arguments, body) = self.functions.get(&function_identifier)
                .ok_or_else(|| FunctionNotFounded(function_identifier.clone()))?;
            // if function is empty or Void just skip variable initialization
            if !(function_arguments.len() == 0) && !(function_arguments[0].1 == SpecifierInterpreter::Void) {
                // check number of arguments
                if variables.len() != function_arguments.len() {
                    return Err(IncorrectTypeOfArguments(format!("Incorrect number of variables, expected: {}, got: {}", function_arguments.len(), variables.len())));
                }
                // check if variables are valid
                for ((_, argument_specifier), given_variable_value) in function_arguments.iter().zip(&variables) {
                    if !given_variable_value.same_type_specifier(argument_specifier) {
                        return Err(IncorrectTypeOfArguments(format!("Incorrect type of argument {}, expected {:?}, found {:?}", function_identifier.clone(), argument_specifier.clone(), given_variable_value)));
                    }
                }
                self.memory_manager.push_scope(SymbolTableKind::Restricted);

                // add variables in the new scope
                for ((argument_identifier, _), variable_values) in function_arguments.iter().zip(variables) {
                    let argument_identifier = if let Some(argument_identifier) = argument_identifier {
                        argument_identifier
                    } else {
                        continue
                    };
                    self.memory_manager.create_value(argument_identifier, variable_values)?;
                }
            } else {
                self.memory_manager.push_scope(SymbolTableKind::Restricted);
            }
            (return_specifier.clone(), body.clone())
        };
        //println!("Entering function {}", function_identifier.clone());
        let function_value = self.statement(&body)
            .or_else(|error| match error {
                ReturnCalled(memory_value) => Ok(memory_value),
                other => Err(other)
            })?;
        self.memory_manager.free_scope();
        if function_value.same_type_specifier(&return_specifier) {
            Ok(function_value)
        }else { 
            Err(FunctionReturnWrongType(format!("Incorrect return type in a function got {:?} instead of type {:?}", function_value, return_specifier)))
        }
        
    }
    fn run<P: AsRef<Path>> (&mut self, file_name: P) -> MemoryValue {
        let config = Config::default();
        info!("Parsing file: {} ...", file_name.as_ref().display());
        let parse = match parse(&config, file_name){
            Ok(parse) => parse,
            Err(_error) => {
                eprintln!("Parsing failed, there is an error in your c code");
                return MemoryValue::Unit;
            }
        };
        self.source = parse.source;
        let translation_unit = parse.unit;
        let functions = translation_unit.0;
        info!("fetching functions...");
        let functions_data = match self.gather_functions(&functions) {
            Ok(functions) => {functions},
            Err(err) =>{
                error!("An error occured while gathering data from the functions");
                eprintln!("{:?}", err);
                panic!("An error occured while gathering data from the functions");
            }
            
        };
        info!(" {} function(s) loaded", functions_data.len());
        info!("saving functions...");
        for function in functions_data {
            self.functions.insert(function.0.clone(), function);
        }
        info!("functions saved");
        let (_main_identifier, main_return_specifier,  _main_arguments, main_body) = if let Some(main) = self.functions.get("main"){
            main
        }else{
            error!("No main function as been founded");
            panic!("No main function");
        };
        let main_return_specifier = main_return_specifier.clone();
        //TODO use main arguments???
        info!("Running main");
        let result = self.statement(&main_body.clone())
            .or_else(|error| match error {
            ReturnCalled(memory_value) => Ok(memory_value),
            other => Err(other)
        });
        debug!("Memory State at the end: ");
        debug!("{:?}", self.memory_manager.symbol_tables);
        debug!("{}", self.memory_manager.build_state());
        match result {
            Ok(value) => {
                let value = match value {
                    MemoryValue::Unit => {MemoryValue::Int(0)}
                    _ => {value}
                };
                info!("Program completed successfully");
                println!("Program completed successfully");
                if  main_return_specifier == SpecifierInterpreter::Void || value.same_type_specifier(&main_return_specifier) {
                    println!("Return value: '{}'", value.get_string());
                } else {
                    println!("Return value with wrong type: '{}' instead of {:?}", value.get_string(), main_return_specifier);
                }
                value
            }
            Err(err) => {
                eprintln!("An error occurred during execution");
                eprintln!("{}", self.source_highlight());
                eprintln!("{}", self.state_memory());
                eprintln!("{}", err.error_message());
                MemoryValue::Unit
            }
        }


    }
    
    fn get_pointer_content(&mut self, memory_index: MemoryIndex) -> Result<MemoryValue, ErrorInterpreter> {
        let memory_value = self.memory_manager.get_from_index(memory_index);
        match memory_value{
            MemoryValue::Pointer(_, new_pointer) => self.get_pointer_content(new_pointer),
            _ => Ok(memory_value),
        }
    }

    fn declarator_kind(&mut self, declarator_kind_node: &Node<ast::DeclaratorKind>) -> Result<Identifier, ErrorInterpreter>{
        debug!("declarator_kind");
        self.update_span(declarator_kind_node.span);
        let declarator_kind = &declarator_kind_node.node;
        match declarator_kind {
            ast::DeclaratorKind::Abstract => {
                warn!("Abstract not implemented in declarator");
                self.update_span(declarator_kind_node.span);
                Err(NotImplemented)
            }
            ast::DeclaratorKind::Identifier(identifier) => {
                Ok(identifier.node.name.clone())
            }
            ast::DeclaratorKind::Declarator(_) => {
                warn!("Declarator not implemented in declarator");
                self.update_span(declarator_kind_node.span);
                Err(NotImplemented)
            }
        }
    }
    
    fn array_declarator(&mut self, array_declarator: &Node<ast::ArrayDeclarator>) -> Result<Option<usize>, ErrorInterpreter> {
        debug!("array_declarator");
        let array_declarator = &array_declarator.node;
        if !array_declarator.qualifiers.is_empty() {
            warn!("Array qualifier not implemented in array declarator");
        };
        match &array_declarator.size {
            ArraySize::Unknown => {
                Ok(None)
            }
            ArraySize::VariableUnknown => {
                error!("You have to define the size of an array");
                Err(NotImplemented)
            }
            ArraySize::VariableExpression(expression) => {
                match self.expression_value(&expression)? {
                    MemoryValue::Int(value) => {
                        if value > 0{
                            Ok(Some(value as usize))
                        }else {
                            Err(InvalidValueForArraySize)
                        }
                    }

                    _ => Err(InvalidValueForArraySize)
                }
            }
            ArraySize::StaticExpression(_) => {
                error!("Size of array cannot be static");
                Err(NotImplemented)
            }
        }
        
    }
    
    fn derived_declarator(&mut self, derived_declarator_node: &Node<DerivedDeclarator>) -> Result<DerivedDeclaratorInterpreter, ErrorInterpreter> {
        debug!("derived_declarator");
        self.update_span(derived_declarator_node.span);
        let derived_declarator = &derived_declarator_node.node;
        match derived_declarator {
            DerivedDeclarator::Pointer(_pointer) => {
                Ok(DerivedDeclaratorInterpreter::Pointer)
            }
            DerivedDeclarator::Array(array) => {
                let size = self.array_declarator(array)?;

                Ok(DerivedDeclaratorInterpreter::Array(size))
            }
            DerivedDeclarator::Function(_) => Ok(DerivedDeclaratorInterpreter::Function),
            DerivedDeclarator::KRFunction(_) => Ok(DerivedDeclaratorInterpreter::Function),
            DerivedDeclarator::Block(_) => {
                error!("Block not implemented in derived_declarator");
                self.update_span(derived_declarator_node.span);
                Err(NotImplemented)
            }
        }
        
        
        
    }
    fn declarator(&mut self, declarator_node: &Node<ast::Declarator>) -> Result<DeclaratorInterpreter, ErrorInterpreter> {
        debug!("Declarator");
        self.update_span(declarator_node.span);
        let declarator = &declarator_node.node;
        let derived_list = &declarator.derived;
        let mut declarator_interpreter = DeclaratorInterpreter{
            identifier: "".to_string(),
            array_sizes: vec![],
            n_pointers: 0,
        };
        if ! declarator.derived.is_empty(){
            for derived_declarator in derived_list{
                match self.derived_declarator(&derived_declarator)?{
                    DerivedDeclaratorInterpreter::Pointer => declarator_interpreter.n_pointers+=1,
                    DerivedDeclaratorInterpreter::Array(size) => declarator_interpreter.array_sizes.push(size),
                    DerivedDeclaratorInterpreter::Function => {}
                };
            }
            
        };
        if !declarator.extensions.is_empty(){
            warn!("Declarator extensions not implemented, don't no what it is used for");
        };
        
        let identifier = self.declarator_kind(&declarator.kind)?;
        declarator_interpreter.identifier = identifier;
        Ok(declarator_interpreter)
    }
    fn binary_operator_expression_identifier(&mut self, binary_operator_expression_node: &Node<BinaryOperatorExpression>) -> Result<IdentifierData, ErrorInterpreter> {
        debug!("binary_operator_expression_identifier");
        self.update_span(binary_operator_expression_node.span);
        let binary_operator_expression = &binary_operator_expression_node.node;
        match binary_operator_expression.operator.node {
            BinaryOperator::Index => {
                let mut lhs = self.expression_identifier(&binary_operator_expression.lhs)?;
                let array =  match self.expression_value(&binary_operator_expression.rhs)?{
                    MemoryValue::Int(value) => {
                        Some(value as usize)
                    },
                    _ => return Err(InvalidValueForArraySize)
                };
                lhs.array_index = array;
                lhs.depth += 1;
                Ok(lhs)
            },
            
            
            _ => {
                
                Err(NoIdentifierCanBeExtract)
            }
        } 
    }
    fn get_operand_value(&mut self, lhs: &IdentifierData) -> Result<MemoryValue, ErrorInterpreter> {
        self.get_value(&lhs)
    }
    fn store_operand_result(&mut self, lhs: &IdentifierData, result: MemoryValue) -> Result<MemoryValue, ErrorInterpreter>  {
        self.change_value(&lhs, result)
    }
    fn binary_operator_expression_value(&mut self, binary_operator_expression_node: &Node<BinaryOperatorExpression>) -> Result<MemoryValue, ErrorInterpreter> {
        debug!("binary_operator_expression_value");
        self.update_span(binary_operator_expression_node.span);
        let binary_operator_expression = &binary_operator_expression_node.node;
        match binary_operator_expression.operator.node{
            BinaryOperator::Index => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (&lhs, rhs) {
                    (MemoryValue::Pointer(_, index), MemoryValue::Int(v)) => {
                        self.get_pointer_content(index + v as usize)
                    }
                    (MemoryValue::Pointer(_,_), _) => {
                        error!("BinaryOperatorExpression rhs is not a valid index");
                        Err(IncorrectTypeBinaryOperation("Invalid index type".into()))
                    }
                    _ => {
                        println!("{:#?}", lhs);
                        error!("BinaryOperatorExpression lhs is not a pointer");
                        Err(IncorrectTypeBinaryOperation("Not an array".into()))
                    }
                }
            }
            BinaryOperator::Multiply => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int(l * r)),
                    (MemoryValue::Float(l), MemoryValue::Float(r)) => Ok(MemoryValue::Float(l * r)),
                    (MemoryValue::Float(l), MemoryValue::Int(r)) | (MemoryValue::Int(r), MemoryValue::Float(l)) =>
                        Ok(MemoryValue::Float(l * r as f64)),
                    _ => Err(InvalidMultiplication)
                }
            }
            BinaryOperator::Divide => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) if r != 0 => Ok(MemoryValue::Int(l / r)),
                    (MemoryValue::Float(l), MemoryValue::Float(r)) if r != 0.0 => Ok(MemoryValue::Float(l / r)),
                    (MemoryValue::Float(l), MemoryValue::Int(r)) if r != 0 => Ok(MemoryValue::Float(l / r as f64)),
                    (MemoryValue::Int(l), MemoryValue::Float(r)) if r != 0.0 => Ok(MemoryValue::Float(l as f64 / r)),
                    (_, MemoryValue::Int(r)) if r == 0 => Err(DivisionByZero),
                    (_, MemoryValue::Float(r)) if r == 0.0 => Err(DivisionByZero),
                    _ => Err(InvalidDivision)
                }
            }
            BinaryOperator::Modulo => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) if r != 0 => Ok(MemoryValue::Int(l % r)),
                    (MemoryValue::Float(l), MemoryValue::Float(r)) if r != 0.0 => Ok(MemoryValue::Float(l % r)),
                    (MemoryValue::Float(l), MemoryValue::Int(r)) if r != 0 => Ok(MemoryValue::Float(l % r as f64)),
                    (MemoryValue::Int(l), MemoryValue::Float(r)) if r != 0.0 => Ok(MemoryValue::Float(l as f64 % r)),
                    (_, MemoryValue::Int(r)) if r == 0 => Err(ModuloByZero),
                    (_, MemoryValue::Float(r)) if r == 0.0 => Err(ModuloByZero),
                    _ => Err(InvalidModulo)
                }
            }
            BinaryOperator::Plus => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int(l + r)),
                    (MemoryValue::Float(l), MemoryValue::Float(r)) => Ok(MemoryValue::Float(l + r)),
                    (MemoryValue::Float(l), MemoryValue::Int(r)) | (MemoryValue::Int(r), MemoryValue::Float(l)) =>
                        Ok(MemoryValue::Float(l + r as f64)),
                    _ => Err(InvalidAddition)
                }
            }
            BinaryOperator::Minus => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int(l - r)),
                    (MemoryValue::Float(l), MemoryValue::Float(r)) => Ok(MemoryValue::Float(l - r)),
                    (MemoryValue::Float(l), MemoryValue::Int(r)) | (MemoryValue::Int(r), MemoryValue::Float(l)) =>
                        Ok(MemoryValue::Float(l - r as f64)),
                    _ => Err(InvalidSubtraction)
                }
            }
            BinaryOperator::ShiftLeft => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) if r >= 0 => Ok(MemoryValue::Int(l << r as u32)),
                    _ => Err(InvalidBitShift)
                }
            }
            BinaryOperator::ShiftRight => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) if r >= 0 => Ok(MemoryValue::Int(l >> r as u32)),
                    _ => Err(InvalidBitShift)
                }
            }
            BinaryOperator::Less => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int((l < r) as i64)),
                    (MemoryValue::Float(l), MemoryValue::Float(r)) => Ok(MemoryValue::Int((l < r) as i64)),
                    (MemoryValue::Float(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int((l < r as f64) as i64)),
                    (MemoryValue::Int(l), MemoryValue::Float(r)) => Ok(MemoryValue::Int(((l as f64) < r) as i64)),
                    _ => Err(InvalidComparison)
                }
            }
            BinaryOperator::Greater => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int((l > r) as i64)),
                    (MemoryValue::Float(l), MemoryValue::Float(r)) => Ok(MemoryValue::Int((l > r) as i64)),
                    (MemoryValue::Float(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int((l > r as f64) as i64)),
                    (MemoryValue::Int(l), MemoryValue::Float(r)) => Ok(MemoryValue::Int((l as f64 > r) as i64)),
                    _ => Err(InvalidComparison)
                }
            }
            BinaryOperator::LessOrEqual => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int((l <= r) as i64)),
                    (MemoryValue::Float(l), MemoryValue::Float(r)) => Ok(MemoryValue::Int((l <= r) as i64)),
                    (MemoryValue::Float(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int((l <= r as f64) as i64)),
                    (MemoryValue::Int(l), MemoryValue::Float(r)) => Ok(MemoryValue::Int((l as f64 <= r) as i64)),
                    _ => Err(InvalidComparison)
                }
            }
            BinaryOperator::GreaterOrEqual => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int((l >= r) as i64)),
                    (MemoryValue::Float(l), MemoryValue::Float(r)) => Ok(MemoryValue::Int((l >= r) as i64)),
                    (MemoryValue::Float(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int((l >= r as f64) as i64)),
                    (MemoryValue::Int(l), MemoryValue::Float(r)) => Ok(MemoryValue::Int((l as f64 >= r) as i64)),
                    _ => Err(InvalidComparison)
                }
            }
            BinaryOperator::Equals => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int((l == r) as i64)),
                    (MemoryValue::Float(l), MemoryValue::Float(r)) => Ok(MemoryValue::Int((l == r) as i64)),
                    (MemoryValue::Float(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int((l == r as f64) as i64)),
                    (MemoryValue::Int(l), MemoryValue::Float(r)) => Ok(MemoryValue::Int((l as f64 == r) as i64)),
                    (MemoryValue::Unit, MemoryValue::Unit) => Ok(MemoryValue::Int(1)),
                    (MemoryValue::Null, MemoryValue::Null) => Ok(MemoryValue::Int(1)),
                    _ => Ok(MemoryValue::Int(0))
                }
            }
            BinaryOperator::NotEquals => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int((l != r) as i64)),
                    (MemoryValue::Float(l), MemoryValue::Float(r)) => Ok(MemoryValue::Int((l != r) as i64)),
                    (MemoryValue::Float(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int((l != r as f64) as i64)),
                    (MemoryValue::Int(l), MemoryValue::Float(r)) => Ok(MemoryValue::Int((l as f64 != r) as i64)),
                    (MemoryValue::Unit, MemoryValue::Unit) => Ok(MemoryValue::Int(0)),
                    (MemoryValue::Null, MemoryValue::Null) => Ok(MemoryValue::Int(0)),
                    _ => Ok(MemoryValue::Int(1))
                }
            }
            BinaryOperator::BitwiseAnd => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int(l & r)),
                    _ => Err(InvalidBitwiseOperation)
                }
            }
            BinaryOperator::BitwiseXor => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int(l ^ r)),
                    _ => Err(InvalidBitwiseOperation)
                }
            }
            BinaryOperator::BitwiseOr => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int(l | r)),
                    _ => Err(InvalidBitwiseOperation)
                }
            }
            BinaryOperator::LogicalAnd => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                match lhs {
                    MemoryValue::Int(l) => if l == 0{
                        return  Ok(MemoryValue::Int(0))
                    }
                    _ => return Err(InvalidLogicalOperation)
                }
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int(((l != 0) && (r != 0)) as i64)),
                    _ => Err(InvalidLogicalOperation)
                }
            }
            BinaryOperator::LogicalOr => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                match lhs {
                    MemoryValue::Int(l) => if l != 0{
                        return  Ok(MemoryValue::Int(l))
                    }
                    _ => return Err(InvalidLogicalOperation)
                }
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.update_span(binary_operator_expression_node.span);
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int(((l != 0) || (r != 0)) as i64)),
                    _ => Err(InvalidLogicalOperation)
                }
            }
            BinaryOperator::Assign => {
                let lhs = self.expression_identifier(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                self.change_value(&lhs, rhs)
                
            }
            BinaryOperator::AssignMultiply => {
                let lhs = self.expression_identifier(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                let current = self.get_operand_value(&lhs)?;
                self.update_span(binary_operator_expression_node.span);
                let result = match (current, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => MemoryValue::Int(l * r),
                    (MemoryValue::Float(l), MemoryValue::Float(r)) => MemoryValue::Float(l * r),
                    (MemoryValue::Float(l), MemoryValue::Int(r)) => MemoryValue::Float(l * r as f64),
                    (MemoryValue::Int(l), MemoryValue::Float(r)) => MemoryValue::Float(l as f64 * r),
                    _ => return Err(InvalidMultiplication)
                };
                self.store_operand_result(&lhs, result)?;
                Ok(MemoryValue::Unit)
            },

            BinaryOperator::AssignDivide => {
                let lhs = self.expression_identifier(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                let current = self.get_operand_value(&lhs)?;
                self.update_span(binary_operator_expression_node.span);
                let result = match (current, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) if r != 0 => MemoryValue::Int(l / r),
                    (MemoryValue::Float(l), MemoryValue::Float(r)) if r != 0.0 => MemoryValue::Float(l / r),
                    (MemoryValue::Float(l), MemoryValue::Int(r)) if r != 0 => MemoryValue::Float(l / r as f64),
                    (_, MemoryValue::Int(0)) => return Err(DivisionByZero),
                    (_, MemoryValue::Float(0.0)) => return Err(DivisionByZero),
                    _ => return Err(InvalidDivision)
                };
                self.store_operand_result(&lhs, result)?;
                Ok(MemoryValue::Unit)
            },

            BinaryOperator::AssignModulo => {
                let lhs = self.expression_identifier(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                let current = self.get_operand_value(&lhs)?;
                self.update_span(binary_operator_expression_node.span);
                let result = match (current, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) if r != 0 => MemoryValue::Int(l % r),
                    (MemoryValue::Float(l), MemoryValue::Float(r)) if r != 0.0 => MemoryValue::Float(l % r),
                    (MemoryValue::Float(l), MemoryValue::Int(r)) if r != 0 => MemoryValue::Float(l % r as f64),
                    (MemoryValue::Int(l), MemoryValue::Float(r)) if r != 0.0 => MemoryValue::Float(l as f64 % r),
                    (_, MemoryValue::Int(0)) => return Err(ModuloByZero),
                    (_, MemoryValue::Float(0.0)) => return Err(ModuloByZero),
                    _ => return Err(InvalidModulo)
                };
                self.store_operand_result(&lhs, result)?;
                Ok(MemoryValue::Unit)
            },

            BinaryOperator::AssignPlus => {
                let lhs = self.expression_identifier(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                let current = self.get_operand_value(&lhs)?;
                self.update_span(binary_operator_expression_node.span);
                let result = match (current, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => MemoryValue::Int(l + r),
                    (MemoryValue::Float(l), MemoryValue::Float(r)) => MemoryValue::Float(l + r),
                    (MemoryValue::Float(l), MemoryValue::Int(r)) => MemoryValue::Float(l + r as f64),
                    (MemoryValue::Int(l), MemoryValue::Float(r)) => MemoryValue::Float(l as f64 + r),
                    _ => return Err(InvalidAddition)
                };
                self.store_operand_result(&lhs, result)?;
                Ok(MemoryValue::Unit)
            },

            BinaryOperator::AssignMinus => {
                let lhs = self.expression_identifier(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                let current = self.get_operand_value(&lhs)?;
                self.update_span(binary_operator_expression_node.span);
                let result = match (current, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => MemoryValue::Int(l - r),
                    (MemoryValue::Float(l), MemoryValue::Float(r)) => MemoryValue::Float(l - r),
                    (MemoryValue::Float(l), MemoryValue::Int(r)) => MemoryValue::Float(l - r as f64),
                    (MemoryValue::Int(l), MemoryValue::Float(r)) => MemoryValue::Float(l as f64 - r),
                    _ => return Err(InvalidSubtraction)
                };
                self.store_operand_result(&lhs, result)?;
                Ok(MemoryValue::Unit)
            },

            BinaryOperator::AssignShiftLeft => {
                let lhs = self.expression_identifier(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                let current = self.get_operand_value(&lhs)?;
                self.update_span(binary_operator_expression_node.span);
                let result = match (current, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) if r >= 0 => MemoryValue::Int(l << r as u32),
                    _ => return Err(InvalidBitShift)
                };
                self.store_operand_result(&lhs, result)?;
                Ok(MemoryValue::Unit)
            },

            BinaryOperator::AssignShiftRight => {
                let lhs = self.expression_identifier(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                let current = self.get_operand_value(&lhs)?;
                self.update_span(binary_operator_expression_node.span);
                let result = match (current, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) if r >= 0 => MemoryValue::Int(l >> r as u32),
                    _ => return Err(InvalidBitShift)
                };
                self.store_operand_result(&lhs, result)?;
                Ok(MemoryValue::Unit)
            },

            BinaryOperator::AssignBitwiseAnd => {
                let lhs = self.expression_identifier(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                let current = self.get_operand_value(&lhs)?;
                self.update_span(binary_operator_expression_node.span);
                let result = match (current, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => MemoryValue::Int(l & r),
                    _ => return Err(InvalidBitwiseOperation)
                };
                self.store_operand_result(&lhs, result)?;
                Ok(MemoryValue::Unit)
            },

            BinaryOperator::AssignBitwiseXor => {
                let lhs = self.expression_identifier(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                let current = self.get_operand_value(&lhs)?;
                self.update_span(binary_operator_expression_node.span);
                let result = match (current, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => MemoryValue::Int(l ^ r),
                    _ => return Err(InvalidBitwiseOperation)
                };
                self.store_operand_result(&lhs, result)?;
                Ok(MemoryValue::Unit)
            },

            BinaryOperator::AssignBitwiseOr => {
                let lhs = self.expression_identifier(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                let current = self.get_operand_value(&lhs)?;
                self.update_span(binary_operator_expression_node.span);
                let result = match (current, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => MemoryValue::Int(l | r),
                    _ => return Err(InvalidBitwiseOperation)
                };
                self.store_operand_result(&lhs, result)?;
                Ok(MemoryValue::Unit)
            }
        }
    }
    fn constant(&mut self, constant_node: &Node<ast::Constant>) -> Result<MemoryValue,ErrorInterpreter> {
        debug!("Constant");
        self.update_span(constant_node.span);
        let constant = &constant_node.node;
        match constant{
            Constant::Integer(value) => {
                //TODO use suffix
                match value.base {
                    IntegerBase::Decimal => {
                        let i: i64 = value.number.parse().map_err(|_| InvalidInt)?;
                        Ok(MemoryValue::Int(i))
                    }
                    _ => {
                        self.update_span(constant_node.span);
                        Err(BaseNotSupported)}
                }
                
            }
            Constant::Float(value) => {
                match value.base {
                    FloatBase::Decimal => {
                        let f: f64 = value.number.parse().map_err(|_| InvalidInt)?;
                        Ok(MemoryValue::Float(f))
                    }
                    FloatBase::Hexadecimal => {Err(BaseNotSupported)}
                }
            }
            Constant::Character(value) => {
                Ok(MemoryValue::Char(value.parse().unwrap()))
            }
        }
    }
    fn unary_operator(&mut self, unary_operator_node: &Node<ast::UnaryOperatorExpression>) -> Result<MemoryValue, ErrorInterpreter> {
        debug!("unary_operator");
        self.update_span(unary_operator_node.span);
        let unary_operator = &unary_operator_node.node;
       
        match unary_operator.operator.node{
            UnaryOperator::Plus => {
                let value = self.expression_value(&unary_operator.operand)?;
                match value{
                    MemoryValue::Int(_) | MemoryValue::Float(_) => { Ok(value) }
                    _ => {
                        self.update_span(unary_operator_node.span);
                        Err(InvalidPlusOperator)}
                }
            }
            UnaryOperator::Minus => {
                let value = self.expression_value(&unary_operator.operand)?;
                match value{
                    MemoryValue::Int(i)  => Ok(MemoryValue::Int(-i)),
                    MemoryValue::Float(f) => Ok(MemoryValue::Float(-f)),
                    _ => {
                        self.update_span(unary_operator_node.span);
                        Err(InvalidMinusOperator)}
                }
            }
            UnaryOperator::Negate => {
                let value = self.expression_value(&unary_operator.operand)?;
                match value{
                    MemoryValue::Int(i)  => Ok(MemoryValue::Int( if i==0 {1} else {0})),
                    MemoryValue::Float(f) => Ok(MemoryValue::Int( if f==0.0 {1} else {0})),
                    _ => {
                        self.update_span(unary_operator_node.span);
                        Err(InvalidNegateOperator)}
                }
            }
            UnaryOperator::PostIncrement => {
                let value = self.expression_value(&unary_operator.operand)?;
                let identifier = self.expression_identifier(&unary_operator.operand)?;
                match value {
                    MemoryValue::Int(value) => self.change_value(&identifier, MemoryValue::Int(value+1))?,
                    MemoryValue::Float(value) => self.change_value(&identifier, MemoryValue::Float(value+1.0))?,
                    _ => {
                        self.update_span(unary_operator_node.span);
                        return Err(ImpossibleToIncrement)
                    }
                };
                Ok(value)
            },
            UnaryOperator::PostDecrement => {
                let value = self.expression_value(&unary_operator.operand)?;
                let identifier = self.expression_identifier(&unary_operator.operand)?;
                match value {
                    MemoryValue::Int(value) => self.change_value(&identifier, MemoryValue::Int(value-1))?,
                    MemoryValue::Float(value) => self.change_value(&identifier, MemoryValue::Float(value-1.0))?,
                    _ => {
                        self.update_span(unary_operator_node.span);
                        return Err(ImpossibleToIncrement)
                    }
                };
                Ok(value)
            },
            UnaryOperator::PreIncrement => {
                let value = self.expression_value(&unary_operator.operand)?;
                let identifier = self.expression_identifier(&unary_operator.operand)?;
                let new_value = match value {
                    MemoryValue::Int(value) => {
                        let new_value = MemoryValue::Int(value+1);
                        self.change_value(&identifier, new_value.clone())?;
                        new_value
                    },
                    MemoryValue::Float(value) => {
                        let new_value = MemoryValue::Float(value+1.0);
                        self.change_value(&identifier, new_value.clone())?;
                        new_value
                    },
                    _ => {
                        self.update_span(unary_operator_node.span);
                        return Err(ImpossibleToIncrement)
                    }
                };
                Ok(new_value)
            },
            UnaryOperator::PreDecrement => {
                let value = self.expression_value(&unary_operator.operand)?;
                let identifier = self.expression_identifier(&unary_operator.operand)?;
                let new_value = match value {
                    MemoryValue::Int(value) => {
                        let new_value = MemoryValue::Int(value-1);
                        self.change_value(&identifier, new_value.clone())?;
                        new_value
                    },
                    MemoryValue::Float(value) => {
                        let new_value = MemoryValue::Float(value-1.0);
                        self.change_value(&identifier, new_value.clone())?;
                        new_value
                    },
                    _ => {
                        self.update_span(unary_operator_node.span);
                        return Err(ImpossibleToIncrement)
                    }
                };
                Ok(new_value)
            },
            UnaryOperator::Address => {
                let mut identifier = self.expression_identifier(&unary_operator.operand)?;
                if identifier.depth == 0{
                    let index = if let Some(offset) = identifier.array_index{
                        if let MemoryValue::Pointer(_, index) = self.get_value_no_array(&identifier.identifier)?{
                            index + offset
                        }else{
                            unreachable!()
                        }
                    }else {
                        self.get_index(&identifier.identifier)?
                    };
                    let pointer_specifier = self.get_value(&identifier)?.get_specifier()?;
                    Ok(MemoryValue::Pointer(pointer_specifier, index))
                }else if identifier.depth > 0 {
                    identifier.depth -= 1; //TODP
                    self.get_value(&identifier)
                }else{
                    self.update_span(unary_operator_node.span);
                    Err(ImpossibleToGetAddressOfAValue)
                }
                
            },
            UnaryOperator::Indirection => {
                let value = self.expression_value(&unary_operator.operand)?;
                match value {
                    MemoryValue::Pointer(_, index) => Ok(self.memory_manager.memory.get(index).clone()),
                    _=> {
                        self.update_span(unary_operator_node.span);
                        Err(IndirectionOnNonPointer)
                    }
                }
            },
            _ => {
                self.update_span(unary_operator_node.span);
                Err(NotImplemented)
            }
        }
        
        
    }


    fn specifier_qualifier(&mut self, specifier_quantifier_node: &Node<ast::SpecifierQualifier>) -> Result<SpecifierInterpreter, ErrorInterpreter>{
        debug!("specifier_qualifier");
        self.update_span(specifier_quantifier_node.span);
        let specifier_quantifier = &specifier_quantifier_node.node;
        match specifier_quantifier{
            SpecifierQualifier::TypeSpecifier(node) => SpecifierInterpreter::from_node(node),
            SpecifierQualifier::TypeQualifier(_) => {
                self.update_span(specifier_quantifier_node.span);
                Err(NotImplemented)},
            SpecifierQualifier::Extension(_) => {
                self.update_span(specifier_quantifier_node.span);
                Err(NotImplemented)}
        }

    }

    fn type_name(&mut self, type_name_node: &Node<ast::TypeName>) -> Result<SpecifierInterpreter, ErrorInterpreter> {
        debug!("type_name");
        self.update_span(type_name_node.span);
        let type_name = &type_name_node.node;
        if type_name.specifiers.is_empty(){
            self.update_span(type_name_node.span);
            return Err(NotTypeSpecifierInTypeName)
        }else if type_name.specifiers.len() > 1{
            warn!("To many specifer in type name, will only take the first one...");
        };
        let specifier = type_name.specifiers.first().unwrap();
        self.specifier_qualifier(specifier)



    }
    fn cast_expression(&mut self, cast_expression_node: &Node<ast::CastExpression>) -> Result<MemoryValue, ErrorInterpreter>{
        debug!("cast_expression");
        self.update_span(cast_expression_node.span);
        let cast_expression = &cast_expression_node.node;
        let specifier = self.type_name(&cast_expression.type_name)?;
        let value = self.expression_value(&cast_expression.expression)?;
        value.cast(&specifier)
    }
    
    fn printf(&self, mut args: Vec<MemoryValue>) -> Result<(), ErrorInterpreter> {
        if self.debug.print_function_call {
            println!("=== Function call  ===");
            print!("Function: printf, ");
            print!("Arguments:");
            for variable in &args {
                print!(" {:?} |", variable.get_string());
            }
            println!("");
        }
        let inital_string = match args.remove(0) {
            MemoryValue::String(value) => {value}
            _=> {return Err(InvalidArgumentsForPrintf)}
        };
        print_c_format(inital_string.clone(), args)?;
        Ok(())
    }
    fn call_expression(&mut self, call_expression_node: &Node<ast::CallExpression>) -> Result<MemoryValue, ErrorInterpreter> {
        debug!("call_expression");
        self.update_span(call_expression_node.span);
        let call_expression = &call_expression_node.node;
        let identifier = self.expression_identifier(&call_expression.callee)?;
        let arguments: Result<Vec<MemoryValue>, ErrorInterpreter> = call_expression.arguments.iter().map(|node| self.expression_value(&node)).collect();
        if identifier.identifier == "printf"{
            self.printf(arguments?)?;
            Ok(MemoryValue::Unit)
        }else {
            self.execute_functions(identifier.identifier, arguments?)
        }
    }
    fn expression_value(&mut self, expression_node: &Node<ast::Expression>) -> Result<MemoryValue, ErrorInterpreter> {
        debug!("expression_value");
        self.update_span(expression_node.span);
        let expression = &expression_node.node;
        match expression {
            ast::Expression::Identifier(identifier) => {
                self.get_value_no_array(&identifier.node.name)
            }
            ast::Expression::BinaryOperator(binary_operator) => {
                self.binary_operator_expression_value(&binary_operator)
            }
            ast::Expression::Constant(constant) => {
                self.constant(constant)
            }
            ast::Expression::UnaryOperator(unary_operator) => {
                self.unary_operator(&unary_operator)
            }
            ast::Expression::Cast(cast_expression_node) => self.cast_expression(cast_expression_node),
            ast::Expression::Call(call_expression) => self.call_expression(call_expression),
            ast::Expression::StringLiteral(string_literal) => {Ok(MemoryValue::String(string_literal.node.concat()))}
            _=> {
                warn!("Expression not implemented in expression");
                self.update_span(expression_node.span);
                Err(NotImplemented)
            }
        }
    }
    fn expression_identifier(&mut self, expression_node: &Node<ast::Expression>) -> Result<IdentifierData, ErrorInterpreter> {
        debug!("expression_identifier");
        self.update_span(expression_node.span);
        let expression = &expression_node.node;
        match expression {
            ast::Expression::Identifier(identifier) => Ok(IdentifierData::from_identifier(identifier.node.name.clone())),
            ast::Expression::BinaryOperator(binary_operator) => {
                self.binary_operator_expression_identifier(binary_operator)
            },
            ast::Expression::UnaryOperator(unary_operator) => {
                let mut identifier = self.expression_identifier(&unary_operator.node.operand)?;
                identifier.array_index.or(Some(0));
                match unary_operator.node.operator.node {
                    UnaryOperator::Address => {
                        identifier.depth-=1;
                    }
                    UnaryOperator::Indirection => {
                        identifier.depth+=1;
                    }
                    _ => return Err(WhatHaveYouDone)
                };
                Ok(identifier)
            },
            _ => {
                self.update_span(expression_node.span);
                Err(NotImplemented)
            }
        }
    }
    fn initializer(&mut self, initializer_node: &Node<ast::Initializer>) -> Result<MemoryValue, ErrorInterpreter> {
        debug!("initializer");
        self.update_span(initializer_node.span);
        let initializer = &initializer_node.node;
        match initializer {
            ast::Initializer::Expression(expression) => {self.expression_value(&expression)}
            ast::Initializer::List(initializer_list_item) => {
                let list_mem_value: Result<Vec<MemoryValue>,ErrorInterpreter> = initializer_list_item.iter().map(|init| self.initializer(&init.node.initializer)).collect();
                let list_mem_value = list_mem_value?;
                if list_mem_value.is_empty(){
                    self.update_span(initializer_node.span);
                    return Err(EmptyDeclarationArray)
                }
                let value = list_mem_value[0].get_specifier()?;
                Ok(MemoryValue::Array(value,list_mem_value))
            }
        }
    }
    fn declarators(&mut self, declarators: &Vec<Node<ast::InitDeclarator>>) -> Result<Vec<(DeclaratorInterpreter, Option<MemoryValue>)>, ErrorInterpreter> {
        debug!("declarators");
        let mut res = vec![];
        for declarator in declarators {
            debug!("In declarators");
            let init_declarator = &declarator.node;
            let declarator = &init_declarator.declarator;
            let identifier = self.declarator(&declarator)?;
            let initializer  = if let Some(init) = &init_declarator.initializer{
                Some(self.initializer(&init)?)
            }else{
                None
            };
            res.push((identifier, initializer));

        };
        Ok(res)
        
    }
    fn declaration(&mut self, declaration_node: &Node<ast::Declaration>) -> Result<MemoryValue, ErrorInterpreter> {
        debug!("Declaration");
        self.update_span(declaration_node.span);
        let declaration = &declaration_node.node;
        //int i;
        let specifier = SpecifierInterpreter::from_vec_declaration(&declaration.specifiers)?;
        let declaration: Vec<(DeclaratorInterpreter, Option<MemoryValue>)> = self.declarators(&declaration.declarators)?;
        for (declarator_interpreter, values) in declaration{
            let local_specifier = declarator_interpreter.to_specifier(specifier.clone())?;
            self.update_span(declaration_node.span);
            if let Some(values) = values{
                if !values.same_type_specifier(&local_specifier){
                  error!("Bad type during declaration of variable for {}, {:?} instead of {:?}", declarator_interpreter.identifier.clone(), values, local_specifier);

                    return Err(IncorrectTypeDeclaration(format!("Bad type during declaration of variable for {}, {:?} instead of {:?}",  declarator_interpreter.identifier.clone(), values, local_specifier)));
                }

                match values{
                    MemoryValue::Int(_) => {self.memory_manager.create_value(&declarator_interpreter.identifier, values)?;}
                    MemoryValue::Float(_) => {self.memory_manager.create_value(&declarator_interpreter.identifier, values)?;}
                    MemoryValue::Array(inside_type, values) => {
                        if declarator_interpreter.array_sizes[0].ok_or(InvalidValueForArraySize)? != values.len(){
                            self.update_span(declaration_node.span);
                            return Err(NotSameSizeArrayAndDeclarationOfArray);
                        }
                        match local_specifier {
                          SpecifierInterpreter::Pointer(inside_type) => {
                              for value in &values{
                                  if !value.same_type_specifier(&*inside_type){
                                      error!("Bad type during declaration of variable for {}, {:?} instead of {:?}", declarator_interpreter.identifier.clone(), value, &*inside_type);
                                      self.update_span(declaration_node.span);
                                      return Err(IncorrectTypeDeclaration(format!("Bad type during declaration of variable for {}, {:?} instead of {:?}",  declarator_interpreter.identifier.clone(), value, &*inside_type)));
                                  }
                              };
                          },
                          _ => unreachable!()
                        };
                        let index = self.memory_manager.add_array(&values)?;
                        self.memory_manager.create_value(&declarator_interpreter.identifier, MemoryValue::Pointer(inside_type, index))?;
                    },
                    MemoryValue::Pointer(_, _) => { self.memory_manager.create_value(&declarator_interpreter.identifier, values)?; }
                    MemoryValue::String(_) => {unreachable!()}
                    MemoryValue::Null => {self.memory_manager.create_value(&declarator_interpreter.identifier, values)?;}
                    MemoryValue::Unit => {self.memory_manager.create_value(&declarator_interpreter.identifier, values)?;}
                    _ => {}
                };
                //self.memory_manager.create_value(&declarator_interpreter.identifier, values);
            }else{
                // create default value
                let default_value = match &local_specifier{
                    SpecifierInterpreter::Int => {
                        local_specifier.default_value()}
                    SpecifierInterpreter::Float => {local_specifier.default_value()}
                    SpecifierInterpreter::Void => {local_specifier.default_value()}
                    //SpecifierInterpreter::Array(array_type) => Ok(MemoryValue::Array(*array_type.clone(), vec![array_type.clone().default_value()?;declarator_interpreter.array_sizes[0]] )),
                    SpecifierInterpreter::Pointer(pointer_type) => {
                        if declarator_interpreter.array_sizes.len() == 1{
                            let default_value = pointer_type.default_value()?;
                            let size_array = declarator_interpreter.array_sizes[0].ok_or(InvalidValueForArraySize)?;
                            let index = self.memory_manager.add_array_default(default_value, size_array)?;
                            Ok(MemoryValue::Pointer(*pointer_type.clone(), index))
                        }else if declarator_interpreter.n_pointers > 0 && declarator_interpreter.array_sizes.len() == 0{
                            local_specifier.default_value()
                        }else{
                            self.update_span(declaration_node.span);
                            Err(NotImplemented)
                        }
                    }
                }?;
                self.memory_manager.create_value(&declarator_interpreter.identifier, default_value)?;
            }
        };
        Ok(MemoryValue::Unit)
    }
    fn block_item(&mut self, block_item_node: &Node<ast::BlockItem>) -> Result<MemoryValue, ErrorInterpreter>{
        debug!("block_item");
        self.update_span(block_item_node.span);
        let block_item = &block_item_node.node;
        match block_item {
            ast::BlockItem::Declaration(declaration) => self.declaration(declaration),
            ast::BlockItem::StaticAssert(_) => Err(ErrorInterpreter::NotImplemented),
            ast::BlockItem::Statement(statement) => self.statement(statement)
        }
    }
    fn compound(&mut self, compound: &Vec<Node<ast::BlockItem>>) -> Result<MemoryValue, ErrorInterpreter> {
        debug!("compound");
        self.memory_manager.push_scope(SymbolTableKind::Scoped);
        for block_item in compound{
            self.block_item(&block_item).map_err(|err| match err {
                BreakCalled | ReturnCalled(_) => {
                    self.memory_manager.free_scope();
                    err
                },
                _ => err
            })?;
        }
        self.memory_manager.free_scope();
        Ok(MemoryValue::Unit)
    }
    fn if_statement(&mut self, if_statement: &Node<ast::IfStatement>) -> Result<MemoryValue, ErrorInterpreter> {
        debug!("if_statement");
        self.update_span(if_statement.span);
        let if_statement = &if_statement.node;
        let condition = self.expression_value(&if_statement.condition)?.evaluate_boolean_value()?;
        if condition {
            self.memory_manager.push_scope(SymbolTableKind::Scoped);
            let res = self.statement(&*if_statement.then_statement);
            self.memory_manager.free_scope();
            res
        }else { 
            if let Some(else_statement) = &if_statement.else_statement{
                self.memory_manager.push_scope(SymbolTableKind::Scoped);
                let res = self.statement(&*else_statement);
                self.memory_manager.free_scope();
                res
            }else { 
                Ok(MemoryValue::Unit)
            }
            
        }
    }
    fn for_statement(&mut self, for_statement: &Node<ast::ForStatement>) -> Result<MemoryValue, ErrorInterpreter> {
        debug!("for_statement");
        self.update_span(for_statement.span);
        self.memory_manager.push_scope(SymbolTableKind::Scoped);
        let for_statement = &for_statement.node;
        match &for_statement.initializer.node {
            ForInitializer::Empty => {return Err(NotImplemented)},
            ForInitializer::Expression(expression) => {
                let _ = self.expression_value(expression)?;},
            ForInitializer::Declaration(declaration) => {
                let _ = self.declaration(&declaration)?;}
            ForInitializer::StaticAssert(_) => {return Err(NotImplemented)}
        }
        while self.expression_value(for_statement.condition.as_ref().ok_or(ForConditionNotDefined)?)?.evaluate_boolean_value()? {
            self.memory_manager.push_scope(SymbolTableKind::Scoped);
            let res_statement = self.statement(&*for_statement.statement);
            if !res_statement.is_ok() {
                self.memory_manager.free_scope();
                if let Err(BreakCalled) = res_statement{
                    break;
                }else {
                    self.memory_manager.free_scope();
                    return res_statement;
                }
            }
            let step = for_statement.step.as_ref().ok_or(ForStepNotDefined)?;
            let expr = self.expression_value(step)?;
            self.memory_manager.free_scope();
        }
        self.memory_manager.free_scope();
        Ok(MemoryValue::Unit)

    }
    fn while_statement(&mut self, while_statement_node: &Node<ast::WhileStatement>) -> Result<MemoryValue, ErrorInterpreter> {
        debug!("for_statement");
        self.update_span(while_statement_node.span);
        let while_statement = &while_statement_node.node;
        while self.expression_value(&while_statement.expression)?.evaluate_boolean_value()? {
            self.memory_manager.push_scope(SymbolTableKind::Scoped);
            let res_statement = self.statement(&*while_statement.statement);
            if !res_statement.is_ok() {
                if let Err(BreakCalled) = res_statement{
                    break;
                }else {
                    self.memory_manager.free_scope();
                    return res_statement;
                }
            }
            self.memory_manager.free_scope();
        }
        Ok(MemoryValue::Unit)

    }
    fn statement(&mut self, statement: &Node<ast::Statement>) -> Result<MemoryValue, ErrorInterpreter> {
        debug!("statement");
        self.update_span(statement.span);
        let statement = &statement.node;
        let value = match statement {
            ast::Statement::Compound(comp) => self.compound(comp),
            ast::Statement::Expression(expression) => {
                match expression.as_ref(){
                    None => { Ok(MemoryValue::Unit)}
                    Some(expr) => {self.expression_value(expr)}
                }
            },
            ast::Statement::Return(expression) => Err(ReturnCalled(
                match expression.as_ref(){
                    None => {MemoryValue::Unit}
                    Some(expr) => {self.expression_value(expr)?}
                }
            )),
            ast::Statement::If(node_if) => self.if_statement(node_if),
            ast::Statement::For(for_statement_node) => self.for_statement(for_statement_node),
            ast::Statement::While(while_statement_node) => self.while_statement(while_statement_node),
            ast::Statement::Break => Err(BreakCalled),
            _ => return Err(NotImplemented)
        };
        value
    }
}

fn print_c_format(string: String, values: Vec<MemoryValue>) -> Result<(), ErrorInterpreter> {
    let list_c_format= ["%c","%d","%e","%f", "%lf", "%lf", "%lu", "%i", "%p", "%s"];
    let mut first_index = 0;
    let mut last_index = string.len()-1;
    if string.chars().nth(0).unwrap() == '"'{
        first_index += 1;
    };
    if string.chars().last().unwrap() == '"'{
        last_index -= 1;
    };
    let string = string.get(first_index..=last_index).unwrap();
    
    let mut parts = vec![string.to_string()];
    for delimiter in list_c_format {
        // Collect all current parts and split them further
        parts = parts.iter()
            .flat_map(|part| part.split(delimiter))
            .map(|s| s.to_string())
            .collect();
    }
    if parts.len() != values.len()+1{
        return Err(InvalidNumberArgumentPrintf);
    }
    for (value, part) in values.iter().zip(parts.iter()) {
        let value = match value {
            MemoryValue::Int(value) => {value.to_string()},
            MemoryValue::Float(value) => {value.to_string()},
            MemoryValue::Char(value) => {value.to_string()},
            MemoryValue::Pointer(_,addres) => {format!("POINTER_WITH_ADDRESS:{}*",addres)},
            MemoryValue::String(value) => {value.to_string()},
            MemoryValue::Null => {"null".to_string()},
            MemoryValue::Unit => {"unit".to_string()},
            MemoryValue::Array(_,_) => unreachable!()
        };
        let new_part = part.clone().replace(r"\n", "\n");
        print!("{}{}", new_part , value);
    }
    print!("{}", parts.last().unwrap().replace(r"\n", "\n"));
    Ok(())
}


/// Simple program to greet a person
#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Args {
    /// Path to the c file to interpret
    #[arg(short, long)]
    path: String,

    /// Print the state of the current part of the code being executed and the memory state of the symbol tables
    #[arg(short, long)]
    debug: bool,

    /// When in debug, don't print the source code
    #[arg(long)]
    disable_source: bool,

    /// When in debug, don't print the memory state of the symbol tables
    #[arg(long)]
    disable_memory: bool,

    /// Press enter between each operation for the interpreter to continue
    #[arg(short, long)]
    manually: bool,

    /// Sleep time between each step in auto mod in milliseconds (50 by default)
    #[arg(short, long)]
    sleep_time: Option<u32>,

    /// Print function call
    #[arg(long)]
    print_function_call: bool,

}

fn build_interpreter_from_args(args: &Args) -> Interpreter{
    if !args.debug && (args.disable_memory || args.manually || args.sleep_time.is_some() || args.disable_source) {
        warn!("You use debug flag not in debug, they will be ignored");
    }
    if args.debug && args.print_function_call {
        warn!("Cannot print function call when in debug mod");
    }
    let debug = if args.debug{
        if args.sleep_time.is_some() && args.manually {
            warn!("Sleep time set but you are in manual mode, sleep time will be ignore");
        };
        DebugInterpreter {
            memory_state: !args.disable_memory,
            source_span: !args.disable_source,
            print_back: 0,
            sleep_time: args.sleep_time.unwrap_or_else(|| 50) as usize,
            print_function_call: false,
            auto: !args.manually,

        }
    }else{
        DebugInterpreter {
            memory_state: false,
            source_span: false,
            print_back: 0,
            sleep_time: 0,
            print_function_call: args.print_function_call,
            auto: true,

        }
    };
    let mut interpreter = Interpreter::new();
    interpreter.debug = debug;
    interpreter
}

fn main() {
    env_logger::init();
    let args = Args::parse();
    let mut interpreter = build_interpreter_from_args(&args);
    let res = interpreter.run(args.path);
    //println!("{:?}", res);
}

#[cfg(test)]
mod tests {
    use std::cmp::PartialEq;
    use crate::{Interpreter, MemoryManager, MemoryValue};

    impl PartialEq for MemoryValue {
        fn eq(&self, other: &Self) -> bool {
            match (self, other) {
                (MemoryValue::Int(a), MemoryValue::Int(b))  => a == b,
                (MemoryValue::Float(a), MemoryValue::Float(b))  => a == b,
                (MemoryValue::Char(a), MemoryValue::Char(b))  => a == b,
                (MemoryValue::Null, MemoryValue::Null) => {true}
                (MemoryValue::Unit, MemoryValue::Unit) => {true}
                _ => false
            }
        }
    }

    #[test]
    fn empty_main() {
        let mut interpreter = Interpreter::new();
        let res = interpreter.run("./c_programs/tests/empty_main.c");
        assert_eq!(res, MemoryValue::Unit);
    }
    #[test]
    fn basic_addition(){
        let mut interpreter = Interpreter::new();
        let res = interpreter.run("./c_programs/tests/basic_addition.c");
        assert_eq!(res, MemoryValue::Int(4));
    }
    
    #[test]
    fn list_manipulation(){
        let mut interpreter = Interpreter::new();
        let res = interpreter.run("./c_programs/tests/list_manipulation.c");
        assert_eq!(res, MemoryValue::Int(60));
    }

    #[test]
    fn local_scope(){
        let mut interpreter = Interpreter::new();
        let res = interpreter.run("./c_programs/tests/local_scope.c");
        assert_eq!(res, MemoryValue::Int(3));
    }
    #[test]
    fn for_loop(){
        let mut interpreter = Interpreter::new();
        let res = interpreter.run("./c_programs/tests/for_loop.c");
        assert_eq!(res, MemoryValue::Int(20));
    }
    #[test]
    fn bubble_sort(){
        let mut interpreter = Interpreter::new();
        let res = interpreter.run("./c_programs/tests/bubble_sort.c");
        assert_eq!(res, MemoryValue::Int(6));
    }

    #[test]
    fn course_example(){
        let mut interpreter = Interpreter::new();
        let res = interpreter.run("./c_programs/tests/example.c");
        assert_eq!(res, MemoryValue::Float(45.0));
    }

    #[test]
    fn nested_return(){
        let mut interpreter = Interpreter::new();
        let res = interpreter.run("./c_programs/tests/test_nested_return.c");
        assert_eq!(res, MemoryValue::Int(5));
    }
}


