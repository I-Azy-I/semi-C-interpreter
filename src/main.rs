extern crate core;

mod parser;

use lang_c::driver::{parse, Config};
use lang_c::visit::Visit;
use std::collections::HashMap;
use std::hash::Hash;
use lang_c::span::Node;
use std::any::{Any, TypeId};
use std::cmp::PartialEq;
use std::convert::identity;
use std::path::Path;
use std::str::FromStr;
use lang_c::ast;
use log::{debug, error, info, warn};
use env_logger::{Logger, Env};
use lang_c::ast::{BinaryOperator, BinaryOperatorExpression, Constant, FloatBase, IntegerBase};
use crate::ErrorInterpreter::*;

#[derive(Debug)]
enum ErrorInterpreter{
    NotImplemented,
    TypeConversion,
    NotAFunction,
    UnreachableReached,
    MissingArgumentsFunction,
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
    InvalidInt,
}
type Int = i64;
type Float = f64;
#[derive(Debug, Clone)]
enum Value{
    Int(i64),
    Float(f64),
    Char(char),
    Array(Vec<Value>),
    Pointer(usize),
    Null,
    Unit
}
impl Value {
    fn same_type_specifier(&self, specifier: &Specifier) -> bool {
        match (self, specifier) {
            (Value::Int(_), Specifier::Int) => true,
            (Value::Float(_), Specifier::Float) => true,
            // Pointer and Array don't have corresponding specifiers in the given enum
            _ => false
        }
    }
    
}
#[derive(Debug, PartialEq)]
enum Specifier{
    Int,
    Float,
    Void,
}

impl Specifier{
    fn default_value(&self) -> Value{
        match self{
            &Specifier::Int => Value::Int(0),
            &Specifier::Float => Value::Float(0.0),
            &Specifier::Void => Value::Unit,
        }
    }
    fn fromNode(specifier: &Node<ast::TypeSpecifier>) -> Result<Specifier, ErrorInterpreter>{
        let specifier = &specifier.node;
        match specifier{
            &ast::TypeSpecifier::Int=>Ok(Specifier::Int),
            &ast::TypeSpecifier::Float=>Ok(Specifier::Float),
            &ast::TypeSpecifier::Void=>Ok(Specifier::Void),
            _=>Err(ErrorInterpreter::SpecifierNotImplemented)
        }
    }
    fn fromVecDeclaration(declaration_specifiers: &Vec<Node<ast::DeclarationSpecifier>>) -> Result<Specifier, ErrorInterpreter>{
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
                let decl_specifier = &specifier.node;;
                match decl_specifier {
                    ast::DeclarationSpecifier::TypeSpecifier(specifier) => {
                        Ok(Specifier::fromNode(specifier))?
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



type FunctionArgument = (Option<Identifier>, Specifier);
type Body = ast::Statement;
type FunctionData = (Identifier, Vec<FunctionArgument>, Body);
type Identifier = String ;

type EnvFunction = HashMap<Identifier, FunctionData>;

type MemoryIndex = usize;
struct Memory<T: Clone> {
    memory: Vec<T>,
    stack_pointer: usize,
}
impl<T: Clone> Memory<T> {
    fn new(default_value: T) -> Memory<T> {
        Memory {
            memory: vec![default_value; 1024],
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
}


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
enum SymbolTableKind {
    Restricted,
    Scoped
}

struct  MemoryManager{
    symbol_tables: Vec<SymbolTable<Identifier, MemoryIndex>>,
    memory: Memory<Value>,
}
impl MemoryManager{
    fn new() -> Self{
        let mut symbol_tables = Vec::new();
        symbol_tables.push(SymbolTable::root());
        MemoryManager{
            symbol_tables,
            memory: Memory::new(Value::Null)
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
    fn get_value(&self, identifier: &Identifier) -> Option<Value> {
        if let Some(index) = self.get_index(identifier) {
            Some(self.memory.get(index).clone())
        }else{
            None
        }
    }

    fn set_value(&mut self, identifier: &Identifier, value: Value) {
        let memory_id = self.memory.add(value);
        self.current_symbol_table_mut().save_key(identifier.clone(), memory_id);
    }
    fn change_value(&mut self, identifier: &Identifier, value: Value) -> Option<()>{
        if let Some(index) = self.get_index(identifier) {
            self.memory.change(index, value);
            Some(())
        }else{
            None
        }

    }

    fn free_scope(&mut self) {
        if self.symbol_tables.len() <= 1 {
            return; // Don't free the root scope
        }

        let current_table = self.symbol_tables.pop().unwrap();
        self.memory.free(current_table.start_pointer);
    }
}
fn convert_node_type<T: 'static, A: 'static>(node: &Node<T>) -> Result<&A, ErrorInterpreter> {
    if let Some(extracted_type) = (&node.node as &dyn Any).downcast_ref::<A>() {
        Ok(extracted_type)
    } else {
        Err(ErrorInterpreter::TypeConversion)
    }
}
fn is_node_of_type<T: 'static, A: 'static>(_: &Node<T>) -> bool {
    println!("is_node_of_type");
    TypeId::of::<T>() == TypeId::of::<A>()
}
fn is_node_of_correct_declaration<T: PartialEq + 'static, A: PartialEq + 'static>(node: &Node<T>, pattern: A) -> bool {
    if !is_node_of_type::<T,A>(node){return false};
    let declaration= convert_node_type::<T,A>(node).expect("Could not convert node type, should never happen");
    declaration == &pattern
}

fn get_function_name(function_def: &ast::FunctionDefinition) -> Result<Identifier, ErrorInterpreter>{
    let declarator = &function_def.declarator.node;
    extract_identifier_from_declarator(&declarator)
}

fn get_function_arguments(function_def: &ast::FunctionDefinition) -> Result<Vec<FunctionArgument>,ErrorInterpreter>{
    let declarator = &function_def.declarator.node;
    let nodes_arg = &declarator.derived;
    if nodes_arg.len() != 1{
        warn!("Function declarator does not have exactly one argument, et t'as rien compris chef");
        return Err(UnreachableReached);
    }
    let nodes_arg = &nodes_arg.iter().next().expect("Function declarator does not have exactly one argument").node;
    
    match nodes_arg {
        ast::DerivedDeclarator::Function(func_declarator) => {
            let func_declarator = &func_declarator.node;
            let parameters = &func_declarator.parameters;
            let mut function_args: Vec<FunctionArgument> = vec![];
            for parameter in parameters {
                let parameter = &parameter.node;
                let specifier = Specifier::fromVecDeclaration(&parameter.specifiers)?;
                let identifier = if let Some(declarator) = &parameter.declarator{
                    Some(extract_identifier_from_declarator(&declarator.node)?)
                }else {
                    warn!("Function declarator does not have exactly an argument");
                    None
                };
                function_args.push((identifier, specifier))
            }
            Ok(function_args)
        }
        _ => {
            warn!("Bad pattern founded while fetching arguments from function");
            Err(UnreachableReached)
        }
    }
}
fn get_function_body(function_def: &ast::FunctionDefinition) -> Result<Body,ErrorInterpreter>{
    Ok(function_def.statement.node.clone())
}
fn get_function_data<T: 'static>(node: &Node<T>) -> Result<FunctionData, ErrorInterpreter> {
    match TypeId::of::<T>() {
        t if t == TypeId::of::<ast::ExternalDeclaration>() => {
            match convert_node_type::<T, ast::ExternalDeclaration>(node)? {
                ast::ExternalDeclaration::Declaration(_) => {
                    Err(NotAFunction)
                },
                ast::ExternalDeclaration::FunctionDefinition(func) => {
                    let function_def = &func.node;
                    let name = get_function_name(function_def)?;
                    let arguments = get_function_arguments(function_def)?;
                    let body = get_function_body(function_def)?;
                    Ok((name, arguments, body))
                },
                ast::ExternalDeclaration::StaticAssert(_) => {
                    Err(NotAFunction)
                }
            }
        }
        _ => Err(NotAFunction)
    }
}
fn gather_functions<T: 'static>(nodes: &Vec<Node<T>>) -> Result<Vec<FunctionData>, ErrorInterpreter> {
    nodes.iter()
        .map(get_function_data)
        .collect::<Result<Vec<FunctionData>, ErrorInterpreter>>()
}

fn extract_identifier_from_declarator(declarator: &ast::Declarator) -> Result<Identifier, ErrorInterpreter>{
    let kind = &declarator.kind.node;
    match kind {
        ast::DeclaratorKind::Abstract => {
            warn!("Abstract not implemented in declarator");
            Err(ErrorInterpreter::NotImplemented)
        }
        ast::DeclaratorKind::Identifier(identifier) => {
            Ok(identifier.node.name.clone())
        }
       ast::DeclaratorKind::Declarator(_) => {
            warn!("Declarator not implemented in declarator");
            Err(ErrorInterpreter::NotImplemented)
        }
    }
}
struct Interpreter  {
    functions: EnvFunction,
    memory_manager: MemoryManager
}
impl Interpreter {
    fn new() -> Self {
        Interpreter { 
            functions: EnvFunction::new(),
            memory_manager: MemoryManager::new(),
        }
    }
    fn execute_functions(&mut self, function_identifier: Identifier, variables: Vec<Identifier>) -> Result<Value, ErrorInterpreter> {
        // fetch function data
        let (_, function_arguments, body) = self.functions.get(&function_identifier)
            .ok_or_else(|| ErrorInterpreter::FunctionNotFounded(function_identifier.clone()))?;
        // if function is empty or Void just skip variable initialization
        if  !(function_arguments.len() == 0) && !(function_arguments[0].1 == Specifier::Void){
            // check number of arguments
            if variables.len() !=  function_arguments.len() {
                return Err(IncorrectTypeOfArguments(format!("Incorrect number of variables, expected: {}, got: {}", function_arguments.len(), variables.len())));
            }
            // check if variables are valid
            for ((_, argument_specifier), given_variable_identifier) in function_arguments.iter().zip(&variables) {
                // check if can get variable from memory
                let variable_data = if let Some(variable_data) = self.memory_manager.get_value(&given_variable_identifier){
                    variable_data
                }else {
                    return Err(IdentifierNotFoundInMemory(format!("When calling {}, identifier {} not founded in memory", function_identifier.clone(), given_variable_identifier.clone())));
                };
                // check if it has correct type
                if !variable_data.same_type_specifier(argument_specifier){
                    return Err(IncorrectTypeOfArguments(format!("Incorrect type of argument {}, expected {:?}, found {:?}", function_identifier.clone(), argument_specifier.clone(), variable_data)));
                }
                // add variable in local memory
            }
            self.memory_manager.push_scope(SymbolTableKind::Restricted);

            // add variables in the new scope
            for ((argument_identifier, _), given_variable_identifier) in function_arguments.iter().zip(variables) {
                let argument_identifier = if let Some(argument_identifier) = argument_identifier {
                    argument_identifier
                }else { 
                    continue
                };
                let variable_data = if let Some(variable_data) = self.memory_manager.get_value(&given_variable_identifier){
                    variable_data
                }else {
                    return Err(IdentifierNotFoundInMemory(format!("When calling {}, identifier {} not founded in memory", function_identifier.clone(), given_variable_identifier.clone())));
                };
                self.memory_manager.set_value(argument_identifier, variable_data.clone());
            }
        }else { 
            self.memory_manager.push_scope(SymbolTableKind::Restricted);
        }
        self.statement(body.clone())
        

    }
    fn run<P: AsRef<Path>> (&mut self, file_name: P){
        let config = Config::default();
        info!("Parsing file: {} ...", file_name.as_ref().display());
        let parse = parse(&config, file_name).expect("Error in file c");
        
        let translation_unit = parse.unit;
        println!("{:#?}", translation_unit);
        let functions = translation_unit.0;
        info!("fetching functions...");
        let functions_data = match gather_functions(&functions) {
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
        let (main_identifier, main_arguments, main_body) = if let Some(main) = self.functions.get("main"){
            main
        }else{
            error!("No main function");
            panic!("No main function");
        };

        //TODO use main arguments???
        info!("Running main");
        let result = self.statement(main_body.clone());
        match result {
            Ok(value) => {
                println!("Program completed successfully");
                println!("{:#?}", value);
            }
            Err(err) => {
                eprintln!("An error occurred during execution");
                eprintln!("{:?}", err);
            }
        }
    }

    fn declarator_kind(&mut self, declarator_kind: ast::DeclaratorKind) -> Result<Identifier, ErrorInterpreter>{
        debug!("declarator_kind");
        match declarator_kind {
            ast::DeclaratorKind::Abstract => {
                warn!("Abstract not implemented in declarator");
                Err(NotImplemented)
            }
            ast::DeclaratorKind::Identifier(identifier) => {
                Ok(identifier.node.name.clone())
            }
            ast::DeclaratorKind::Declarator(_) => {
                warn!("Declarator not implemented in declarator");
                Err(NotImplemented)
            }
        }
    }

    fn declarator(&mut self, declarator: ast::Declarator) -> Result<Identifier, ErrorInterpreter> {
        debug!("Declarator");
        if ! declarator.derived.is_empty(){
            // TODO implementation for array and pointer
            warn!("Declarator derived not implemented (for array, pointers, ...)");
        };
        if !declarator.extensions.is_empty(){
            warn!("Declarator extensions not implemented, don't no what it is used for");
        };
        self.declarator_kind(declarator.kind.node)
    }
    fn binary_operator_expression(&mut self, binary_operator_expression: BinaryOperatorExpression) -> Result<Value, ErrorInterpreter> {
        debug!("binary_operator_expression");
        match binary_operator_expression.operator.node{
            BinaryOperator::Index => {
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Array(arr), Value::Int(v)) => {
                        let index = v as usize;
                        arr.get(index)
                            .cloned()
                            .ok_or_else(|| {
                                error!("Index out of bound");
                                IndexOutOfBounds
                            })
                    }
                    (Value::Array(_), _) => {
                        error!("BinaryOperatorExpression rhs is not a valid index");
                        Err(IncorrectTypeBinaryOperation("Invalid index type".into()))
                    }
                    _ => {
                        error!("BinaryOperatorExpression lhs is not an array");
                        Err(IncorrectTypeBinaryOperation("Not an array".into()))
                    }
                }
            }
            BinaryOperator::Multiply => {
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) => Ok(Value::Int(l * r)),
                    (Value::Float(l), Value::Float(r)) => Ok(Value::Float(l * r)),
                    (Value::Float(l), Value::Int(r)) | (Value::Int(r), Value::Float(l)) =>
                        Ok(Value::Float(l * r as f64)),
                    _ => Err(InvalidMultiplication)
                }
            }
            BinaryOperator::Divide => {
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) if r != 0 => Ok(Value::Int(l / r)),
                    (Value::Float(l), Value::Float(r)) if r != 0.0 => Ok(Value::Float(l / r)),
                    (Value::Float(l), Value::Int(r)) if r != 0 => Ok(Value::Float(l / r as f64)),
                    (Value::Int(l), Value::Float(r)) if r != 0.0 => Ok(Value::Float(l as f64 / r)),
                    (_, Value::Int(r)) if r == 0 => Err(DivisionByZero),
                    (_, Value::Float(r)) if r == 0.0 => Err(DivisionByZero),
                    _ => Err(InvalidDivision)
                }
            }
            BinaryOperator::Modulo => {
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) if r != 0 => Ok(Value::Int(l % r)),
                    (Value::Float(l), Value::Float(r)) if r != 0.0 => Ok(Value::Float(l % r)),
                    (Value::Float(l), Value::Int(r)) if r != 0 => Ok(Value::Float(l % r as f64)),
                    (Value::Int(l), Value::Float(r)) if r != 0.0 => Ok(Value::Float(l as f64 % r)),
                    (_, Value::Int(r)) if r == 0 => Err(ModuloByZero),
                    (_, Value::Float(r)) if r == 0.0 => Err(ModuloByZero),
                    _ => Err(InvalidModulo)
                }
            }
            BinaryOperator::Plus => {
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) => Ok(Value::Int(l + r)),
                    (Value::Float(l), Value::Float(r)) => Ok(Value::Float(l + r)),
                    (Value::Float(l), Value::Int(r)) | (Value::Int(r), Value::Float(l)) =>
                        Ok(Value::Float(l + r as f64)),
                    _ => Err(InvalidAddition)
                }
            }
            BinaryOperator::Minus => {
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) => Ok(Value::Int(l - r)),
                    (Value::Float(l), Value::Float(r)) => Ok(Value::Float(l - r)),
                    (Value::Float(l), Value::Int(r)) | (Value::Int(r), Value::Float(l)) =>
                        Ok(Value::Float(l - r as f64)),
                    _ => Err(InvalidSubtraction)
                }
            }
            BinaryOperator::ShiftLeft => {
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) if r >= 0 => Ok(Value::Int(l << r as u32)),
                    _ => Err(InvalidBitShift)
                }
            }
            BinaryOperator::ShiftRight => {
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) if r >= 0 => Ok(Value::Int(l >> r as u32)),
                    _ => Err(InvalidBitShift)
                }
            }
            BinaryOperator::Less => {
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) => Ok(Value::Int((l < r) as i64)),
                    (Value::Float(l), Value::Float(r)) => Ok(Value::Int((l < r) as i64)),
                    (Value::Float(l), Value::Int(r)) => Ok(Value::Int((l < r as f64) as i64)),
                    (Value::Int(l), Value::Float(r)) => Ok(Value::Int(((l as f64) < r) as i64)),
                    _ => Err(InvalidComparison)
                }
            }
            BinaryOperator::Greater => {
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) => Ok(Value::Int((l > r) as i64)),
                    (Value::Float(l), Value::Float(r)) => Ok(Value::Int((l > r) as i64)),
                    (Value::Float(l), Value::Int(r)) => Ok(Value::Int((l > r as f64) as i64)),
                    (Value::Int(l), Value::Float(r)) => Ok(Value::Int((l as f64 > r) as i64)),
                    _ => Err(InvalidComparison)
                }
            }
            BinaryOperator::LessOrEqual => {
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) => Ok(Value::Int((l <= r) as i64)),
                    (Value::Float(l), Value::Float(r)) => Ok(Value::Int((l <= r) as i64)),
                    (Value::Float(l), Value::Int(r)) => Ok(Value::Int((l <= r as f64) as i64)),
                    (Value::Int(l), Value::Float(r)) => Ok(Value::Int((l as f64 <= r) as i64)),
                    _ => Err(InvalidComparison)
                }
            }
            BinaryOperator::GreaterOrEqual => {
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) => Ok(Value::Int((l >= r) as i64)),
                    (Value::Float(l), Value::Float(r)) => Ok(Value::Int((l >= r) as i64)),
                    (Value::Float(l), Value::Int(r)) => Ok(Value::Int((l >= r as f64) as i64)),
                    (Value::Int(l), Value::Float(r)) => Ok(Value::Int((l as f64 >= r) as i64)),
                    _ => Err(InvalidComparison)
                }
            }
            BinaryOperator::Equals => {
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) => Ok(Value::Int((l == r) as i64)),
                    (Value::Float(l), Value::Float(r)) => Ok(Value::Int((l == r) as i64)),
                    (Value::Float(l), Value::Int(r)) => Ok(Value::Int((l == r as f64) as i64)),
                    (Value::Int(l), Value::Float(r)) => Ok(Value::Int((l as f64 == r) as i64)),
                    (Value::Unit, Value::Unit) => Ok(Value::Int(1)),
                    (Value::Null, Value::Null) => Ok(Value::Int(1)),
                    _ => Ok(Value::Int(0))
                }
            }
            BinaryOperator::NotEquals => {
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) => Ok(Value::Int((l != r) as i64)),
                    (Value::Float(l), Value::Float(r)) => Ok(Value::Int((l != r) as i64)),
                    (Value::Float(l), Value::Int(r)) => Ok(Value::Int((l != r as f64) as i64)),
                    (Value::Int(l), Value::Float(r)) => Ok(Value::Int((l as f64 != r) as i64)),
                    (Value::Unit, Value::Unit) => Ok(Value::Int(0)),
                    (Value::Null, Value::Null) => Ok(Value::Int(0)),
                    _ => Ok(Value::Int(1))
                }
            }
            BinaryOperator::BitwiseAnd => {
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) => Ok(Value::Int(l & r)),
                    _ => Err(InvalidBitwiseOperation)
                }
            }
            BinaryOperator::BitwiseXor => {
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) => Ok(Value::Int(l ^ r)),
                    _ => Err(InvalidBitwiseOperation)
                }
            }
            BinaryOperator::BitwiseOr => {
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) => Ok(Value::Int(l | r)),
                    _ => Err(InvalidBitwiseOperation)
                }
            }
            BinaryOperator::LogicalAnd => {
                // TODO evaluate at first lhs
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) => Ok(Value::Int(((l != 0) && (r != 0)) as i64)),
                    _ => Err(InvalidLogicalOperation)
                }
            }
            BinaryOperator::LogicalOr => {
                // TODO evaluate at first lhs
                let lhs = self.expression_value(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                match (lhs, rhs) {
                    (Value::Int(l), Value::Int(r)) => Ok(Value::Int(((l != 0) || (r != 0)) as i64)),
                    _ => Err(InvalidLogicalOperation)
                }
            }
            BinaryOperator::Assign => {
                let lhs = self.expression_identifier(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                self.memory_manager.change_value(&lhs, rhs);
                Ok(Value::Unit)
            }
            BinaryOperator::AssignMultiply => {
                let lhs = self.expression_identifier(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                let current = self.memory_manager.get_value(&lhs)
                    .ok_or(IdentifierNotFoundInMemory(lhs.clone()))?;
                let result = match (current, rhs) {
                    (Value::Int(l), Value::Int(r)) => Value::Int(l * r),
                    (Value::Float(l), Value::Float(r)) => Value::Float(l * r),
                    (Value::Float(l), Value::Int(r)) => Value::Float(l * r as f64),
                    (Value::Int(l), Value::Float(r)) => Value::Float(l as f64 * r),
                    _ => return Err(InvalidMultiplication)
                };
                self.memory_manager.change_value(&lhs, result);
                Ok(Value::Unit)
            }
            BinaryOperator::AssignDivide => {
                let lhs = self.expression_identifier(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                let current =  self.memory_manager.get_value(&lhs)
                    .ok_or(IdentifierNotFoundInMemory(lhs.clone()))?;
                let result = match (current, rhs) {
                    (Value::Int(l), Value::Int(r)) if r != 0 => Value::Int(l / r),
                    (Value::Float(l), Value::Float(r)) if r != 0.0 => Value::Float(l / r),
                    (Value::Float(l), Value::Int(r)) if r != 0 => Value::Float(l / r as f64),
                    (_, Value::Int(0)) => return Err(DivisionByZero),
                    (_, Value::Float(0.0)) => return Err(DivisionByZero),
                    _ => return Err(InvalidDivision)
                };
                self.memory_manager.change_value(&lhs, result);
                Ok(Value::Unit)
            }
            BinaryOperator::AssignModulo => {
                let lhs = self.expression_identifier(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                let current =  self.memory_manager.get_value(&lhs)
                    .ok_or(IdentifierNotFoundInMemory(lhs.clone()))?;
                let result = match (current, rhs) {
                    (Value::Int(l), Value::Int(r)) if r != 0 => Value::Int(l % r),
                    (Value::Float(l), Value::Float(r)) if r != 0.0 => Value::Float(l % r),
                    (Value::Float(l), Value::Int(r)) if r != 0 => Value::Float(l % r as f64),
                    (Value::Int(l), Value::Float(r)) if r != 0.0 => Value::Float(l as f64 % r),
                    (_, Value::Int(0))  => return Err(ModuloByZero),
                    (_, Value::Float(0.0))  => return Err(ModuloByZero),
                    _ => return Err(InvalidModulo)
                };
                self.memory_manager.change_value(&lhs, result);
                Ok(Value::Unit)
            }
            BinaryOperator::AssignPlus => {
                let lhs = self.expression_identifier(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                let current = self.memory_manager.get_value(&lhs)
                    .ok_or(IdentifierNotFoundInMemory(lhs.clone()))?;
                let result = match (current, rhs) {
                    (Value::Int(l), Value::Int(r)) => Value::Int(l + r),
                    (Value::Float(l), Value::Float(r)) => Value::Float(l + r),
                    (Value::Float(l), Value::Int(r)) => Value::Float(l + r as f64),
                    (Value::Int(l), Value::Float(r)) => Value::Float(l as f64 + r),
                    _ => return Err(InvalidAddition)
                };
                self.memory_manager.change_value(&lhs, result);
                Ok(Value::Unit)
            }
            BinaryOperator::AssignMinus => {
                let lhs = self.expression_identifier(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                let current = self.memory_manager.get_value(&lhs)
                    .ok_or(IdentifierNotFoundInMemory(lhs.clone()))?;
                let result = match (current, rhs) {
                    (Value::Int(l), Value::Int(r)) => Value::Int(l - r),
                    (Value::Float(l), Value::Float(r)) => Value::Float(l - r),
                    (Value::Float(l), Value::Int(r)) => Value::Float(l - r as f64),
                    (Value::Int(l), Value::Float(r)) => Value::Float(l as f64 - r),
                    _ => return Err(InvalidSubtraction)
                };
                self.memory_manager.change_value(&lhs, result);
                Ok(Value::Unit)
            }
            BinaryOperator::AssignShiftLeft => {
                let lhs = self.expression_identifier(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                let current = self.memory_manager.get_value(&lhs)
                    .ok_or(IdentifierNotFoundInMemory(lhs.clone()))?;
                let result = match (current, rhs) {
                    (Value::Int(l), Value::Int(r)) if r >= 0 => Value::Int(l << r as u32),
                    _ => return Err(InvalidBitShift)
                };
                self.memory_manager.change_value(&lhs, result);
                Ok(Value::Unit)
            }
            BinaryOperator::AssignShiftRight => {
                let lhs = self.expression_identifier(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                let current =  self.memory_manager.get_value(&lhs)
                    .ok_or(IdentifierNotFoundInMemory(lhs.clone()))?;
                let result = match (current, rhs) {
                    (Value::Int(l), Value::Int(r)) if r >= 0 => Value::Int(l >> r as u32),
                    _ => return Err(InvalidBitShift)
                };
                self.memory_manager.change_value(&lhs, result);
                Ok(Value::Unit)
            }
            BinaryOperator::AssignBitwiseAnd => {
                let lhs = self.expression_identifier(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                let current =  self.memory_manager.get_value(&lhs)
                    .ok_or(IdentifierNotFoundInMemory(lhs.clone()))?;
                let result = match (current, rhs) {
                    (Value::Int(l), Value::Int(r)) => Value::Int(l & r),
                    _ => return Err(InvalidBitwiseOperation)
                };
                self.memory_manager.change_value(&lhs, result);
                Ok(Value::Unit)
            }
            BinaryOperator::AssignBitwiseXor => {
                let lhs = self.expression_identifier(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                let current =  self.memory_manager.get_value(&lhs)
                    .ok_or(IdentifierNotFoundInMemory(lhs.clone()))?;
                let result = match (current, rhs) {
                    (Value::Int(l), Value::Int(r)) => Value::Int(l ^ r),
                    _ => return Err(InvalidBitwiseOperation)
                };
                self.memory_manager.change_value(&lhs, result);
                Ok(Value::Unit)
            }
            BinaryOperator::AssignBitwiseOr => {
                let lhs = self.expression_identifier(binary_operator_expression.lhs.node)?;
                let rhs = self.expression_value(binary_operator_expression.rhs.node)?;
                let current =  self.memory_manager.get_value(&lhs)
                    .ok_or(IdentifierNotFoundInMemory(lhs.clone()))?;
                let result = match (current, rhs) {
                    (Value::Int(l), Value::Int(r)) => Value::Int(l | r),
                    _ => return Err(InvalidBitwiseOperation)
                };
                self.memory_manager.change_value(&lhs, result);
                Ok(Value::Unit)
            }
        }
    }
    fn constant(&mut self, constant: ast::Constant) -> Result<Value,ErrorInterpreter> {
        match constant{
            Constant::Integer(value) => {
                //TODO use suffix
                match value.base {
                    IntegerBase::Decimal => {
                        let i: i64 = value.number.parse().map_err(|_| InvalidInt)?;
                        Ok(Value::Int(i))
                    }
                    _ => {Err(BaseNotSupported)}
                }
                
            }
            Constant::Float(value) => {
                match value.base {
                    FloatBase::Decimal => {
                        let f: f64 = value.number.parse().map_err(|_| InvalidInt)?;
                        Ok(Value::Float(f))
                    }
                    FloatBase::Hexadecimal => {Err(BaseNotSupported)}
                }
            }
            Constant::Character(value) => {
                Ok(Value::Char(value.parse().unwrap()))
            }
        }
    }
    fn expression_value(&mut self, expression: ast::Expression) -> Result<Value, ErrorInterpreter> {
        debug!("expression_value");
        match expression {
            ast::Expression::Identifier(identifier) => {
                if let Some(value) = self.memory_manager.get_value(&identifier.node.name){
                    Ok(value.clone())
                }else{
                    Err(IdentifierNotFoundInMemory(identifier.node.name.clone()))
                }
            }
            ast::Expression::BinaryOperator(binary_operator) => {
                self.binary_operator_expression(binary_operator.node)
            }
            ast::Expression::Constant(constant) => {
                self.constant(constant.node)
            }
            _=> {
                println!("{:?}", expression);
                warn!("Expression not implemented in expression");
                Err(NotImplemented)
            }
        }
    }
    fn expression_identifier(&mut self, expression: ast::Expression) -> Result<Identifier, ErrorInterpreter> {
        debug!("expression_identifier");
        match expression {
            ast::Expression::Identifier(identifier) => Ok(identifier.node.name),
            _ => Err(NotImplemented)
        }
    }
    fn initializer(&mut self, initializer: ast::Initializer) -> Result<Value, ErrorInterpreter> {
        debug!("initializer");
        match initializer {
            ast::Initializer::Expression(expression) => {self.expression_value(expression.node)}
            ast::Initializer::List(initializer_list_item) => {todo!()}
        }
    }
    fn declarators(&mut self, declarators: Vec<Node<ast::InitDeclarator>>) -> Result<Vec<(Identifier, Option<Value>)>, ErrorInterpreter> {
        debug!("declarators");
        let mut res = vec![];
        for declarator in declarators {
            debug!("In declarators: Declarator: {:?}", declarator);
            let init_declarator = declarator.node;
            let declarator = init_declarator.declarator;
            let identifier = self.declarator(declarator.node)?;
            let initializer  = if let Some(init) = init_declarator.initializer{
                Some(self.initializer(init.node)?)
            }else{
                None
            };
            res.push((identifier, initializer));

        };
        Ok(res)
    }
    fn declaration(&mut self, declaration: ast::Declaration) -> Result<Value, ErrorInterpreter> {
        debug!("Declaration");
        //int i;
        let specifier = Specifier::fromVecDeclaration(&declaration.specifiers)?;
        let declaration: Vec<(Identifier, Option<Value>)> = self.declarators(declaration.declarators)?;
        for (identifier, values) in declaration{
          if let Some(values) = values{
              if !values.same_type_specifier(&specifier){
                  error!("Bad type during declaration of variable for {}, {:?} instead of {:?}", identifier, values, specifier);
                  return Err(IncorrectTypeDeclaration(format!("Bad type during declaration of variable for {}, {:?} instead of {:?}", identifier, values, specifier)));
              }
              self.memory_manager.set_value(&identifier, values);
          }else{
              self.memory_manager.set_value(&identifier, specifier.default_value())
          }
        };
        Ok(Value::Unit)
    }
    fn block_item(&mut self, block_item: ast::BlockItem) -> Result<Value, ErrorInterpreter>{
        debug!("block_item: {:?}", block_item);
        match block_item {
            ast::BlockItem::Declaration(declaration) => self.declaration(declaration.node),
            ast::BlockItem::StaticAssert(static_assert) => Err(ErrorInterpreter::NotImplemented),
            ast::BlockItem::Statement(statement) => self.statement(statement.node)
        }
    }
    fn compound(&mut self, compound:  Vec<Node<ast::BlockItem>>) -> Result<Value, ErrorInterpreter> {
        debug!("compound");
        
        let mut last_value = Value::Unit;
        for block_item in compound{
            last_value = self.block_item(block_item.node)?;
        }
        Ok(last_value)

    }
    fn statement(&mut self, statement: ast::Statement) -> Result<Value, ErrorInterpreter> {
        debug!("statement");
        let value = match statement {
            ast::Statement::Compound(comp) => self.compound(comp),
            ast::Statement::Expression(expression) => self.expression_value(expression.unwrap().node),
            ast::Statement::Return(expression) => self.expression_value(expression.unwrap().node),
            _ => return Err(NotImplemented)
        };
        value
    }
    fn interpret<T: 'static>(&mut self, block_item: ast::BlockItem) -> Result<Value, ErrorInterpreter>{
        
        todo!()
        /*
        match TypeId::of::<T>() {
            t if t == TypeId::of::<ast::ExternalDeclaration>() => {
                match convert_node_type::<T, ast::ExternalDeclaration>(node)? {
                    ast::ExternalDeclaration::Declaration(_) => {
                        Err(ErrorInterpreter::NotImplemented)
                    },
                    ast::ExternalDeclaration::FunctionDefinition(func) => {
                        info!("Entering function");
                        self.interpret(func)
                    },
                    ast::ExternalDeclaration::StaticAssert(_) => {
                        Err(ErrorInterpreter::NotImplemented)
                    }
                }
            }
            t if t == TypeId::of::<ast::FunctionDefinition>() => {
                let function_def = convert_node_type::<T, ast::FunctionDefinition>(node)?;
                // get return specifier
                let specifier = Specifier::fromVecDeclaration(&function_def.specifiers)?;
                // get arguments
                let declarator = &function_def.declarator.node;
                //let x = declarator.derived;
                // transfer memory into the new scope
    
                todo!()
            }
            _ => Err(ErrorInterpreter::NotImplemented),
        }*/
        
    }
}


    

fn main() {
    env_logger::init();
    let mut interpreter = Interpreter::new();
    interpreter.run("test.c");
}

#[cfg(test)]
mod tests {
    use crate::MemoryManager;

    #[test]
    fn creation_add_value() {
        
    }
}


