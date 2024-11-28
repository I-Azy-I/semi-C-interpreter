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
use lang_c::ast::{ArrayDeclarator, ArraySize, BinaryOperator, BinaryOperatorExpression, Constant, DerivedDeclarator, FloatBase, IntegerBase, UnaryOperator, UnaryOperatorExpression};
use crate::ErrorInterpreter::*;

const STACK_SIZE: usize = 20;
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
}
type Int = i64;
type Float = f64;
#[derive(Debug, Clone)]
enum MemoryValue {
    Int(i64),
    Float(f64),
    Char(char),
    //Array(SpecifierInterpreter,Vec<MemoryValue>),
    Pointer(SpecifierInterpreter,usize),
    Null,
    Unit
}

impl MemoryValue {
    fn same_type_specifier(&self, specifier: &SpecifierInterpreter) -> bool {
        match (self, specifier) {
            (MemoryValue::Int(_), SpecifierInterpreter::Int) => true,
            (MemoryValue::Float(_), SpecifierInterpreter::Float) => true,
            // Pointer and Array don't have corresponding specifiers in the given enum
            _ => false
        }
    }
    
    
}
struct Value{
    value: MemoryValue,
    index: Option<usize>,
}

impl Value {
    fn same_type_specifier(&self, specifier: &SpecifierInterpreter) -> bool {
        match (&self.value, specifier) {
            (MemoryValue::Int(_), SpecifierInterpreter::Int) => true,
            (MemoryValue::Float(_), SpecifierInterpreter::Float) => true,
            //(MemoryValue::Array(spec_value, _), SpecifierInterpreter::Array(spec_spec)) => *spec_value == **spec_spec,
            (MemoryValue::Pointer(pointer_type_value, _), SpecifierInterpreter::Pointer(pointer_type_spec)) => *pointer_type_value == **pointer_type_spec,
            _ => false
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
        match self{
            &SpecifierInterpreter::Int => Ok(MemoryValue::Int(0)),
            &SpecifierInterpreter::Float => Ok(MemoryValue::Float(0.0)),
            &SpecifierInterpreter::Void => Ok(MemoryValue::Unit),
            _ => Err(InvalidDefaultSpecifierValueConversion),
        }
    }
    fn fromNode(specifier: &Node<ast::TypeSpecifier>) -> Result<SpecifierInterpreter, ErrorInterpreter>{
        let specifier = &specifier.node;
        match specifier{
            &ast::TypeSpecifier::Int=>Ok(SpecifierInterpreter::Int),
            &ast::TypeSpecifier::Float=>Ok(SpecifierInterpreter::Float),
            &ast::TypeSpecifier::Void=>Ok(SpecifierInterpreter::Void),
            _=>Err(SpecifierNotImplemented)
        }
    }
    fn fromVecDeclaration(declaration_specifiers: &Vec<Node<ast::DeclarationSpecifier>>) -> Result<SpecifierInterpreter, ErrorInterpreter>{
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
                        Ok(SpecifierInterpreter::fromNode(specifier))?
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
    array_sizes: Vec<usize>,
    n_pointers: usize,
}
enum DerivedDeclaratorInterpreter{
    Pointer,
    Array(usize)
}

type FunctionArgument = (Option<Identifier>, SpecifierInterpreter);
type Body = ast::Statement;
type FunctionData = (Identifier, Vec<FunctionArgument>, Node<Body>);
type Identifier = String ;

#[derive(Debug, Clone)]
struct IdentifierData{
    identifier: Identifier,
    array_index: Option<usize>,
}
impl IdentifierData{
    fn from_identifier(identifier: Identifier) -> Self{
        IdentifierData {
            identifier,
            array_index: None,
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

    fn create_value(&mut self, identifier: &Identifier, value: MemoryValue) -> MemoryIndex{
        debug!("MEMORY_STATE_BEFORE CREATE {:?} {:?}", identifier, value);
        debug!("{}", self.build_state());
        let memory_id = self.memory.add(value);
        self.current_symbol_table_mut().save_key(identifier.clone(), memory_id);
        debug!("MEMORY_STATE_AFTER CREATE");
        debug!("{}", self.build_state());
        debug!("SYMBOL TABLES");
        debug!("{:?}", self.symbol_tables);
        memory_id
    }
    fn change_value(&mut self, identifier: &Identifier, value: MemoryValue) -> Option<()> {
        debug!("MEMORY_STATE_BEFORE CHANGE {:?} {:?}", identifier, value);
        debug!("{}", self.build_state());
        if let Some(index) = self.get_index(&identifier) {
            match self.memory.get_mut(index) {
                /*
                MemoryValue::Array(elements_type, array) => {
                    if let Some(array_index) = identifier.array_index {
                        array[array_index] = value;
                        debug!("MEMORY_STATE_AFTER CHANGE");
                        debug!("{}", self.build_state());
                        Some(())
                    } else {
                        debug!("MEMORY_STATE_AFTER CHANGE");
                        debug!("{}", self.build_state());
                        None
                    }
                }*/
                mem_value => {
                    *mem_value = value;
                    debug!("MEMORY_STATE_AFTER CHANGE");
                    debug!("{}", self.build_state());
                    Some(())
                }
            }
        } else {
            debug!("MEMORY_STATE_AFTER CHANGE");
            debug!("{}", self.build_state());
            None
        }
        
    }
    fn set_to_index(&mut self, memory_index: MemoryIndex, value: MemoryValue) { 
        debug!("MEMORY_STATE_BEFORE SET_INDEX {:?}", memory_index);
        debug!("{}", self.build_state());
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
    
    fn add_array(&mut self, default_value: MemoryValue, size: usize) -> MemoryIndex{
        debug!("MEMORY_STATE_BEFORE ADD ARRAY {:?} {}", default_value, size);
        debug!("{}", self.build_state());
        let index = self.memory.add(default_value.clone());
        for i in 1..size{
            self.set_to_index(i + index, default_value.clone());
        };
        self.memory.stack_pointer += size-1;
        index
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
                MemoryValue::Int(value) => { format!("{}", value) },
                MemoryValue::Float(value) => {format!("{}", value)}
                MemoryValue::Char(value) => {format!("{}", value)}
                //MemoryValue::Array(type_array, array) => {format!("type: {:?}, content: {:?}", type_array, array)}
                MemoryValue::Pointer(type_pointer, pointer) => {format!("type: {:?}, content: {:?}", type_pointer, pointer)}
                MemoryValue::Null => { "null".to_string()},
                MemoryValue::Unit => { "unit".to_string()},
            };
            res.push_str(el.clone().as_str());
        }
        res.push_str("|");
        res
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

fn get_function_arguments(function_def: &ast::FunctionDefinition) -> Result<Vec<FunctionArgument>, ErrorInterpreter>{
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
                let specifier = SpecifierInterpreter::fromVecDeclaration(&parameter.specifiers)?;
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
fn get_function_body(function_def: &ast::FunctionDefinition) -> Result<Node<Body>,ErrorInterpreter>{
    Ok(function_def.statement.clone())
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
    memory_manager: MemoryManager,
    return_called: bool,
}
impl Interpreter {
    fn new() -> Self {
        Interpreter { 
            functions: EnvFunction::new(),
            memory_manager: MemoryManager::new(),
            return_called: false,
        }
    }
    fn get_value(&self, identifier: &Identifier) -> Result<MemoryValue, ErrorInterpreter> {
        if let Some(value) = self.memory_manager.get_value(&identifier){
            Ok(value)
        }else{
            error!("Impossible to get variable {}", identifier.clone());
            Err(IdentifierNotFoundInMemory(identifier.clone()))
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
    fn get_value_from_pointer(&mut self, identifier: &Identifier, offset: usize) -> Result<MemoryValue, ErrorInterpreter> {
        let inside_value_pointer = self.get_value(&identifier)?;
        let pointer_address = match inside_value_pointer{
            MemoryValue::Pointer(_, address) => address,
            _ => return Err(NotAPointer)
        };
        Ok(self.memory_manager.get_from_index(pointer_address+offset))
    }

    fn set_value_inside_pointer(&mut self, identifier: &Identifier, offset: usize, value: MemoryValue) -> Result<(), ErrorInterpreter> {
        let inside_value_pointer = self.get_value(identifier)?;
        let pointer_address = match inside_value_pointer{
            MemoryValue::Pointer(_, address) => address,
            _ => return Err(NotAPointer)
        };
        self.memory_manager.set_to_index(pointer_address+offset, value);
        Ok(())
    }
    fn execute_functions(&mut self, function_identifier: Identifier, variables: Vec<Identifier>) -> Result<MemoryValue, ErrorInterpreter> {
        // fetch function data
        let (_, function_arguments, body) = self.functions.get(&function_identifier)
            .ok_or_else(|| ErrorInterpreter::FunctionNotFounded(function_identifier.clone()))?;
        // if function is empty or Void just skip variable initialization
        if  !(function_arguments.len() == 0) && !(function_arguments[0].1 == SpecifierInterpreter::Void){
            // check number of arguments
            if variables.len() !=  function_arguments.len() {
                return Err(IncorrectTypeOfArguments(format!("Incorrect number of variables, expected: {}, got: {}", function_arguments.len(), variables.len())));
            }
            // check if variables are valid
            for ((_, argument_specifier), given_variable_identifier) in function_arguments.iter().zip(&variables) {
                // check if can get variable from memory
                let given_variable_identifier_data = IdentifierData::from_identifier(given_variable_identifier.clone());
                let variable_data = self.get_value(&given_variable_identifier_data.identifier)?;
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
                let given_variable_identifier_data = IdentifierData::from_identifier(given_variable_identifier.clone());
                let variable_data= self.get_value(&given_variable_identifier_data.identifier)?;
                self.memory_manager.create_value(argument_identifier, variable_data.clone());
            }
        }else { 
            self.memory_manager.push_scope(SymbolTableKind::Restricted);
        }
        let function_value = self.statement(&body.clone());
        self.return_called = false;
        function_value
        

    }
    fn run<P: AsRef<Path>> (&mut self, file_name: P) -> MemoryValue {
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
        let result = self.statement(&main_body.clone());
        match result {
            Ok(value) => {
                info!("Program completed successfully");
                value
            }
            Err(err) => {
                eprintln!("An error occurred during execution");
                eprintln!("{:?}", err);
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
        let declarator_kind = &declarator_kind_node.node;
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
    
    fn array_declarator(&mut self, array_declarator: &Node<ast::ArrayDeclarator>) -> Result<usize, ErrorInterpreter> {
        debug!("array_declarator");
        let array_declarator = &array_declarator.node;
        if !array_declarator.qualifiers.is_empty() {
            warn!("Array qualifier not implemented in array declarator");
        };
        match &array_declarator.size {
            ArraySize::Unknown => {
                error!("You have to define the size of an array");
                Err(NotImplemented)
            }
            ArraySize::VariableUnknown => {
                error!("You have to define the size of an array");
                Err(NotImplemented)
            }
            ArraySize::VariableExpression(expression) => {
                match self.expression_value(&expression)? {
                    MemoryValue::Int(value) => { Ok(value as usize) }
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
        let derived_declarator = &derived_declarator_node.node;
        match derived_declarator {
            DerivedDeclarator::Pointer(pointer) => {
                Ok(DerivedDeclaratorInterpreter::Pointer)
            }
            DerivedDeclarator::Array(array) => {
                let size = self.array_declarator(array)?;
                Ok(DerivedDeclaratorInterpreter::Array(size))
            }
            DerivedDeclarator::Function(_) => {
                error!("Function not implemented in derived_declarator");
                Err(NotImplemented)
            }
            DerivedDeclarator::KRFunction(_) => {
                error!("KrFunction not implemented in derived_declarator");
                Err(NotImplemented)
            }
            DerivedDeclarator::Block(_) => {
                error!("Block not implemented in derived_declarator");
                Err(NotImplemented)
            }
        }
        
        
        
    }
    fn declarator(&mut self, declarator_node: &Node<ast::Declarator>) -> Result<DeclaratorInterpreter, ErrorInterpreter> {
        debug!("Declarator");
        let declarator = &declarator_node.node;
        let derived_list = &declarator.derived;
        let mut declarator_interpreter = DeclaratorInterpreter{
            identifier: "".to_string(),
            array_sizes: vec![],
            n_pointers: 0,
        };
        if ! declarator.derived.is_empty(){
            warn!("Declarator derived not implemented (for array, pointers, ...)");
            for derived_declarator in derived_list{
                match self.derived_declarator(&derived_declarator)?{
                    DerivedDeclaratorInterpreter::Pointer => declarator_interpreter.n_pointers+=1,
                    DerivedDeclaratorInterpreter::Array(size) => declarator_interpreter.array_sizes.push(size),
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
        let binary_operator_expression = &binary_operator_expression_node.node;
        match binary_operator_expression.operator.node {
            BinaryOperator::Index => {
                let mut lhs = self.expression_identifier(&binary_operator_expression.lhs)?;
                let rhs =  match self.expression_value(&binary_operator_expression.rhs)?{
                    MemoryValue::Int(value) => lhs.array_index = Some(value as usize),
                    _ => return Err(InvalidValueForArraySize)
                };
                Ok(lhs)
            }
            _ => Err(NoIdentifierCanBeExtract)
        } 
    }
    fn get_operand_value(&mut self, lhs: &IdentifierData) -> Result<MemoryValue, ErrorInterpreter> {
        match lhs.array_index {
            Some(index) => self.get_value_from_pointer(&lhs.identifier, index),
            None => self.get_value(&lhs.identifier),
        }
    }
    fn store_operand_result(&mut self, lhs: &IdentifierData, result: MemoryValue) -> Result<(), ErrorInterpreter>  {
        match lhs.array_index {
            Some(index) => self.set_value_inside_pointer(&lhs.identifier, index, result),
            None => {
                self.memory_manager.change_value(&lhs.identifier, result);
                Ok(())
            }
        }
    }
    fn binary_operator_expression_value(&mut self, binary_operator_expression_node: &Node<BinaryOperatorExpression>) -> Result<MemoryValue, ErrorInterpreter> {


        debug!("binary_operator_expression_value");
        let binary_operator_expression = &binary_operator_expression_node.node;
        match binary_operator_expression.operator.node{
            BinaryOperator::Index => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
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
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) if r >= 0 => Ok(MemoryValue::Int(l << r as u32)),
                    _ => Err(InvalidBitShift)
                }
            }
            BinaryOperator::ShiftRight => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) if r >= 0 => Ok(MemoryValue::Int(l >> r as u32)),
                    _ => Err(InvalidBitShift)
                }
            }
            BinaryOperator::Less => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
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
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int(l & r)),
                    _ => Err(InvalidBitwiseOperation)
                }
            }
            BinaryOperator::BitwiseXor => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int(l ^ r)),
                    _ => Err(InvalidBitwiseOperation)
                }
            }
            BinaryOperator::BitwiseOr => {
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int(l | r)),
                    _ => Err(InvalidBitwiseOperation)
                }
            }
            BinaryOperator::LogicalAnd => {
                // TODO evaluate at first lhs
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int(((l != 0) && (r != 0)) as i64)),
                    _ => Err(InvalidLogicalOperation)
                }
            }
            BinaryOperator::LogicalOr => {
                // TODO evaluate at first lhs
                let lhs = self.expression_value(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                match (lhs, rhs) {
                    (MemoryValue::Int(l), MemoryValue::Int(r)) => Ok(MemoryValue::Int(((l != 0) || (r != 0)) as i64)),
                    _ => Err(InvalidLogicalOperation)
                }
            }
            BinaryOperator::Assign => {
                let lhs = self.expression_identifier(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                if let Some(array_index) = lhs.array_index{
                    self.set_value_inside_pointer(&lhs.identifier, array_index, rhs)?;
                }else{
                    self.memory_manager.change_value(&lhs.identifier, rhs);
                }
                Ok(MemoryValue::Unit)
            }
            BinaryOperator::AssignMultiply => {
                let lhs = self.expression_identifier(&binary_operator_expression.lhs)?;
                let rhs = self.expression_value(&binary_operator_expression.rhs)?;
                let current = self.get_operand_value(&lhs)?;
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
        let constant = &constant_node.node;
        match constant{
            Constant::Integer(value) => {
                //TODO use suffix
                match value.base {
                    IntegerBase::Decimal => {
                        let i: i64 = value.number.parse().map_err(|_| InvalidInt)?;
                        Ok(MemoryValue::Int(i))
                    }
                    _ => {Err(BaseNotSupported)}
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
        let unary_operator = &unary_operator_node.node;
        let value = self.expression_value(&unary_operator.operand)?;
        match unary_operator.operator.node{
            UnaryOperator::Plus => {
                match value{
                    MemoryValue::Int(_) | MemoryValue::Float(_) => { Ok(value) }
                    _ => {Err(InvalidPlusOperator)}
                }
            }
            UnaryOperator::Minus => {
                match value{
                    MemoryValue::Int(i)  => Ok(MemoryValue::Int(-i)),
                    MemoryValue::Float(f) => Ok(MemoryValue::Float(-f)),
                    _ => {Err(InvalidMinusOperator)}
                }
            }
            UnaryOperator::Negate => {
                match value{
                    MemoryValue::Int(i)  => Ok(MemoryValue::Int( if i==0 {1} else {0})),
                    MemoryValue::Float(f) => Ok(MemoryValue::Int( if f==0.0 {1} else {0})),
                    _ => {Err(InvalidNegateOperator)}
                }
            }
            _ => {Err(NotImplemented)}
        }
        
        
    }
    fn expression_value(&mut self, expression_node: &Node<ast::Expression>) -> Result<MemoryValue, ErrorInterpreter> {
        debug!("expression_value");
        let expression = &expression_node.node;
        match expression {
            ast::Expression::Identifier(identifier) => {
                if let Some(value) = self.memory_manager.get_value(&IdentifierData::from_identifier(identifier.node.name.clone()).identifier){
                    Ok(value.clone())
                }else{
                    Err(IdentifierNotFoundInMemory(identifier.node.name.clone()))
                }
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
            _=> {
                println!("{:?}", expression);
                warn!("Expression not implemented in expression");
                Err(NotImplemented)
            }
        }
    }
    fn expression_identifier(&mut self, expression_node: &Node<ast::Expression>) -> Result<IdentifierData, ErrorInterpreter> {
        debug!("expression_identifier");
        let expression = &expression_node.node;
        match expression {
            ast::Expression::Identifier(identifier) => Ok(IdentifierData::from_identifier(identifier.node.name.clone())),
            ast::Expression::BinaryOperator(binary_operator) => {
                self.binary_operator_expression_identifier(binary_operator)
            },
            _ => {
                println!("{:?}", expression);
                Err(NotImplemented)
            }
        }
    }
    fn initializer(&mut self, initializer_node: &Node<ast::Initializer>) -> Result<MemoryValue, ErrorInterpreter> {
        debug!("initializer");
        let initializer = &initializer_node.node;
        match initializer {
            ast::Initializer::Expression(expression) => {self.expression_value(&expression)}
            ast::Initializer::List(initializer_list_item) => {todo!()}
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
        let declaration = &declaration_node.node;
        //int i;
        let specifier = SpecifierInterpreter::fromVecDeclaration(&declaration.specifiers)?;
        let declaration: Vec<(DeclaratorInterpreter, Option<MemoryValue>)> = self.declarators(&declaration.declarators)?;
        for (declarator_interpreter, values) in declaration{
            if !declarator_interpreter.array_sizes.is_empty()  &&  declarator_interpreter.n_pointers > 0 {
                return Err(InitializationArrayAndPointerImpossible);
            } else if declarator_interpreter.array_sizes.len() > 1{
                return Err(MultipleDimensionArrayNotImplemented);
            }
            let local_specifier = if declarator_interpreter.array_sizes.len() == 1{
                SpecifierInterpreter::Pointer(Box::new(specifier.clone()))}
            else if declarator_interpreter.n_pointers == 1 {
                SpecifierInterpreter::Pointer(Box::new(specifier.clone()))
            }else if declarator_interpreter.n_pointers > 1 {
                /*let mut result = specifier.clone();
                for _ in 0..declarator_interpreter.n_pointers {
                    result = SpecifierInterpreter::Pointer(Box::new(result));
                }
                result*/
                return Err(MultiplePointerNotImplemented)
            } else{
                specifier.clone()
            };
            
            if let Some(values) = values{
                if !values.same_type_specifier(&local_specifier){
                  error!("Bad type during declaration of variable for {}, {:?} instead of {:?}", declarator_interpreter.identifier.clone(), values, local_specifier);
                  return Err(IncorrectTypeDeclaration(format!("Bad type during declaration of variable for {}, {:?} instead of {:?}",  declarator_interpreter.identifier.clone(), values, local_specifier)));
                }
                
                self.memory_manager.create_value(&declarator_interpreter.identifier, values);
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
                            let index = self.memory_manager.add_array(default_value, declarator_interpreter.array_sizes[0]);
                            Ok(MemoryValue::Pointer(local_specifier,index))
                        }else if declarator_interpreter.n_pointers == 1{
                            Err(NotImplemented)
                        }else{
                            Err(NotImplemented)
                        }
                    }
                }?;
                self.memory_manager.create_value(&declarator_interpreter.identifier, default_value);
            }
        };
        Ok(MemoryValue::Unit)
    }
    fn block_item(&mut self, block_item_node: &Node<ast::BlockItem>) -> Result<MemoryValue, ErrorInterpreter>{
        debug!("block_item");
        let block_item = &block_item_node.node;
        match block_item {
            ast::BlockItem::Declaration(declaration) => self.declaration(declaration),
            ast::BlockItem::StaticAssert(static_assert) => Err(ErrorInterpreter::NotImplemented),
            ast::BlockItem::Statement(statement) => self.statement(statement)
        }
    }
    fn compound(&mut self, compound: &Vec<Node<ast::BlockItem>>) -> Result<MemoryValue, ErrorInterpreter> {
        debug!("compound");
        for block_item in compound{
            let value = self.block_item(&block_item)?;
            if self.return_called{
                return Ok(value);
            }
        }
        Ok(MemoryValue::Unit)

    }
    fn statement(&mut self, statement: &Node<ast::Statement>) -> Result<MemoryValue, ErrorInterpreter> {
        let statement = &statement.node;
        debug!("statement");
        let value = match statement {
            ast::Statement::Compound(comp) => self.compound(comp),
            ast::Statement::Expression(expression) => self.expression_value(expression.as_ref().unwrap()),
            ast::Statement::Return(expression) => {
                self.return_called = true;
                self.expression_value(expression.as_ref().unwrap())
            },
            _ => return Err(NotImplemented)
        };
        value
    }
}


    

fn main() {
    env_logger::init();
    let mut interpreter = Interpreter::new();
    let res = interpreter.run("./c_programs/test.c");
    println!("{:?}", res);
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
    fn basic_adition(){
        let mut interpreter = Interpreter::new();
        let res = interpreter.run("./c_programs/tests/basic_addition.c");
        assert_eq!(res, MemoryValue::Int(4));
    }
}


