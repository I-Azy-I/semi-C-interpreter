use std::collections::HashMap;
use std::hash::Hash;
use std::mem::discriminant;
use lang_c::ast;
use lang_c::span::Node;
use log::{debug, warn};
use crate::errors::{ErrorInterpreter};
use crate::errors::ErrorInterpreter::{ArraySizeLessThanOne, ConversionValueSpecifierNotImplement, HasToBeAIntOrFloatForBooleanEvaluation, IdentifierNotFoundInMemory, ImpossibleToCastIntoThisType, InitializationArrayAndPointerImpossible, InvalidType, MultipleDimensionArrayNotImplemented, SpecifierNotImplemented, VariableAlreadyExist};
const STACK_SIZE: usize = 1000000;
const PRINT_MEMORY: bool = false;
#[derive(Debug, Clone)]
pub enum MemoryValue {
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
    pub(crate) fn get_string(&self) -> String {
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
    pub(crate) fn same_type_specifier(&self, specifier: &SpecifierInterpreter) -> bool {
        match (self, specifier) {
            (MemoryValue::Int(_), SpecifierInterpreter::Int) => true,
            (MemoryValue::Float(_), SpecifierInterpreter::Float) => true,
            (MemoryValue::Pointer(pointer_type_value,_), SpecifierInterpreter::Pointer(pointer_type_specifier)) => pointer_type_value.eq(pointer_type_specifier),
            (MemoryValue::Array(_,_), SpecifierInterpreter::Pointer(_)) => true,
            (MemoryValue::Unit, SpecifierInterpreter::Void) => true,
            _ => false
        }
    }
    pub fn evaluate_boolean_value(&self) -> Result<bool, ErrorInterpreter>{
        match self {
            MemoryValue::Int(value) => Ok(*value != 0),
            MemoryValue::Float(value) => Ok(*value != 0.0),
            _=> Err(HasToBeAIntOrFloatForBooleanEvaluation)
        }
    }
    pub fn get_specifier(&self) -> Result<SpecifierInterpreter, ErrorInterpreter> {
        match self {
            MemoryValue::Int(_) => Ok(SpecifierInterpreter::Int),
            MemoryValue::Float(_) => Ok(SpecifierInterpreter::Float),
            MemoryValue::Pointer(pointer_type_value,_) => Ok(SpecifierInterpreter::Pointer(Box::new(pointer_type_value.clone()))),
            MemoryValue::Array(_pointer_type_value, _) => unreachable!(),
            _ => Err(ConversionValueSpecifierNotImplement)
        }
    }
    pub fn cast(self, specifier: &SpecifierInterpreter) -> Result<MemoryValue, ErrorInterpreter> {
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
pub enum SpecifierInterpreter {
    Int,
    Float,
    Void,
    //Array(Box<SpecifierInterpreter>),
    Pointer(Box<SpecifierInterpreter>)
}


impl SpecifierInterpreter {
    pub fn default_value(&self) -> Result<MemoryValue,ErrorInterpreter> {
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
    pub fn from_node(specifier: &Node<ast::TypeSpecifier>) -> Result<SpecifierInterpreter, ErrorInterpreter>{
        let specifier = &specifier.node;
        match specifier{
            &ast::TypeSpecifier::Int=>Ok(SpecifierInterpreter::Int),
            &ast::TypeSpecifier::Float=>Ok(SpecifierInterpreter::Float),
            &ast::TypeSpecifier::Void=>Ok(SpecifierInterpreter::Void),
            _=>Err(SpecifierNotImplemented)
        }
    }
    pub(crate) fn from_vec_declaration(declaration_specifiers: &Vec<Node<ast::DeclarationSpecifier>>) -> Result<SpecifierInterpreter, ErrorInterpreter>{
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
pub struct DeclaratorInterpreter {
    pub(crate) identifier: Identifier,
    pub(crate) array_sizes: Vec<Option<usize>>,
    pub(crate) n_pointers: usize,
}
impl DeclaratorInterpreter{
    pub(crate) fn to_specifier(&self, specifier: SpecifierInterpreter) -> Result<SpecifierInterpreter, ErrorInterpreter>{
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
pub enum DerivedDeclaratorInterpreter{
    Pointer,
    Array(Option<usize>),
    Function,
}

pub type FunctionArgument = (Option<Identifier>, SpecifierInterpreter);
pub type Body = ast::Statement;
pub type FunctionData = (Identifier,SpecifierInterpreter, Vec<FunctionArgument>, Node<Body>);
pub type Identifier = String ;

#[derive(Debug, Clone)]
pub struct IdentifierData{
    pub(crate) identifier: Identifier,
    pub(crate) array_index: Option<usize>,
    pub(crate) depth: i32
}
impl IdentifierData{
    pub fn from_identifier(identifier: Identifier) -> Self{
        IdentifierData {
            identifier,
            array_index: None,
            depth: 0
        }
    }
}


pub type EnvFunction = HashMap<Identifier, FunctionData>;

pub type MemoryIndex = usize;
pub struct Memory<T: Clone> {
    memory: Vec<T>,
    stack_pointer: usize,
}
impl<T: Clone> Memory<T> {
    pub fn new(default_value: T) -> Memory<T> {
        Memory {
            memory: vec![default_value; STACK_SIZE],
            stack_pointer: 0,
        }
    }
    pub fn get_stack_pointer(&self) -> MemoryIndex {
        self.stack_pointer
    }
    pub fn free(&mut self, from: MemoryIndex){
        self.stack_pointer = from;
    }
    pub fn add(&mut self, value: T) -> MemoryIndex {
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
    pub fn get(&self, memory: MemoryIndex)-> &T{
        &self.memory[memory]
    }
    pub fn change(&mut self, memory: MemoryIndex, value: T){
        self.memory[memory] = value;
    }
    pub fn get_mut(&mut self, memory: MemoryIndex) -> &mut T {
        &mut self.memory[memory]
    }
}

#[derive(Debug, Clone)]
pub struct SymbolTable<T, U> {
    pub start_pointer: MemoryIndex,
    pub kind: SymbolTableKind,
    pub current: HashMap<T, U>,
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
pub enum SymbolTableKind {
    Restricted,
    Scoped
}

pub struct  MemoryManager{
    pub symbol_tables: Vec<SymbolTable<Identifier, MemoryIndex>>,
    pub memory: Memory<MemoryValue>,
}
impl MemoryManager{
    pub(crate) fn new() -> Self{
        let mut symbol_tables = Vec::new();
        symbol_tables.push(SymbolTable::root());
        MemoryManager{
            symbol_tables,
            memory: Memory::new(MemoryValue::Null)
        }
    }
    pub fn current_symbol_table(&self) -> &SymbolTable<Identifier, MemoryIndex> {
        self.symbol_tables.last().unwrap()
    }

    pub fn current_symbol_table_mut(&mut self) -> &mut SymbolTable<Identifier, MemoryIndex> {
        self.symbol_tables.last_mut().unwrap()
    }

    pub fn push_scope(&mut self, kind: SymbolTableKind) {
        let start_pointer = self.memory.get_stack_pointer();
        let new_table = match kind {
            SymbolTableKind::Scoped => SymbolTable::scoped(start_pointer),
            SymbolTableKind::Restricted => SymbolTable::restricted(start_pointer),
        };
        self.symbol_tables.push(new_table);
    }

    pub fn get_index(&self, key: &Identifier) -> Option<MemoryIndex>{
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
    pub(crate) fn get_value(&self, identifier: &Identifier) -> Option<MemoryValue> {
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

    pub fn create_value(&mut self, identifier: &Identifier, value: MemoryValue) -> Result<MemoryIndex, ErrorInterpreter>{
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
    pub fn change_value(&mut self, identifier: &Identifier, value: MemoryValue) -> Result<MemoryValue, ErrorInterpreter> {
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
    pub fn set_to_index(&mut self, memory_index: MemoryIndex, value: MemoryValue) {
        debug!("MEMORY_STATE_BEFORE SET_INDEX {:?}", memory_index);
        debug!("{}", self.build_state());
        self.print_state();
        self.memory.change(memory_index, value);
        debug!("MEMORY_STATE_AFTER SET_INDEX");
        debug!("{}", self.build_state());
    }

    pub(crate) fn get_from_index(&mut self, memory_index: MemoryIndex) -> MemoryValue {
        debug!("MEMORY_STATE_BEFORE SET_INDEX {:?}", memory_index);
        debug!("{}", self.build_state());
        let v = self.memory.get(memory_index);
        debug!("MEMORY_STATE_AFTER SET_INDEX");
        debug!("{}", self.build_state());
        v.clone()
    }
    pub fn add_array(&mut self, values: &Vec<MemoryValue>) -> Result<MemoryIndex, ErrorInterpreter> {
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

    pub fn add_array_default(&mut self, default_value: MemoryValue, size: usize) -> Result<MemoryIndex, ErrorInterpreter>{
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

    pub fn free_scope(&mut self) {
        if self.symbol_tables.len() <= 1 {
            return; // Don't free the root scope
        }

        let current_table = self.symbol_tables.pop().unwrap();
        self.memory.free(current_table.start_pointer);
    }

    pub fn build_state(&self) -> String  {
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

    pub fn print_state(&self) {
        if !PRINT_MEMORY {
            return;
        }
        for table in self.symbol_tables.iter() {
            println!("{:?}", table);
        }
        println!("{}", self.build_state())
    }
}