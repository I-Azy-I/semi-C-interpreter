mod memory;
mod interpreter;
mod errors;


use clap::Parser;
use log::warn;
use interpreter::Interpreter;
use crate::interpreter::DebugInterpreter;









/// An interpreter for a subset of C
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
        DebugInterpreter::new(
            !args.disable_memory,
            !args.disable_source,
            0,
            args.sleep_time.unwrap_or_else(|| 50) as usize,
            false,
            !args.manually,

        )
    }else{
        DebugInterpreter::new(
            false,
            false,
            0,
            0,
             args.print_function_call,
            true,

        )
    };
    let mut interpreter = Interpreter::new();
    interpreter.debug = debug;
    interpreter
}

fn main() {
    env_logger::init();
    let args = Args::parse();
    let mut interpreter = build_interpreter_from_args(&args);
    let _res = interpreter.run(args.path);
    //println!("{:?}", res);
}

#[cfg(test)]
mod tests {
    use std::cmp::PartialEq;
    use crate::interpreter::Interpreter;
    use crate::memory::MemoryValue;

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
        assert_eq!(res, MemoryValue::Int(0));
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


