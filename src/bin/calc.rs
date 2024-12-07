use lang_c::driver::{parse, Config};

fn main() {
    let config = Config::default();
    let parse = parse(&config, "c_programs/test.c").expect("Error in file c").unit;
    println!("{:#?}", parse);
    
}
