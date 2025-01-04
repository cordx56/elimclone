#![feature(rustc_private)]

use analycore::rewrite_fn;
use std::env::args;
use std::fs::read_to_string;
use std::io::{self, Write};

fn main() {
    simple_logger::init().unwrap();

    let file = args().nth(1).unwrap();
    let source = read_to_string(&file).unwrap();
    print!("input function name to be rewritten: ");
    io::stdout().flush().unwrap();
    let mut fn_name = String::new();
    io::stdin().read_line(&mut fn_name).unwrap();
    let res = rewrite_fn(file.into(), source, fn_name.trim());
    if let Ok(res) = res {
        println!("{}", res);
    } else {
        log::error!("{:?}", res);
    }
}
