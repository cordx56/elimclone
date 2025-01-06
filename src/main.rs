#![feature(rustc_private)]

use analycore::rewrite_fn;
use std::env::args;
use std::fs::read_to_string;

fn main() {
    simple_logger::init_with_env().unwrap();

    let file = args().nth(1).unwrap();
    let source = read_to_string(&file).unwrap();
    let fn_name = args().nth(2).unwrap();
    let res = rewrite_fn(file.into(), source, &fn_name);
    if let Ok(res) = res {
        if let Some(res) = res {
            log::info!("rewrite success");
            println!("{}", res);
        } else {
            log::info!("unable to rewrite");
        }
    } else {
        log::error!("{:?}", res);
    }
}
