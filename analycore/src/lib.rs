#![feature(rustc_private)]

pub mod enter;
pub mod rewrite;

pub extern crate polonius_engine;
pub extern crate rustc_borrowck;
pub extern crate rustc_driver;
pub extern crate rustc_errors;
pub extern crate rustc_hash;
pub extern crate rustc_hir;
pub extern crate rustc_interface;
pub extern crate rustc_middle;
pub extern crate rustc_session;
pub extern crate rustc_span;

use std::path::PathBuf;

#[derive(Clone, PartialEq, Debug)]
pub enum Error {
    ArgIndexOut,
    FnNotFound,
    Internal,
}

pub fn rewrite_fn(name: PathBuf, source: String, fn_name: &str) -> Result<String, Error> {
    let do_rewrite = |source: String, arg_nth: usize| {
        enter::enter(name.clone(), source.clone(), |ctx| {
            if let Some(item) = enter::get_fn(ctx, fn_name) {
                let (sig, gen, bid) = item.expect_fn();
                if sig.decl.inputs.len() <= arg_nth {
                    return Err(Error::ArgIndexOut);
                }
                return Ok(rewrite::rewrite(
                    source,
                    ctx,
                    *sig,
                    *gen,
                    bid.hir_id.owner.def_id,
                    arg_nth,
                )
                .map_err(|_| Error::Internal)?);
            }
            Err(Error::FnNotFound)
        })
    };
    let do_check = |source: String| {
        log::info!("type & borrow check");
        enter::enter(name.clone(), source, |ctx| {
            if let Some(item) = enter::get_fn(ctx, fn_name) {
                let (sig, gen, bid) = item.expect_fn();
                let bck = rewrite::borrowck(ctx, bid.hir_id.owner.def_id);
                let errors = bck.output_facts.unwrap().errors;
                if 0 == errors.len() {
                    log::info!("type & borrow check ok");
                    return Ok(true);
                } else {
                    log::warn!("type & borrow check failed\n{:?}", errors);
                }
            }
            Ok(false)
        })
    };
    let mut updated = source;
    for i in 0.. {
        log::info!("{}th arg rewrite start", i);
        let upd = do_rewrite(updated.clone(), i);
        match upd {
            Ok(Some(upd)) => {
                log::info!("{i}th rewritten");
                if do_check(upd.clone()) == Ok(true) {
                    updated = upd;
                }
            }
            Err(Error::ArgIndexOut) => {
                log::info!("arg index out of range");
                break;
            }
            Err(e) => {
                return Err(e);
            }
            _ => {}
        }
    }
    Ok(updated)
}
