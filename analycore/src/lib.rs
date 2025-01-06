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

#[derive(Clone, PartialEq, Debug)]
pub enum CompileResult<T> {
    Ok(T),
    Err(T),
}

pub fn rewrite_fn(name: PathBuf, source: String, fn_name: &str) -> Result<Option<String>, Error> {
    let do_rewrite = |source: String| {
        enter::enter(name.clone(), source.clone(), |ctx| {
            if let Some(item) = enter::get_fn(ctx, fn_name) {
                let (sig, gen, bid) = item.expect_fn();
                return Ok(
                    rewrite::rewrite(source, ctx, *sig, *gen, bid.hir_id.owner.def_id)
                        .map_err(|_| Error::Internal)?,
                );
            }
            Err(Error::FnNotFound)
        })
    };
    let do_check = |source: String| {
        log::info!("type & borrow check");
        enter::enter(name.clone(), source, |ctx| {
            if let Some(item) = enter::get_fn(ctx, fn_name) {
                let (_sig, _gen, bid) = item.expect_fn();
                let bck = rewrite::borrowck(ctx, bid.hir_id.owner.def_id);
                return Ok(true);
            }
            Ok(false)
        })
    };
    let mut updated = source;
    let upd = do_rewrite(updated.clone());
    log::info!("rewrite exited");
    match upd {
        Ok(CompileResult::Ok(Ok(Some(upd)))) => {
            updated = upd;
        }
        Err(e) => {
            return Err(e);
        }
        _ => {}
    }
    if do_check(updated.clone()) == Ok(CompileResult::Ok(Ok(true))) {
        Ok(Some(updated))
    } else {
        Ok(None)
    }
}
