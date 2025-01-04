use crate::rewrite::rewrite;
use rustc_hir::{def_id::DefId, Item, ItemKind};
use rustc_interface::interface;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use rustc_session::config;
use rustc_span::{FileName, RealFileName};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{atomic::AtomicBool, Arc};

use crate::Error;

pub fn enter<T>(
    name: PathBuf,
    source: String,
    f: impl for<'tcx> FnOnce(&TyCtxt<'tcx>) -> Result<T, Error> + Send,
) -> Result<T, Error>
where
    T: Send,
{
    let config = interface::Config {
        opts: config::Options {
            debuginfo: config::DebugInfo::Full,
            unstable_opts: config::UnstableOptions {
                polonius: config::Polonius::Legacy,
                ..Default::default()
            },
            ..Default::default()
        },
        input: config::Input::Str {
            name: FileName::Real(RealFileName::LocalPath(name)),
            input: source,
        },
        output_dir: None,
        output_file: None,
        file_loader: None,
        lint_caps: HashMap::default(),
        register_lints: None,
        override_queries: None,
        registry: rustc_driver::diagnostics_registry(),
        crate_cfg: vec![],
        crate_check_cfg: vec![],
        expanded_args: vec![],
        hash_untracked_state: None,
        ice_file: None,
        locale_resources: rustc_driver::DEFAULT_LOCALE_RESOURCES.to_owned(),
        make_codegen_backend: None,
        psess_created: None,
        using_internal_features: Arc::new(AtomicBool::new(true)),
    };
    log::info!("compiler configured; start compilation");
    interface::run_compiler(config, |compiler| {
        log::info!("entered into interface::run_compiler");
        compiler.enter(|queries| {
            log::info!("entered into compiler");

            let Ok(mut gcx) = queries.global_ctxt() else {
                log::error!("error on fetching global context");
                //return Err((Error::UnknownError, None));
                return Err(Error::Internal);
            };

            gcx.enter(|ctx| {
                log::info!("entered into global context");
                f(&ctx)
            })
        })
    })
}

pub fn get_fn<'a, 'tcx>(ctx: &'a TyCtxt<'tcx>, fn_name: &str) -> Option<&'a Item<'tcx>> {
    for item_id in ctx.hir().items() {
        let item = ctx.hir().item(item_id);
        match item.kind {
            ItemKind::Fn(_signature, _generics, _body_id) => {
                if fn_name == item.ident.name.as_str() {
                    return Some(&item);
                }
            }
            _ => {}
        }
    }
    None
}
