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

use rustc_borrowck::consumers;
use rustc_interface::interface;
use rustc_session::config;
use rustc_span::{FileName, RealFileName};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{atomic::AtomicBool, Arc};

pub fn enter(name: PathBuf, source: &str) {
    let config = interface::Config {
        opts: config::Options {
            debuginfo: config::DebugInfo::Full,
            error_format: config::ErrorOutputType::Json {
                pretty: true,
                json_rendered: rustc_errors::emitter::HumanReadableErrorType::Default,
                color_config: rustc_errors::ColorConfig::Auto,
            },
            unstable_opts: config::UnstableOptions {
                polonius: config::Polonius::Legacy,
                ..Default::default()
            },
            ..Default::default()
        },
        input: config::Input::Str {
            name: FileName::Real(RealFileName::LocalPath(name)),
            input: source.to_owned(),
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
                return;
            };

            gcx.enter(|ctx| {
                log::info!("entered into global context");
                for item_id in ctx.hir().items() {}
            });
        });
    });
}
