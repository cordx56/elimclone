use crate::rewrite::rewrite;
use rustc_hir::{Item, ItemKind};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;

pub fn compile(source: String, compiler: &Compiler) {}

pub fn enter_compilation(compiler: &Compiler) {
    compiler.enter(|queries| {
        log::info!("entered into compiler");

        let Ok(mut gcx) = queries.global_ctxt() else {
            log::error!("error on fetching global context");
            //return Err((Error::UnknownError, None));
            return;
        };

        gcx.enter(recv_tyctxt);
    });
}

pub fn recv_tyctxt<'tcx>(ctx: TyCtxt<'tcx>) {
    log::info!("entered into global context");
    for item_id in ctx.hir().items() {
        let item = ctx.hir().item(item_id);
        check_item(item);
    }
}

pub fn check_item<'hir>(item: &'hir Item) {
    match item.kind {
        ItemKind::Fn(signature, generics, body_id) => {
            rewrite(signature.clone(), generics.clone(), body_id);
        }
        _ => {}
    }
}
