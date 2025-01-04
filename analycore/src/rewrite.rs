use rustc_borrowck::consumers::{
    get_body_with_borrowck_facts, BodyWithBorrowckFacts, ConsumerOptions,
};
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    BodyId, FnSig, Generics, TyKind,
};
use rustc_middle::{
    mir::{
        BindingForm, BorrowKind, Local, LocalInfo, Operand, Rvalue, StatementKind, TerminatorKind,
        VarBindingForm,
    },
    ty::{Ty, TyCtxt},
};

pub fn rewrite<'a, 'tcx, 'hir>(
    source: String,
    ctx: &'a TyCtxt<'tcx>,
    signature: FnSig<'hir>,
    generics: Generics<'hir>,
    def_id: LocalDefId,
    arg_nth: usize,
) -> Result<Option<String>, ()> {
    let clone_local_id = ctx.lang_items().clone_fn().unwrap();
    rewrite_mir(source, ctx, def_id, arg_nth, clone_local_id)
}

pub fn borrowck<'a, 'tcx>(
    ctx: &'a TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> BodyWithBorrowckFacts<'tcx> {
    get_body_with_borrowck_facts(*ctx, def_id, ConsumerOptions::PoloniusOutputFacts)
}

pub fn rewrite_mir<'a, 'tcx>(
    source: String,
    ctx: &'a TyCtxt<'tcx>,
    def_id: LocalDefId,
    arg_nth: usize,
    clone_local_id: DefId,
) -> Result<Option<String>, ()> {
    let mut rewrite = RewriteString::new(source.clone());

    let mut v = Vec::new();

    let bck = borrowck(ctx, def_id);
    let body = &bck.body;
    let arg_local = body.args_iter().nth(arg_nth).unwrap();
    let arg_decl = body.local_decls.get(arg_local).unwrap();
    if arg_decl
        .ty
        .ref_mutability()
        .map(|v| v.is_mut())
        .unwrap_or(false)
        || arg_decl.mutability.is_mut()
    {
        return Ok(None);
    }
    if arg_decl.mutability.is_mut() {
        return Ok(None);
    }

    v.push(arg_local);
    let rewrite_ty = !arg_decl.ty.is_ref();

    let arg_name = {
        let span = arg_decl.source_info.span;
        source_slice(&source, span.lo().0, span.hi().0).to_owned()
    };

    let span = match arg_decl.local_info() {
        LocalInfo::User(b) => match b {
            BindingForm::Var(v) => match v {
                VarBindingForm {
                    binding_mode,
                    opt_ty_info,
                    opt_match_place,
                    pat_span,
                } => {
                    if let Some(span) = opt_ty_info {
                        Some(span)
                    } else {
                        None
                    }
                }
                _ => None,
            },
            _ => None,
        },
        _ => None,
    };
    if let Some(span) = span {
        if rewrite_ty {
            rewrite.rewrite(span.lo().0 as i32, span.lo().0 as i32, "&".to_owned());
        }
    } else {
        return Ok(None);
    }

    let check_opr = |v: &[Local], opr| match opr {
        &Operand::Move(place) => {
            if let Some(local) = place.as_local() {
                if v.contains(&local) {
                    return true;
                }
            }
            false
        }
        _ => false,
    };

    for bb in body.basic_blocks.iter() {
        for stmt in bb.statements.iter() {
            match &stmt.kind {
                StatementKind::Assign(a) => {
                    let (left, rval) = &**a;
                    match rval {
                        Rvalue::Use(opr) => {
                            if check_opr(&v, opr) {
                                return Ok(None);
                            }
                        }
                        Rvalue::Ref(_, kind, place) => match kind {
                            BorrowKind::Mut { .. } => {
                                if let Some(local) = place.as_local() {
                                    if v.contains(&local) {
                                        return Ok(None);
                                    }
                                }
                            }
                            _ => {
                                if let Some(local) = place.as_local() {
                                    if v.contains(&local) {
                                        let span = stmt.source_info.span;
                                        let left_decl =
                                            body.local_decls.get(left.as_local().unwrap()).unwrap();
                                        if left_decl.is_user_variable() {
                                            //rewrite.rewrite(span.lo().0, span.hi().0, "");
                                        } else {
                                            /*
                                            let decl = body.local_decls.get(local).unwrap();
                                            rewrite.rewrite(
                                                span.lo().0 as i32,
                                                span.hi().0 as i32,
                                                format!(
                                                    "&{}",
                                                    source_slice(
                                                        &source,
                                                        decl.source_info.span.lo().0,
                                                        decl.source_info.span.hi().0,
                                                    ),
                                                ),
                                            );
                                            */
                                        }
                                        //todo!("rewrite &v");
                                    }
                                }
                            }
                        },
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        if let Some(term) = &bb.terminator {
            match &term.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                    unwind,
                    call_source,
                    fn_span,
                } => {
                    for arg in args.iter() {
                        if check_opr(&v, &arg.node) {
                            return Ok(None);
                        }
                    }
                    if let Some((def_id, _)) = func.const_fn_def() {
                        if def_id == clone_local_id {
                            let call_span = term.source_info.span;
                            if let Some(local) = destination.as_local() {
                                v.push(local);
                                let local_decl = body.local_decls.get(local).unwrap();
                                let span = local_decl.source_info.span;
                                // 返り値の型
                                rewrite.rewrite(
                                    span.lo().0 as i32,
                                    span.lo().0 as i32,
                                    "&".to_owned(),
                                );
                            }
                            // 変数の前に&をつける
                            if rewrite_ty {
                                rewrite.rewrite(
                                    call_span.lo().0 as i32,
                                    call_span.lo().0 as i32,
                                    "&".to_owned(),
                                );
                            }

                            // .clone() を除去する
                            let arg_span = &args[0].span;
                            if fn_span.lo().0 < arg_span.lo().0 {
                                // Clone::clone(&arg) の形式
                                rewrite.rewrite(
                                    fn_span.lo().0 as i32,
                                    arg_span.lo().0 as i32,
                                    "".to_owned(),
                                );
                                rewrite.rewrite(
                                    arg_span.hi().0 as i32,
                                    fn_span.hi().0 as i32,
                                    "".to_owned(),
                                );
                            } else {
                                // exp.clone() の形式
                                rewrite.rewrite(
                                    arg_span.hi().0 as i32,
                                    fn_span.hi().0 as i32,
                                    "".to_owned(),
                                );
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }
    Ok(Some(rewrite.report()))
}

fn source_slice<'a>(source: &'a str, from: u32, until: u32) -> &'a str {
    source.split_at(until as usize).0.split_at(from as usize).1
}

struct RewriteString {
    source: String,
    // (at, diff_length)
    //position_log: Vec<(i32, i32)>,
    replaces: Vec<(i32, i32, String)>, //target: String,
}
impl RewriteString {
    fn new(source: String) -> Self {
        Self {
            source, //.clone(),
            //target: source,
            //position_log: Vec::new(),
            replaces: Vec::new(),
        }
    }
    fn rewrite(&mut self, from: i32, until: i32, insert: String) {
        self.replaces.push((from, until, insert));
        /*
        log::info!(
            "rewrite {} to {}",
            source_slice(&self.source, from, until),
            insert
        );
        let mut new_from = from as i32;
        let mut new_until = until as i32;
        for (diff_from, diff_len) in &self.position_log {
            if *diff_from < from as i32 {
                new_from += *diff_len;
                new_until += *diff_len;
            }
        }
        let diff = (insert.len() as i32) + (from as i32) - (until as i32);
        self.position_log.push((from as i32, diff));
        let (_, tail) = self.target.split_at(new_until as usize);
        let (head, _) = self.target.split_at(new_from as usize);
        self.target = format!("{}{}{}", head, insert, tail);
        */
    }
    fn report(&self) -> String {
        let mut target = self.source.clone();
        //let mut report = String::new();
        let mut sorted = self.replaces.clone();
        let mut diff = 0;
        sorted.sort_by(|(a_from, _, _), (b_from, _, _)| a_from.cmp(b_from));
        for (from, until, insert) in sorted {
            let (head, tail) = target.split_at((until + diff) as usize);
            //target = tail.to_owned();
            let (head, _) = head.split_at((from + diff) as usize);
            target = format!("{}{}{}", head, insert, tail);
            diff += from - until + insert.len() as i32;
        }
        target
    }
}
