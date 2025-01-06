use rustc_borrowck::consumers::{
    get_body_with_borrowck_facts, BodyWithBorrowckFacts, ConsumerOptions,
};
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    BodyId, FnSig, Generics,
};
use rustc_middle::{
    mir::{
        BindingForm, Body, BorrowKind, Local, LocalInfo, Operand, Rvalue, StatementKind,
        TerminatorKind, UserTypeProjections, VarBindingForm,
    },
    ty::{BoundRegionKind, BoundVariableKind, Ty, TyCtxt, TyKind},
};
use rustc_span::Span;

use std::collections::BTreeMap;

pub fn borrowck<'a, 'tcx>(
    ctx: &'a TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> BodyWithBorrowckFacts<'tcx> {
    get_body_with_borrowck_facts(*ctx, def_id, ConsumerOptions::RegionInferenceContext)
}

#[derive(Clone, Copy, Debug)]
struct Range {
    lo: u32,
    hi: u32,
}
impl Range {
    fn new(lo: u32, hi: u32) -> Self {
        Self { lo, hi }
    }
}
impl From<Span> for Range {
    fn from(value: Span) -> Self {
        Self::new(value.lo().0, value.hi().0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum LifetimeRelation {
    Eq,
    ValidOutlive,
    InvalidOutlive,
    Assume,
}
/// a = b, then `Relation::Clone(b, a)`.
#[derive(Clone, Copy, Debug)]
enum VarRelation {
    /// immutable reference to from
    ImmRef {
        right: Local,
        left: Local,
        lifetime: LifetimeRelation,
        range: Range,
    },
    /// mutable reference to from
    MutRef {
        right: Local,
        left: Local,
        lifetime: LifetimeRelation,
        range: Range,
    },
    /// copy from to
    Copy {
        right: Local,
        left: Option<Local>,
        range: Range,
    },
    /// move from to
    Move {
        right: Local,
        left: Option<Local>,
        range: Range,
    },
    /// clone from to
    Clone {
        from: Local,
        to: Local,
        range: (Range, Option<Range>),
    },
}
impl VarRelation {
    /*
    fn right(&self) -> Local {
        match self {
            VarRelation::ImmRef(l, _, _) => *l,
            VarRelation::MutRef(l, _, _) => *l,
            VarRelation::Copy(l, _) => *l,
            VarRelation::Move(l, _) => *l,
            VarRelation::Clone(l, _) => *l,
        }
    }
    fn left(&self) -> Option<Local> {
        match self {
            VarRelation::ImmRef(_, t, _) => Some(*t),
            VarRelation::MutRef(_, t, _) => Some(*t),
            VarRelation::Copy(_, t) => *t,
            VarRelation::Move(_, t) => *t,
            VarRelation::Clone(_, t) => Some(*t),
        }
    }
    fn lifetime_rel(&self) -> Option<LifetimeRelation> {
        match self {
            VarRelation::ImmRef(_, _, l) => Some(*l),
            VarRelation::MutRef(_, _, l) => Some(*l),
            _ => None,
        }
    }
    */
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Constraint {
    Eq(Local, Local),
    /// left >= right
    Outlive(Local, Local),
}
struct Constraints(Vec<Constraint>);
impl Constraints {
    fn push(&mut self, new: Constraint) {
        match new {
            Constraint::Eq(l1, l2) => {
                let eqs = vec![l1, l2];
                for c in &self.0 {}
            }
            Constraint::Outlive(sup, sub) => {}
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum VarTypeRelation {
    Eq(Local),
    ImmRef(Local),
    MutRef(Local),
    Deref(Local),
}

#[derive(Debug)]
struct V {
    // (variable, add ref to type, )
    relations: Vec<VarRelation>,
    ty: BTreeMap<Local, Vec<VarTypeRelation>>,
    lifetime_annotation_id: u8,
}
impl V {
    fn new() -> Self {
        Self {
            relations: Vec::new(),
            ty: BTreeMap::new(),
            lifetime_annotation_id: b'a',
        }
    }
    /*
    fn contains(&self, local: Local) -> Option<VarRelation> {
        for v in &self.relations {
            if v.from() == local {
                return Some(*v);
            }
        }
        None
    }
    */
    fn push_ty(&mut self, local: Local, rel: VarTypeRelation) {
        if let Some(rs) = self.ty.get_mut(&local) {
            if !rs.contains(&rel) {
                rs.push(rel);
            }
        } else {
            self.ty.insert(local, vec![rel]);
        }
    }
    fn push(&mut self, rel: VarRelation) {
        match rel {
            VarRelation::ImmRef { right, left, .. } => {
                self.push_ty(left, VarTypeRelation::ImmRef(right));
                //self.push_ty(right, VarTypeRelation::Deref(left));
            }
            VarRelation::MutRef { right, left, .. } => {
                self.push_ty(left, VarTypeRelation::MutRef(right));
                //self.push_ty(right, VarTypeRelation::Deref(left));
            }
            VarRelation::Copy { right, left, .. } => {
                if let Some(left) = left {
                    self.push_ty(left, VarTypeRelation::Eq(right));
                    self.push_ty(right, VarTypeRelation::Eq(left));
                }
            }
            VarRelation::Move { right, left, .. } => {
                if let Some(left) = left {
                    self.push_ty(left, VarTypeRelation::Eq(right));
                    self.push_ty(right, VarTypeRelation::Eq(left));
                }
            }
            VarRelation::Clone { from, to, .. } => {
                self.push_ty(from, VarTypeRelation::ImmRef(to));
                //self.push_ty(to, VarTypeRelation::Deref(from));
            }
        }
        self.relations.push(rel);
    }
    fn list_affected_local_recur(&self, list: &mut BTreeMap<Local, ()>, local: Local) {
        if let Some(rel) = self.ty.get(&local) {
            for rel in rel {
                match rel {
                    VarTypeRelation::Eq(r) => {
                        if list.get(r).is_none() {
                            list.insert(*r, ());
                            self.list_affected_local_recur(list, *r);
                        }
                    }
                    VarTypeRelation::ImmRef(r) => {
                        if list.get(r).is_none() {
                            list.insert(*r, ());
                            self.list_affected_local_recur(list, *r);
                        }
                        /*
                        let v = ty.get_mut(&local).unwrap();
                        let idx = v.iter().enumerate().find(|(_, v)| v == &&rel).unwrap().0;
                        v.remove(idx);
                        */
                    }
                    VarTypeRelation::MutRef(r) => {}
                    VarTypeRelation::Deref(r) => {}
                    _ => {}
                }
            }
        }
    }
    /// 引数`local`の型を参照に書き換えたときに、型を書き換える必要のある変数のリストを取得する
    fn list_affected_local(&self, local: Local) -> Vec<Local> {
        let mut res = BTreeMap::new();
        self.list_affected_local_recur(&mut res, local);
        log::debug!("{local:?} affect: {res:?}");
        res.into_keys().collect()
    }
    fn new_annotation_id(&mut self) -> u8 {
        let annot = self.lifetime_annotation_id;
        self.lifetime_annotation_id += 1;
        annot
    }
}
impl V {
    fn may_be_moved(&self, local: Local) -> bool {
        for rel in &self.relations {
            if let VarRelation::Move { right, .. } = rel {
                if *right == local {
                    return true;
                }
            }
        }
        false
    }
    fn may_be_mutably_borrowed(&self, local: Local) -> bool {
        for rel in &self.relations {
            if let VarRelation::MutRef { right, .. } = rel {
                if *right == local {
                    return true;
                }
            }
        }
        false
    }
    fn elim(&mut self, generics: &Generics<'_>, body: &Body<'_>) -> Substitutes {
        log::info!("start calculation for S by using V");
        let mut s = Substitutes::new();
        let mut candidates = Vec::new();
        for rel in &self.relations {
            match rel {
                VarRelation::Clone { .. } => {
                    candidates.push(*rel);
                }
                _ => {}
            }
        }
        let mut clones = Vec::new();
        log::debug!("candidates: {candidates:?}");
        for rel in &candidates {
            match *rel {
                VarRelation::Clone { from, to, .. } => {
                    if !self.may_be_mutably_borrowed(from) && !self.may_be_mutably_borrowed(to)
                    /*
                    if !self.may_be_moved(from)
                        && !self.may_be_mutably_borrowed(from)
                        && !self.may_be_moved(to)
                        && !self.may_be_mutably_borrowed(to)
                        */
                    {
                        clones.push(*rel);
                    }
                }
                _ => {}
            }
        }
        log::debug!("eliminate: {clones:?}");
        let mut affected = BTreeMap::new();
        for clone in &clones {
            match clone {
                VarRelation::Clone {
                    from,
                    to,
                    range: (r1, r2),
                } => {
                    s.rewrite(r1.lo, r1.hi, "".to_owned());
                    if let Some(r2) = r2 {
                        s.rewrite(r2.lo, r2.hi, "".to_owned());
                    }
                    let mut new_annotation = self.new_annotation_id();
                    let affect = self.list_affected_local(*from);
                    for affect in affect {
                        log::debug!("{affect:?} affected by rewrite of {to:?}");
                        // 型が等しい場合にライフタイムアノテーションの関係を解決
                        if let Some(annotation) = affected.get(&affect).map(|v| *v) {
                            for (_, annot) in &mut affected {
                                log::info!(
                                    "lifetime annotation {} is unified to {}",
                                    *annot as char,
                                    new_annotation as char
                                );
                                if *annot == new_annotation {
                                    *annot = annotation;
                                }
                            }
                            new_annotation = annotation;
                        } else {
                            affected.insert(affect, new_annotation);
                        }
                    }
                }
                _ => {}
            }
        }
        log::debug!("affected: {affected:?}");
        let mut annotations = BTreeMap::new();
        for (local, annot) in &affected {
            let decl = body.local_decls.get(*local).unwrap();
            match decl.local_info() {
                LocalInfo::User(BindingForm::Var(var)) => {
                    if let Some(span) = &var.opt_ty_info {
                        let range = Range::from(*span);
                        s.rewrite(range.lo, range.lo, format!("&'{} ", *annot as char));
                        annotations.insert(*annot, ());
                    }
                }
                _ => {
                    let range = Range::from(decl.source_info.span);
                    if range.lo != range.hi {
                        s.rewrite(range.lo, range.lo, format!("&'{} ", *annot as char));
                        annotations.insert(*annot, ());
                    }
                }
            }
        }
        if 0 < annotations.len() {
            let mut annot_str = String::new();
            for (annot, _) in annotations {
                annot_str.push('\'');
                annot_str.push(annot as char);
                annot_str.push(',');
            }
            let range = Range::from(generics.span);
            if 0 < range.hi - range.lo {
                s.rewrite(range.hi - 1, range.hi - 1, format!(",{annot_str}"));
            } else {
                s.rewrite(range.hi, range.hi, format!("<{annot_str}>"));
            }
        }
        s
    }
}

pub fn rewrite<'a, 'hir, 'tcx>(
    source: String,
    ctx: &'a TyCtxt<'tcx>,
    signature: FnSig<'hir>,
    generics: Generics<'hir>,
    def_id: LocalDefId,
) -> Result<Option<String>, ()> {
    let clone_local_id = ctx.lang_items().clone_fn().unwrap();

    let bck = borrowck(ctx, def_id);
    let body = &bck.body;

    log::debug!("MIR basic blocks:\n{:?}", body.basic_blocks);

    let mut v = V::new();

    let get_opr_rel = |opr, left| match opr {
        &Operand::Copy(r) => Some(VarRelation::Copy {
            right: r.local,
            left,
            range: Range::from(opr.span(&body.local_decls)),
        }),
        &Operand::Move(r) => Some(VarRelation::Move {
            right: r.local,
            left,
            range: Range::from(opr.span(&body.local_decls)),
        }),
        _ => None,
    };
    let local_lifetime_eval = |l1: Local, l2: Local| {
        let l1d = body.local_decls.get(l1).unwrap();
        let l2d = body.local_decls.get(l2).unwrap();
        match (l1d.ty.kind(), l2d.ty.kind()) {
            (TyKind::Ref(r1, _, _), TyKind::Ref(r2, _, _)) => {
                if !r1.is_var() || !r2.is_var() {
                    return None;
                }
                if bck
                    .region_inference_context
                    .eval_equal(r1.as_var(), r2.as_var())
                {
                    Some(LifetimeRelation::Eq)
                } else if bck
                    .region_inference_context
                    .eval_outlives(r1.as_var(), r2.as_var())
                {
                    Some(LifetimeRelation::ValidOutlive)
                } else {
                    Some(LifetimeRelation::InvalidOutlive)
                }
            }
            _ => None,
        }
    };
    for bb in body.basic_blocks.iter() {
        for stmt in bb.statements.iter() {
            match &stmt.kind {
                StatementKind::Assign(a) => {
                    let (left, rval) = &**a;
                    match rval {
                        Rvalue::Use(opr) => {
                            if let Some(rel) = get_opr_rel(&opr, Some(left.local)) {
                                v.push(rel)
                            }
                        }
                        Rvalue::Ref(rregion, kind, place) => {
                            let left_decl = body.local_decls.get(left.local).unwrap();
                            let lrel;
                            if let TyKind::Ref(lregion, _, _mutability) = left_decl.ty.kind() {
                                if rregion.is_var() && lregion.is_var() {
                                    let rrvid = rregion.as_var();
                                    let lrvid = lregion.as_var();
                                    if bck.region_inference_context.eval_equal(rrvid, lrvid) {
                                        lrel = LifetimeRelation::Eq;
                                    } else if bck
                                        .region_inference_context
                                        .eval_outlives(rrvid, lrvid)
                                    {
                                        lrel = LifetimeRelation::ValidOutlive;
                                    } else {
                                        lrel = LifetimeRelation::InvalidOutlive;
                                    }
                                } else {
                                    lrel = LifetimeRelation::Assume;
                                }
                            } else {
                                lrel = LifetimeRelation::Assume;
                            };
                            let rel;
                            let range = Range::from(
                                body.local_decls.get(place.local).unwrap().source_info.span,
                            );
                            match kind {
                                BorrowKind::Mut { .. } => {
                                    rel = VarRelation::MutRef {
                                        right: place.local,
                                        left: left.local,
                                        lifetime: lrel,
                                        range,
                                    };
                                }
                                _ => {
                                    rel = VarRelation::ImmRef {
                                        right: place.local,
                                        left: left.local,
                                        lifetime: lrel,
                                        range,
                                    };
                                }
                            }
                            v.push(rel);
                        }
                        Rvalue::Repeat(opr, _) => {
                            if let Some(rel) = get_opr_rel(&opr, None) {
                                v.push(rel)
                            }
                        }
                        Rvalue::Cast(_, opr, _) => {
                            if let Some(rel) = get_opr_rel(&opr, None) {
                                v.push(rel);
                            }
                        }
                        Rvalue::BinaryOp(_, ops) => {
                            let (binl, binr) = &**ops;
                            if let Some(rel) = get_opr_rel(&binl, None) {
                                v.push(rel);
                            }
                            if let Some(rel) = get_opr_rel(&binr, None) {
                                v.push(rel);
                            }
                        }
                        Rvalue::UnaryOp(_, opr) => {
                            if let Some(rel) = get_opr_rel(&opr, None) {
                                v.push(rel);
                            }
                        }
                        Rvalue::Aggregate(_, oprs) => {
                            for opr in oprs.iter() {
                                if let Some(rel) = get_opr_rel(&opr, None) {
                                    v.push(rel);
                                }
                            }
                        }
                        Rvalue::ShallowInitBox(opr, _) => {
                            if let Some(rel) = get_opr_rel(&opr, None) {
                                v.push(rel);
                            }
                        }
                        Rvalue::CopyForDeref(r) => {}
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
                    if let Some((def_id, _)) = func.const_fn_def() {
                        if def_id == clone_local_id {
                            let arg = &args[0];
                            let range;
                            if fn_span.lo().0 < arg.span.lo().0 {
                                range = (
                                    Range::new(fn_span.lo().0, arg.span.lo().0),
                                    Some(Range::new(arg.span.hi().0, fn_span.hi().0)),
                                );
                            } else {
                                range = (Range::new(arg.span.hi().0, fn_span.hi().0), None);
                            }
                            match arg.node {
                                Operand::Move(a) => {
                                    v.push(VarRelation::Clone {
                                        from: a.local,
                                        to: destination.local,
                                        range,
                                    });
                                }
                                Operand::Copy(a) => {
                                    v.push(VarRelation::Clone {
                                        from: a.local,
                                        to: destination.local,
                                        range,
                                    });
                                }
                                _ => {}
                            }
                        } else {
                            /*
                             * 手元でライフタイム注釈を確認する必要があったら書く
                             *
                            let fn_ty = ctx.type_of(def_id).instantiate_identity();
                            let fn_sig = fn_ty.fn_sig(ctx);
                            if let Some(fn_sig) = fn_sig.no_bound_vars() {
                                let inputs = fn_sig.inputs();
                            }
                            log::debug!("{:?}", fn_ty);
                            */
                            for arg in args.iter() {
                                if let Some(act) = get_opr_rel(&arg.node, None) {
                                    v.push(act);
                                }
                            }
                        }
                    }
                }
                /*
                 * 一旦実装しないでよさそう
                 *
                TerminatorKind::Drop { place, target, unwind, replace } => {}
                TerminatorKind::TailCall { func, args, fn_span } => {}
                TerminatorKind::Assert { cond, expected, msg, target, unwind } => {}
                TerminatorKind::Yield { value, resume, resume_arg, drop }=> {}
                */
                _ => {}
            }
        }
    }
    log::debug!("{v:?}");
    let s = v.elim(&generics, &body);

    /*
    'arg: for arg_local in body.args_iter() {
        let mut v = V::new();
        let mut sa = RewriteString::new();

        let user_type_span = |user_ty: &UserTypeProjections| {
            for (_, span) in &user_ty.contents {
                sa.rewrite(
                    span.lo().0,
                    span.lo().0,
                    format!("&'{} ", lifetime_annotation as char),
                );
                v.push(arg_local, Some(lifetime_annotation));
                lifetime_annotation += 1;
            }
        };

        let arg_decl = body.local_decls.get(arg_local).unwrap();
        if arg_decl
            .ty
            .ref_mutability()
            .map(|v| v.is_mut())
            .unwrap_or(false)
            || arg_decl.mutability.is_mut()
        {
            continue 'arg;
        }
        if arg_decl.mutability.is_mut() {
            continue 'arg;
        }

        if let Some(user_ty) = arg_decl.user_ty {
            if !arg_decl.ty.is_ref() {
                user_type_span(&*user_ty);
            } else {
                v.push(arg_local, None);
            }
        } else {
            continue 'arg;
        }

        /*
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
                sa.rewrite(
                    span.lo().0,
                    span.lo().0,
                    format!("&'{} ", lifetime_annotation as char),
                );
                lifetime_annotation += 1;
            }
        } else {
            continue 'arg;
        }
        */

        let check_opr = |v: &V, opr| match opr {
            &Operand::Move(place) => {
                if let Some(local) = place.as_local() {
                    if v.contains(local).is_some() {
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
                                    continue 'arg;
                                }
                            }
                            Rvalue::Ref(_, kind, place) => match kind {
                                BorrowKind::Mut { .. } => {
                                    // ここで可変性を検査しなくても、変数宣言時の可変性を見れば良い
                                    /*
                                    if let Some(local) = place.as_local() {
                                        if v.contains(local).is_some() {
                                            continue 'arg;
                                        }
                                    }
                                    */
                                }
                                _ => {
                                    if let Some(local) = place.as_local() {
                                        if v.contains(local).is_some() {
                                            let span = stmt.source_info.span;
                                            let left_decl = body
                                                .local_decls
                                                .get(left.as_local().unwrap())
                                                .unwrap();
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
                // TODO: ここ調べるべきターミネータ全部調べる
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
                                    if let Some(local_decl) = body.local_decls.get(local) {
                                        // 代入先の変数の型が参照でなくかつ変数が可変、または
                                        // 参照先の型が可変借用
                                        if (!local_decl.ty.is_ref()
                                            && local_decl.mutability.is_mut())
                                            || local_decl
                                                .ty
                                                .ref_mutability()
                                                .map(|v| v.is_mut())
                                                .unwrap_or(false)
                                        {
                                            continue 'arg;
                                        }
                                        if let Some((_, lifetime)) = v.contains(local) {
                                        } else {
                                            if let Some(user_ty) = &local_decl.user_ty {
                                                user_type_span(&*user_ty);
                                            } else {
                                                v.push(local, None);
                                            }
                                        }
                                    }
                                }
                                // 変数の前に&をつける

                                // .clone() を除去する
                                let arg_span = &args[0].span;
                                if fn_span.lo().0 < arg_span.lo().0 {
                                    // Clone::clone(&arg) の形式
                                    sa.rewrite(fn_span.lo().0, arg_span.lo().0, "".to_owned());
                                    sa.rewrite(arg_span.hi().0, fn_span.hi().0, "".to_owned());
                                } else {
                                    // exp.clone() の形式
                                    sa.rewrite(arg_span.hi().0, fn_span.hi().0, "".to_owned());
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        s.merge(&sa);
    }
    */
    Ok(Some(s.apply(source)))
}

fn source_slice<'a>(source: &'a str, from: i32, until: i32) -> &'a str {
    source.split_at(until as usize).0.split_at(from as usize).1
}

struct Substitutes {
    replaces: Vec<(u32, u32, String)>,
}
impl Substitutes {
    fn new() -> Self {
        Self {
            replaces: Vec::new(),
        }
    }
    fn rewrite(&mut self, from: u32, until: u32, insert: String) {
        self.replaces.push((from, until, insert));
    }
    fn merge(&mut self, other: &Self) {
        self.replaces.extend_from_slice(&other.replaces);
    }
    fn apply(&self, mut target: String) -> String {
        let mut sorted = self.replaces.clone();
        let mut diff = 0i32;
        sorted.sort_by(|(a_from, _, _), (b_from, _, _)| a_from.cmp(b_from));
        for (from, until, insert) in sorted {
            let (head, tail) = target.split_at((until as i32 + diff) as usize);
            //target = tail.to_owned();
            let (head, _) = head.split_at((from as i32 + diff) as usize);
            log::info!(
                "rewrite \"{}\" to \"{}\"",
                source_slice(&target, from as i32 + diff, until as i32 + diff),
                insert
            );
            target = format!("{}{}{}", head, insert, tail);
            diff += (from as i32) - (until as i32) + (insert.len() as i32);
        }
        target
    }
}
