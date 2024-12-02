use rustc_hir::{BodyId, FnSig, Generics, TyKind};

pub fn rewrite<'hir>(signature: FnSig<'hir>, generics: Generics<'hir>, body_id: BodyId) {
    for input in signature.decl.inputs {
        match input.kind {
            TyKind::Ref(lifetime, mut_ty) => {
                // this argument cannot rewrite because it is mutable
                if mut_ty.mutbl.is_mut() {
                    continue;
                }
                if lifetime.is_anonymous() {
                    todo!("create new lifetime")
                }
            }
            _ => {
                todo!("rewrite to ref")
            }
        }
    }
}
