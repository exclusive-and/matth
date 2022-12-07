
module Theory.Homomorphisms

import Theory.AxiomJ


||| Proof that a homomorphism preserves some canonical operation.
public export
HomPreserves : {domainTy, codomainTy : Type}
            -> (domainOp   : domainTy -> domainTy -> domainTy)
            -> (codomainOp : codomainTy -> codomainTy -> codomainTy)
            -> (hom : domainTy -> codomainTy)
            -> Type
HomPreserves {domainTy} {codomainTy} domainOp codomainOp hom =
    (x, y : domainTy) -> Id (hom (domainOp x y)) (codomainOp (hom x) (hom y))
