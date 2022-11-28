
module AlgSet.Monoids

import Theory.AxiomJ
import Theory.Sets
import AlgSet.Magma
import AlgSet.Semigroups


public export
HasIdentity : {t : Type}
           -> (s : Set t)
           -> (e : t)
           -> s e
           -> SetOp2 {t} s
           -> Type
HasIdentity {t} s e p m =
    (x : t) -> (q : s x) -> Id (m e p x q) x

public export
record IsMonoid (t : Type) (s : Set t) (e : t) (m : SetOp2 {t} s) where
    constructor MkMonoidProp

    isSemigroup : IsSemigroup t s m

    eInSet : s e
    hasIdentity : HasIdentity s e eInSet m

