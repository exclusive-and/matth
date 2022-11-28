
module AlgSet.Semigroups

import Theory.AxiomJ
import Theory.Sets
import AlgSet.Magma


public export
IsAssociative : {t : Type} -> (s : Set t) -> SetOp2 {t} s -> Type
IsAssociative {t} s m = (x : t) -> (p : s x)
                     -> (y : t) -> (q : s y)
                     -> (z : t) -> (r : s z)
                     -> (u : s (m x p y q))
                     -> (v : s (m y q z r))
                     -> Id (m x p (m y q z r) v) (m (m x p y q) u z r)

public export
record IsSemigroup (t : Type) (s : Set t) (m : SetOp2 {t} s) where
    constructor MkSemigroupProp

    isAssociative : IsAssociative s m
