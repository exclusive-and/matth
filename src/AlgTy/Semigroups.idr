
module AlgTy.Semigroups

import Theory.AxiomJ
import AlgTy.Properties
import AlgTy.Magma

%hide Prelude.Algebra.Monoid
%hide Prelude.Algebra.Semigroup
%hide Prelude.Nat.Nat
%hide Prelude.Nat.plus
%hide Prelude.Nat.mult


public export
record IsSemigroup (a : Type) (m : a -> a -> a) where
    constructor MkSemigroupProp
    isMagma : IsMagma a m
    isAssociative : IsAssociative {a} m
