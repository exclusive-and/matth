
module AlgTy.Monoids

import Theory.AxiomJ
import AlgTy.Properties
import AlgTy.Magma
import AlgTy.Semigroups

%hide Prelude.Algebra.Monoid
%hide Prelude.Algebra.Semigroup
%hide Prelude.Nat.Nat
%hide Prelude.Nat.plus
%hide Prelude.Nat.mult


public export
record IsMonoid (a : Type) (e : a) (m : a -> a -> a) where
    constructor MkMonoidProp
    isSemigroup : IsSemigroup a m
    hasIdentity : HasIdentity {a} e m
