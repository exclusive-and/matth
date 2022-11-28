
module Algebra.Rings

import Theory.AxiomJ
import AlgTy.Properties
import AlgTy.Magma
import AlgTy.Semigroups
import AlgTy.Monoids
import AlgTy.Groups

%hide Prelude.Algebra.Monoid
%hide Prelude.Algebra.Semigroup
%hide Prelude.Nat.Nat
%hide Prelude.Nat.plus
%hide Prelude.Nat.mult


record IsRing (a : Type) (zero : a) (plus : a -> a -> a) (neg : a -> a) (mult : a -> a -> a) where
    constructor MkRingProp
    plusIsGroup : IsGroup a zero plus neg
    plusCommutes : IsCommutative {a} plus

    multIsSemigroup : IsSemigroup a mult
    multDistributes : IsDistributive {a} mult plus

