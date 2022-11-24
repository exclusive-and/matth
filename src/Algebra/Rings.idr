
module Algebra.Rings

import Theory.AxiomJ
import Algebra.Properties
import Algebra.Magma
import Algebra.Semigroups
import Algebra.Monoids
import Algebra.Groups

%hide Prelude.Algebra.Monoid
%hide Prelude.Algebra.Semigroup
%hide Prelude.Nat.Nat
%hide Prelude.Nat.plus
%hide Prelude.Nat.mult


record Ring (a : Type) (zero : a) (plus : a -> a -> a) (neg : a -> a) (mult : a -> a -> a) where
    constructor MkRing
    plusGroup : Group a zero plus neg
    plusCommutes : isCommutative {a} plus

    multMonoid : Semigroup a mult


