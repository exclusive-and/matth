
module Algebra.Monoids

import Theory.AxiomJ
import Algebra.Properties
import Algebra.Magma
import Algebra.Semigroups

%hide Prelude.Algebra.Monoid
%hide Prelude.Algebra.Semigroup


public export
record Monoid (a : Type) (e : a) (m : a -> a -> a) where
    constructor MkMonoid
    semigroup : Semigroup a m
    identity : hasIdentity {a} e m
