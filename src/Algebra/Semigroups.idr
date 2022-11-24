
module Algebra.Semigroups

import Theory.AxiomJ
import Algebra.Properties
import Algebra.Magma

%hide Prelude.Algebra.Monoid
%hide Prelude.Algebra.Semigroup


public export
record Semigroup (a : Type) (m : a -> a -> a) where
    constructor MkSemigroup
    magma : Magma a m
    assoc : isAssociative {a} m
