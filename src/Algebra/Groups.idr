
module Algebra.Groups

import Theory.AxiomJ
import Algebra.Properties
import Algebra.Magma
import Algebra.Semigroups
import Algebra.Monoids

%hide Prelude.Algebra.Monoid
%hide Prelude.Algebra.Semigroup


public export
record Group (a : Type) (e : a) (m : a -> a -> a) (inv : a -> a) where
    constructor MkGroup
    monoid : Monoid a e m
    invertible : isInvertible {a} e m inv

