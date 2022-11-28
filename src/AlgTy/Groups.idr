
module AlgTy.Groups

import Theory.AxiomJ
import AlgTy.Properties
import AlgTy.Magma
import AlgTy.Semigroups
import AlgTy.Monoids

%hide Prelude.Algebra.Monoid
%hide Prelude.Algebra.Semigroup
%hide Prelude.Nat.Nat
%hide Prelude.Nat.plus
%hide Prelude.Nat.mult


public export
record IsGroup (a : Type) (e : a) (m : a -> a -> a) (inv : a -> a) where
    constructor MkGroupProp
    isMonoid : IsMonoid a e m
    isInvertible : IsInvertible {a} e m inv

public export
record Group (a : Type) where
    constructor MkGroup
    mult : a -> a -> a
    identity : a
    invert : a -> a

    isGroup : IsGroup a identity mult invert

