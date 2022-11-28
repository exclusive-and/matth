
module AlgTy.Magma

import Theory.AxiomJ
import AlgTy.Properties

%hide Prelude.Algebra.Monoid
%hide Prelude.Algebra.Semigroup
%hide Prelude.Nat.Nat
%hide Prelude.Nat.plus
%hide Prelude.Nat.mult


public export
record IsMagma (a : Type) (m : a -> a -> a) where
    constructor MkMagmaProp
    cong : (x, y, u, v : a) -> Id x y -> Id u v -> Id (m x u) (m y v)

