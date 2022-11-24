
module Algebra.Magma

import Theory.AxiomJ
import Algebra.Properties

%hide Prelude.Algebra.Monoid
%hide Prelude.Algebra.Semigroup


public export
record Magma (a : Type) (m : a -> a -> a) where
    constructor MkMagma
    cong : (x, y, u, v : a) -> Id x y -> Id u v -> Id (m x u) (m y v)

