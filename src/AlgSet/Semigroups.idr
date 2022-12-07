
module AlgSet.Semigroups

import Theory.AxiomJ
import Theory.Sets
import AlgSet.Magma

%hide Prelude.Algebra.Semigroup


public export
IsAssociative : {t : Type} -> (s : Set t) -> SetOp2 {t} s -> Type
IsAssociative {t} s m = (x : t) -> (p : s x)
                     -> (y : t) -> (q : s y)
                     -> (z : t) -> (r : s z)
                     -> (u : s (m x p y q))
                     -> (v : s (m y q z r))
                     -> Id (m x p (m y q z r) v) (m (m x p y q) u z r)

public export
record Semigroup (t : Type) where
    constructor MkSemigroup
    carrierSet      : Set t
    semigroupOp     : SetOp2 carrierSet
    isClosed        : IsClosed carrierSet semigroupOp
    isAssociative   : IsAssociative carrierSet semigroupOp

public export
interface XMagma r => XSemigroup (r : Type -> Type) where
    xIsAssociative  : (rec : r t) -> IsAssociative (xCarrier rec) (xOperation rec)

public export
xSemigroup : XSemigroup r => r t -> Semigroup t
xSemigroup r =
    MkSemigroup
        (xCarrier r) (xOperation r) (xIsClosed r) -- Magma laws
        (xIsAssociative r)                        -- Semigroup laws

public export
XMagma Semigroup where
    xCarrier   = carrierSet
    xOperation = semigroupOp
    xIsClosed  = isClosed

public export
XSemigroup Semigroup where
    xIsAssociative = isAssociative
