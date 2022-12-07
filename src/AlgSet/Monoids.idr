
module AlgSet.Monoids

import Theory.AxiomJ
import Theory.Sets
import AlgSet.Magma
import AlgSet.Semigroups

%hide Prelude.Algebra.Semigroup
%hide Prelude.Algebra.Monoid


public export
IsIdentity : {t : Type} -> t -> (t -> t -> t) -> Type
IsIdentity {t} e m = (x : t) -> Id (m e x) x

public export
record Monoid (t : Type) where
    constructor MkMonoid
    carrierSet    : Set t
    monoidOp      : t -> t -> t
    isClosed      : IsClosed carrierSet monoidOp
    isAssociative : IsAssociative monoidOp
    identity      : t
    hasIdentity   : carrierSet identity
    isIdentity    : IsIdentity identity monoidOp

public export
interface XSemigroup r => XMonoid (r : Type -> Type) where
    xIdentity    : r t -> t
    xHasIdentity : (rec : r t) -> xCarrier rec (xIdentity rec)
    xIsIdentity  : (rec : r t)
                -> IsIdentity (xIdentity rec) (xOperation rec)

public export
xMonoid : XMonoid r => r t -> Monoid t
xMonoid r =
    MkMonoid
        (xCarrier r) (xOperation r) (xIsClosed r)       -- Magma laws
        (xIsAssociative r)                              -- Semigroup laws
        (xIdentity r) (xHasIdentity r) (xIsIdentity r)  -- Monoid laws


public export
XMagma Monoid where
    xCarrier    = carrierSet
    xOperation  = monoidOp
    xIsClosed   = isClosed

public export
XSemigroup Monoid where
    xIsAssociative = isAssociative

public export
XMonoid Monoid where
    xIdentity    = identity
    xHasIdentity = hasIdentity
    xIsIdentity  = isIdentity


public export
record SubMonoid (t : Type) where
    constructor MkSubMonoid
    superMonoid : Monoid t
    subset      : Set t
    isSubset    : IsSubset subset (carrierSet superMonoid)
    isClosed    : IsClosed subset (monoidOp superMonoid)
    hasIdentity : subset (identity superMonoid)

public export
XMagma SubMonoid where
    xCarrier     = subset
    xOperation m = let super = superMonoid m in monoidOp super
    xIsClosed    = isClosed

public export
XSemigroup SubMonoid where
    xIsAssociative m =
      let
        super = superMonoid m
      in
        isAssociative super

public export
XMonoid SubMonoid where
    xIdentity m   = let super = superMonoid m in identity super
    xHasIdentity  = hasIdentity
    xIsIdentity m = let super = superMonoid m in isIdentity super


postulate intMonoid : Monoid Int
