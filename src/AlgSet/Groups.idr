
module AlgSet.Groups

import Theory.AxiomJ
import Theory.Sets
import AlgSet.Magma
import AlgSet.Semigroups
import AlgSet.Monoids

%hide Prelude.Algebra.Semigroup
%hide Prelude.Algebra.Monoid
%hide Prelude.Nat.(-)


public export
HasInverse : {t : Type}
          -> (s : Set t)
          -> (inv : (x : t) -> t)
          -> Type
HasInverse {t} s inv = (x : t) -> s x -> s (inv x)

public export
IsInverse : {t : Type}
         -> (e : t)
         -> (t -> t -> t)
         -> (inv : (x : t) -> t)
         -> Type
IsInverse {t} e m inv = (x : t) -> Id (m (inv x) x) e

public export
record Group (t : Type) where
    constructor MkGroup
    carrierSet    : Set t
    groupOp       : t -> t -> t
    isClosed      : IsClosed carrierSet groupOp
    isAssociative : IsAssociative groupOp
    identity      : t
    hasIdentity   : carrierSet identity
    isIdentity    : IsIdentity identity groupOp
    invert        : t -> t
    hasInverse    : HasInverse carrierSet invert
    isInverse     : IsInverse identity  groupOp invert

public export
interface XMonoid r => XGroup (r : Type -> Type) where
    xInvert     : (rec : r t) -> t -> t
    xHasInverse : (rec : r t) -> HasInverse (xCarrier rec) (xInvert rec)
    xIsInverse  : (rec : r t)
               -> IsInverse (xIdentity rec) (xOperation rec) (xInvert rec)

public export
xGroup : XGroup r => r t -> Group t
xGroup r =
    MkGroup
        (xCarrier r) (xOperation r) (xIsClosed r)
        (xIsAssociative r)
        (xIdentity r) (xHasIdentity r) (xIsIdentity r)
        (xInvert r) (xHasInverse r) (xIsInverse r)

public export
XMagma Group where
    xCarrier    = carrierSet
    xOperation  = groupOp
    xIsClosed   = isClosed

public export
XSemigroup Group where
    xIsAssociative = isAssociative

public export
XMonoid Group where
    xIdentity    = identity
    xHasIdentity = hasIdentity
    xIsIdentity  = isIdentity

public export
XGroup Group where
    xInvert     = invert
    xHasInverse = hasInverse
    xIsInverse  = isInverse


public export
record SubGroup (t : Type) where
    constructor MkSubGroup
    superGroup  : Group t
    subset      : Set t
    isSubset    : IsSubset subset (carrierSet superGroup)
    isClosed    : IsClosed subset (groupOp superGroup)
    hasIdentity : subset (identity superGroup)
    hasInverse  : HasInverse subset (invert superGroup)

public export
XMagma SubGroup where
    xCarrier     = subset
    xOperation m = let super = superGroup m in groupOp super
    xIsClosed    = isClosed

public export
XSemigroup SubGroup where
    xIsAssociative m =
      let
        super = superGroup m
      in
        isAssociative super

public export
XMonoid SubGroup where
    xIdentity m   = let super = superGroup m in identity super
    xHasIdentity  = hasIdentity
    xIsIdentity m = let super = superGroup m in isIdentity super


public export
IsCommutative : {t : Type} -> (t -> t -> t) -> Type
IsCommutative {t} m =
    (x : t) -> (y : t) -> Id (m x y) (m y x)

public export
record AbelianGroup (t : Type) where
    constructor MkAbelianGroup
    carrierSet    : Set t
    groupOp       : t -> t -> t
    isClosed      : IsClosed carrierSet groupOp
    isAssociative : IsAssociative groupOp
    isCommutative : IsCommutative groupOp
    identity      : t
    hasIdentity   : carrierSet identity
    isIdentity    : IsIdentity identity groupOp
    invert        : t -> t
    hasInverse    : HasInverse carrierSet invert
    isInverse     : IsInverse identity  groupOp invert

public export
XMagma AbelianGroup where
    xCarrier    = carrierSet
    xOperation  = groupOp
    xIsClosed   = isClosed

public export
XSemigroup AbelianGroup where
    xIsAssociative = isAssociative

public export
XMonoid AbelianGroup where
    xIdentity    = identity
    xHasIdentity = hasIdentity
    xIsIdentity  = isIdentity

public export
XGroup AbelianGroup where
    xInvert     = invert
    xHasInverse = hasInverse
    xIsInverse  = isInverse
