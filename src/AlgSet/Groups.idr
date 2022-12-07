
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
         -> (s : Set t)
         -> (e : t)
         -> (t -> t -> t)
         -> (inv : (x : t) -> t)
         -> Type
IsInverse {t} s e m inv = (x : t) -> Id (m (inv x) x) e

public export
record Group (t : Type) where
    constructor MkGroup
    carrierSet    : Set t
    groupOp       : t -> t -> t
    isClosed      : IsClosed carrierSet groupOp
    isAssociative : IsAssociative carrierSet groupOp
    identity      : t
    hasIdentity   : carrierSet identity
    isIdentity    : IsIdentity carrierSet identity groupOp
    invert        : t -> t
    hasInverse    : HasInverse carrierSet invert
    isInverse     : IsInverse carrierSet identity
                              groupOp invert

public export
interface XMonoid r => XGroup (r : Type -> Type) where
    xInvert     : (rec : r t) -> t -> t
    xHasInverse : (rec : r t) -> HasInverse (xCarrier rec) (xInvert rec)
    xIsInverse  : (rec : r t)
               -> IsInverse (xCarrier rec) (xIdentity rec)
                            (xOperation rec) (xInvert rec)

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

