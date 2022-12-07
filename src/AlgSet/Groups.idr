
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
          -> (inv : (x : t) -> s x -> t)
          -> Type
HasInverse {t} s inv = (x : t) -> (p : s x) -> s (inv x p)

public export
IsInverse : {t : Type}
         -> (s : Set t)
         -> (e : t)
         -> s e
         -> SetOp2 {t} s
         -> (inv : SetOp1 {t} s)
         -> HasInverse {t} s inv
         -> Type
IsInverse {t} s e p m inv hasInv =
    (x : t) -> (q : s x) -> Id (m (inv x q) (hasInv x q) x q) e

public export
record Group (t : Type) where
    constructor MkGroup
    carrierSet    : Set t
    groupOp       : SetOp2 carrierSet
    isClosed      : IsClosed carrierSet groupOp
    isAssociative : IsAssociative carrierSet groupOp
    identity      : t
    hasIdentity   : carrierSet identity
    isIdentity    : IsIdentity carrierSet identity hasIdentity groupOp
    invert        : SetOp1 carrierSet
    hasInverse    : HasInverse carrierSet invert
    isInverse     : IsInverse carrierSet identity hasIdentity
                              groupOp invert hasInverse

public export
interface XMonoid r => XGroup (r : Type -> Type) where
    xInvert     : (rec : r t) -> SetOp1 (xCarrier rec)
    xHasInverse : (rec : r t) -> HasInverse (xCarrier rec) (xInvert rec)
    xIsInverse  : (rec : r t)
               -> IsInverse (xCarrier rec) (xIdentity rec) (xHasIdentity rec)
                            (xOperation rec) (xInvert rec) (xHasInverse rec)

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

