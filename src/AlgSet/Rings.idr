
module AlgSet.Rings

import Theory.AxiomJ
import Theory.Sets
import AlgSet.Magma
import AlgSet.Semigroups
import AlgSet.Monoids
import AlgSet.Groups

%hide Prelude.Algebra.Semigroup
%hide Prelude.Algebra.Monoid
%hide Prelude.Nat.(-)


public export
record Ring (t : Type) where
    constructor MkRing
    carrierSet  : Set t
    -- Addition is an Abelian group
    addOp            : t -> t -> t
    addIsClosed      : IsClosed carrierSet addOp
    addIsAssociative : IsAssociative addOp
    addIdentity      : t
    addHasIdentity   : carrierSet addIdentity
    addIsIdentity    : IsIdentity addIdentity addOp
    addInvert        : t -> t
    addHasInverse    : HasInverse carrierSet addInvert
    addIsInverse     : IsInverse addIdentity addOp addInvert
    -- Multiplication is a semigroup
    mulOp            : t -> t -> t
    mulIsClosed      : IsClosed carrierSet mulOp
    mulIsAssociative : IsAssociative mulOp

public export
ringAddGroup : Ring t -> Group t
ringAddGroup r =
    MkGroup
        (carrierSet r) (addOp r) (addIsClosed r)
        (addIsAssociative r)
        (addIdentity r) (addHasIdentity r) (addIsIdentity r)
        (addInvert r) (addHasInverse r) (addIsInverse r)

public export
ringMulSemigroup : Ring t -> Semigroup t
ringMulSemigroup r =
    MkSemigroup
        (carrierSet r) (mulOp r) (mulIsClosed r)
        (mulIsAssociative r)


public export
record SubRing (t : Type) where
    constructor MkSubRing
    superRing      : Ring t
    subset         : Set t
    -- Addition subgroup
    addIsClosed    : IsClosed subset (addOp superRing)
    addHasIdentity : subset (addIdentity superRing)
    addHasInverse  : HasInverse subset (addInvert superRing)
    -- Multiplication subsemigroup
    mulIsClosed    : IsClosed subset (mulOp superRing)

public export
subringIsRing : SubRing t -> Ring t
subringIsRing sub =
  let
    super = superRing sub
  in
    MkRing
        (subset sub) (addOp super) (addIsClosed sub)
        (addIsAssociative super)
        (addIdentity super) (addHasIdentity sub) (addIsIdentity super)
        (addInvert super) (addHasInverse sub) (addIsInverse super)
        (mulOp super) (mulIsClosed sub)
        (mulIsAssociative super)
