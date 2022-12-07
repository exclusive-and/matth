
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
    addIsAssociative : IsAssociative carrierSet addOp
    addIdentity      : t
    addHasIdentity   : carrierSet addIdentity
    addIsIdentity    : IsIdentity carrierSet addIdentity addOp
    addInvert        : t -> t
    addHasInverse    : HasInverse carrierSet addInvert
    addIsInverse     : IsInverse carrierSet addIdentity
                                 addOp addInvert
    -- Multiplication is a semigroup
    mulOp            : t -> t -> t
    mulIsClosed      : IsClosed carrierSet mulOp
    mulIsAssociative : IsAssociative carrierSet mulOp

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

