
module AlgSet.Rings

import Theory.AxiomJ
import Theory.Sets
import Theory.Homomorphisms
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
    addIsCommutative : IsCommutative addOp
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
ringAddGroup : Ring t -> AbelianGroup t
ringAddGroup r =
    MkAbelianGroup
        (carrierSet r) (addOp r) (addIsClosed r)
        (addIsAssociative r)
        (addIsCommutative r)
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
        (addIsCommutative super)
        (addIdentity super) (addHasIdentity sub) (addIsIdentity super)
        (addInvert super) (addHasInverse sub) (addIsInverse super)
        (mulOp super) (mulIsClosed sub)
        (mulIsAssociative super)


public export
record RingHom (domainTy : Type) (codomainTy : Type) where
    constructor MkRingHom
    domain       : Ring domainTy
    codomain     : Ring codomainTy

    homMap : domainTy -> codomainTy

    preservesAdd : HomPreserves (addOp domain) (addOp codomain) homMap
    preservesMul : HomPreserves (mulOp domain) (mulOp codomain) homMap

||| Ring endomorphisms: trivial homomorphisms.
public export
ringEndo : Ring t -> RingHom t t
ringEndo r = MkRingHom r r id (\x, y => refl) (\x, y => refl)


||| Example rings (TODO: prove laws)

public export
intRing : Ring Int
intRing =
    MkRing
        (\x => ())
        (+) (\x, p, y, q => ())
        intAddAssoc
        intAddCommutes
        0 () zeroIsIntAddId
        negate (\x, p => ()) negateIsIntAddInv
        (*) (\x, p, y, q => ())
        intMulAssoc
  where
    intAddAssoc : IsAssociative {t = Int} (+)
    intAddAssoc = ?realIntAddAssoc

    intAddCommutes : IsCommutative {t = Int} (+)
    intAddCommutes = ?realIntAddCommutes

    zeroIsIntAddId : IsIdentity {t = Int} 0 (+)
    zeroIsIntAddId = ?realZeroIsIntAddId

    negateIsIntAddInv : IsInverse {t = Int} 0 (+) negate
    negateIsIntAddInv = ?realNegateIsIntAddInv

    intMulAssoc : IsAssociative {t = Int} (*)
    intMulAssoc = ?realIntMulAssoc

||| Even subring of integer ring.
public export
evenIntSubInt : SubRing Int
evenIntSubInt =
    MkSubRing
        intRing
        (\x => DPair Int (\k => Id (2 * k) x))
        evenIntRingAddIsClosed
        (0 ** refl)
        evenIntRingAddHasInv
        evenIntRingMulIsClosed
  where
    evenIntRingAddIsClosed : IsClosed (\x => DPair Int (\k => Id (2 * k) x)) (+)
    evenIntRingAddIsClosed x (j ** p) y (k ** q) =
        ?realEvenIntRingAddIsClosed

    evenIntRingAddHasInv : HasInverse (\x => DPair Int (\k => Id (2 * k) x)) negate
    evenIntRingAddHasInv x (k ** p) =
        ?realEvenIntRingAddHasInv

    evenIntRingMulIsClosed : IsClosed (\x => DPair Int (\k => Id (2 * k) x)) (*)
    evenIntRingMulIsClosed x (j ** p) y (k ** q) =
        ?realEvenIntRingMulIsClosed

||| Ring of even integers from even subring.
public export
evenIntRing : Ring Int
evenIntRing = subringIsRing evenIntSubInt

||| Homomorphism from integer ring to even ring.
export
intToEvenIntHom : RingHom Int Int
intToEvenIntHom =
    MkRingHom
        intRing
        evenIntRing
        (* 2)
        preservesAdd
        preservesMul
  where
    preservesAdd : HomPreserves {domainTy = Int} {codomainTy = Int} (+) (+) (* 2)
    preservesAdd = ?realPreservesAdd

    preservesMul : HomPreserves {domainTy = Int} {codomainTy = Int} (*) (*) (* 2)
    preservesMul = ?realPreservesMul
