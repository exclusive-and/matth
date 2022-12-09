
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
    -- Morphism laws
    homMap       : domainTy -> codomainTy
    homIsTotal   : (x : domainTy)
                -> carrierSet domain x
                -> carrierSet codomain (homMap x)
    -- Structure-preserving laws
    preservesAdd : HomPreserves (addOp domain) (addOp codomain) homMap
    preservesMul : HomPreserves (mulOp domain) (mulOp codomain) homMap

||| Ring endomorphisms: trivial homomorphisms.
public export
ringEndo : Ring t -> RingHom t t
ringEndo r =
    MkRingHom r r id (\x, p => p) (\x, y => refl) (\x, y => refl)


||| Ideal of a ring.
public export
record Ideal (t : Type) (ring : Ring t) where
    constructor MkIdeal
    subset   : Set t
    isSubset : IsSubset subset (carrierSet ring)
    -- Addition subgroup
    addIsClosed     : IsClosed subset (addOp ring)
    addHasIdentity  : subset (addIdentity ring)
    addHasInverse   : HasInverse subset (addInvert ring)
    -- R-closure under multiplication
    rMulIsClosed : (r : t) -> (carrierSet ring r)
                -> (x : t) -> subset x
                -> subset (mulOp ring r x)

public export
kerSet : RingHom domainTy codomainTy -> domainTy -> Type
kerSet hom x =
    ( carrierSet (domain hom) x
    , Id (homMap hom x) (addIdentity (codomain hom))
    )

||| The kernel of a homomorphism is an ideal.
public export
kerIdeal : RingHom domainTy codomainTy -> Ideal domainTy (domain hom)
kerIdeal hom =
    MkIdeal
        (kerSet hom) (\x, p => fst p)
        kerAddIsClosed
        kerAddHasIdentity
        ?kerAddHasInverse
        ?kerRMulIsClosed
  where
    kerAddIsClosed : IsClosed (kerSet hom) (addOp (domain hom))
    kerAddIsClosed x (p1, p2) y (q1, q2) =
      let
        add   = addOp $ domain hom
        coadd = addOp $ codomain hom
        f     = homMap hom

        step1 = transport {prop = Id (f (add x y))} (preservesAdd hom x y) refl
        -- Id (hom (m x y)) (hom (m x y)) -----> Id (hom (m x y)) (n (hom x) (hom y))   by preservesAdd
        step2 = transport {prop = \k => Id (f (add x y)) (coadd k (f y))} p2 step1
        -- Id (hom (m x y)) (n (hom x) (hom y)) -----> Id (hom (m x y)) (n 0 (hom y))   by p
        step3 = transport {prop = Id (f (add x y))} (addIsIdentity (codomain hom) (f y)) step2
        -- Id (hom (m x y)) (n 0 (hom y)) -----> Id (hom (m x y)) (hom y)               by addIsIdentity
        step4 = transport {prop = Id (f (add x y))} q2 step3
        -- Id (hom (m x y)) (hom y) -----> Id (hom (m x y)) 0                           by q
      in
        (addIsClosed (domain hom) x p1 y q1, step4)

    kerAddHasIdentity : kerSet hom (addIdentity (domain hom))
    kerAddHasIdentity =
      let
        step1 = ?realKerAddHasIdentity
      in
        (addHasIdentity (domain hom), step1)


public export
zeroSet : Ring t -> t -> Type
zeroSet r x = Id (addIdentity r) x

||| A ring with only the ideals {0} and R is simple.
public export
data TrivialIdeal
    : (t : Type) -> (r : Ring t) -> Ideal t r -> Type
  where
    ZeroIdeal : (i : Ideal t r)
             -> SetEq (zeroSet (ring i)) (subset i)
             -> TrivialIdeal t r i

    FullIdeal : (i : Ideal t r)
             -> SetEq (carrierSet (ring i)) (subset i)
             -> TrivialIdeal t r i

public export
IsSimpleRing : (r : Ring t) -> Type
IsSimpleRing r = (i : Ideal t r) -> TrivialIdeal t r i


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
        (2 *) (\x, p => MkDPair x refl)
        preservesAdd
        preservesMul
  where
    preservesAdd : HomPreserves {domainTy = Int} {codomainTy = Int} (+) (+) (2 *)
    preservesAdd = ?realPreservesAdd

    preservesMul : HomPreserves {domainTy = Int} {codomainTy = Int} (*) (*) (2 *)
    preservesMul = ?realPreservesMul
