
module Polynomials.Poly

import Theory.AxiomJ
import Theory.Sets
import AlgSet.Magma
import AlgSet.Semigroups
import AlgSet.Monoids
import AlgSet.Groups
import AlgSet.Rings

import Convolution

import Prelude.List


||| Polynomials as lists of coefficients from a ring.
public export
data Polynomial : (coeffTy : Type) -> (r : Ring coeffTy) -> Type where
    Poly : List (DPair coeffTy (carrierSet r)) -> Polynomial coeffTy r

||| Add two polynomials together using an open zip.
public export
polyAdd : {r : Ring t}
       -> Polynomial t r
       -> Polynomial t r
       -> Polynomial t r

polyAdd {r} (Poly aCoeffs) (Poly bCoeffs) =
    Poly $ openZipWith id id go aCoeffs bCoeffs
  where
    go : DPair t (carrierSet r)
      -> DPair t (carrierSet r)
      -> DPair t (carrierSet r)
    go (x ** p) (y ** q) =
        MkDPair (addOp r x y) (addIsClosed r x p y q)

||| Invert a polynomial by inverting all its coefficients.
public export
polyAddInvert : {r : Ring t}
             -> Polynomial t r
             -> Polynomial t r

polyAddInvert {r} (Poly xs) = Poly $ map go xs where
    go : DPair t (carrierSet r)
      -> DPair t (carrierSet r)
    go (x ** p) =
        MkDPair (addInvert r x) (addHasInverse r x p)

||| Multiply two polynomials with a convolution.
public export
polyMul : {r : Ring t}
       -> Polynomial t r
       -> Polynomial t r
       -> Polynomial t r

polyMul {r} (Poly aCoeffs) (Poly bCoeffs) =
    Poly $ map reduce $ convolveWith go aCoeffs bCoeffs
  where
    go : DPair t (carrierSet r)
      -> DPair t (carrierSet r)
      -> DPair t (carrierSet r)
    go (x ** p) (y ** q) =
        MkDPair (mulOp r x y) (mulIsClosed r x p y q)

    goReduce : DPair t (carrierSet r)
            -> DPair t (carrierSet r)
            -> DPair t (carrierSet r)
    goReduce (x ** p) (acc ** accq) =
        MkDPair (addOp r x acc) (addIsClosed r x p acc accq)

    reduce : List (DPair t (carrierSet r))
          -> DPair t (carrierSet r)
    reduce Nil =
        MkDPair (addIdentity r) (addHasIdentity r)

    reduce (x :: xs) = goReduce x (reduce xs)


public export
polyAddAssoc : IsAssociative polyAdd
polyAddAssoc = ?realPolyAddAssoc

public export
polyAddCommutes : IsCommutative polyAdd
polyAddCommutes = ?realPolyAddCommute

public export
nilPolyIsPolyAddId : IsIdentity (Poly Nil) polyAdd
nilPolyIsPolyAddId = ?realNilPolyIsPolyAddId

public export
isPolyAddInverse : {r : Ring t} -> IsInverse (Poly Nil) polyAdd polyAddInvert
isPolyAddInverse = ?realIsPolyAddInverse

public export
polyMulAssoc : IsAssociative polyMul
polyMulAssoc = ?realPolyMulAssoc

public export
polynomialRing : {r : Ring t} -> Ring (Polynomial t r)
polynomialRing {r} =
    MkRing
        (\x => ())  -- The polynomial set's only restriction is that all
                    -- coefficients are in the carrier set of the ring. Since
                    -- that's enforced by construction, the set is trivial.
        -- Polynomial addition group laws
        polyAdd (\x, p, y, q => ())
        polyAddAssoc
        polyAddCommutes
        (Poly Nil) () nilPolyIsPolyAddId
        polyAddInvert (\x, p => ()) (isPolyAddInverse {r})
        -- Polynomial multiplication semigroup laws
        polyMul (\x, p, y, q => ())
        polyMulAssoc


public export
poly1 : Polynomial Int AlgSet.Rings.intRing
poly1 = Poly [MkDPair 1 (), MkDPair 0 (), MkDPair 1 ()]

public export
poly2 : Polynomial Int AlgSet.Rings.intRing
poly2 = Poly [MkDPair 7 (), MkDPair 2 ()]

public export
poly3 : Polynomial Int AlgSet.Rings.evenIntRing
poly3 = Poly [MkDPair 6 (3 ** refl), MkDPair 54 (27 ** refl), MkDPair 22 (11 ** refl)]

public export
poly4 : Polynomial Int AlgSet.Rings.evenIntRing
poly4 = Poly [MkDPair 38 (19 ** refl), MkDPair 32 (16 ** refl)]
