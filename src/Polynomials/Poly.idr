
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


public export
data Polynomial : (coeffTy : Type) -> (r : Ring coeffTy) -> Type where
    Poly : List (DPair coeffTy (carrierSet r)) -> Polynomial coeffTy r

polyAdd : {r : Ring t} -> Polynomial t r -> Polynomial t r -> Polynomial t r
polyAdd {r} (Poly aCoeffs) (Poly bCoeffs) =
    Poly $ openZipWith id id go aCoeffs bCoeffs
  where
    go : DPair t (carrierSet r) -> DPair t (carrierSet r) -> DPair t (carrierSet r)
    go (MkDPair x p) (MkDPair y q) =
      let
        addGroup = ringAddGroup r
        add      = xOperation addGroup
        closed   = xIsClosed addGroup
      in
        MkDPair (add x y) (closed x p y q)


polyMul : {r : Ring t} -> Polynomial t r -> Polynomial t r -> Polynomial t r
polyMul {r} (Poly aCoeffs) (Poly bCoeffs) =
    Poly $ map reduce $ convolveWith go aCoeffs bCoeffs
  where
    go : DPair t (carrierSet r) -> DPair t (carrierSet r) -> DPair t (carrierSet r)
    go (x ** p) (y ** q) =
      let
        mulSemigroup = ringMulSemigroup r
        mul          = xOperation mulSemigroup
        closed       = xIsClosed mulSemigroup
      in
        MkDPair (mul x y) (closed x p y q)

    goReduce : DPair t (carrierSet r) -> DPair t (carrierSet r) -> DPair t (carrierSet r)
    goReduce (x ** p) (acc ** accq) =
      let
        addGroup = ringAddGroup r
        add      = xOperation addGroup
        closed   = xIsClosed addGroup
      in
        MkDPair (add x acc) (closed x p acc accq)

    reduce : List (DPair t (carrierSet r)) -> DPair t (carrierSet r)
    reduce Nil       = MkDPair (addIdentity r) (addHasIdentity r)
    reduce (x :: xs) = goReduce x (reduce xs)



postulate intAddAssoc : IsAssociative {t = Int} (\x => ()) (+)

postulate intAddId : IsIdentity {t = Int} (\x => ()) 0 (+)

postulate intAddInv : IsInverse {t = Int} (\x => ()) 0 (+) negate


postulate intMulAssoc : IsAssociative {t = Int} (\x => ()) (*)

export
intRing : Ring Int
intRing =
    MkRing
        (\x => ()) (+) (\x, p, y, q => ())
        intAddAssoc
        0 () intAddId
        negate (\x, p => ()) intAddInv
        (*) (\x, p, y, q => ())
        intMulAssoc

export
poly1 : Polynomial Int Polynomials.Poly.intRing
poly1 = Poly [MkDPair 1 (), MkDPair 0 (), MkDPair 1 ()]

export
poly2 : Polynomial Int Polynomials.Poly.intRing
poly2 = Poly [MkDPair 7 (), MkDPair 2 ()]
