
module AlgSet.Groups

import Theory.AxiomJ
import Theory.Sets
import AlgSet.Magma
import AlgSet.Semigroups
import AlgSet.Monoids

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
record IsGroup (t : Type) (s : Set t) (e : t) (m : SetOp2 {t} s) (inv : SetOp1 {t} s) where
    constructor MkGroupProp

    isMonoid   : IsMonoid t s e m
    hasInverse : HasInverse s inv
    isInverse  : IsInverse s e (eInSet isMonoid) m inv hasInverse

public export
record Group (t : Type) (s : Set t) where
    constructor MkGroup
    mult     : (x : t) -> s x -> (y : t) -> s y -> t
    inv      : (x : t) -> s x -> t
    identity : t
    isGroup  : IsGroup t s identity mult inv


{-
postulate plusAssociates : (x : Int) -> () -> (y : Int) -> () -> (z : Int) -> () -> () -> () -> Id (x + (y + z)) ((x + y) + z)

postulate zeroIsIdentity : (x : Int) -> () -> Id (0 + x) x

postulate negateIsInverse : (x : Int) -> () -> Id ((negate x) + x) 0

export
intGroupProp : IsGroup Int (\x => ()) 0 (\x, p, y, q => x + y) (\x, p => negate x)
intGroupProp =
  let
    magma     = MkMagmaProp (\x, p, y, q => ())
    semigroup = MkSemigroupProp magma plusAssociates
    monoid    = MkMonoidProp semigroup () zeroIsIdentity

    hasInv = (\x, p => ())
  in
    MkGroupProp monoid hasInv negateIsInverse
-}
