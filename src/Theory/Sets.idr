
module Theory.Sets

import Theory.AxiomJ


public export
Set : (t : Type) -> Type
Set t = t -> Type

public export
element : {t : Type} -> (s : Set t) -> (x : t) -> Type
element {t} s x = s x


||| Sets generated by a generator and an operation.
data GeneratedSet : (t : Type) -> (x : t) -> Type
  where
    Generator : (x : t)
             -> GeneratedSet t x

    Generated1 : (m : t -> t)
              -> (x : t) -> GeneratedSet t x
              -> GeneratedSet t (m x)

    Generated2 : (m : t -> t -> t)
              -> (x : t) -> GeneratedSet t x
              -> (y : t) -> GeneratedSet t y
              -> GeneratedSet t (m x y)


public export
IsSubset : {t : Type} -> (u, v : Set t) -> Type
IsSubset {t} u v = (x : t) -> u x -> v x

public export
SetEq : {t : Type} -> (u, v : Set t) -> Type
SetEq {t} u v = (IsSubset u v, IsSubset v u)


||| Set operations with closure built-in

public export
ClosedOp1 : {t : Type} -> (s : Set t) -> Type
ClosedOp1 {t} s = (x : t) -> s x -> DPair t s

public export
ClosedOp2 : {t : Type} -> (s : Set t) -> Type
ClosedOp2 {t} s =
    (x : t) -> s x -> (y : t) -> s y -> DPair t s
