
module Theory.Sets

import Theory.AxiomJ


public export
Set : (t : Type) -> Type
Set t = t -> Type

public export
element : {t : Type} -> (s : Set t) -> (x : t) -> Type
element {t} s x = s x

public export
IsSubset : {t : Type} -> (u, v : Set t) -> (x : t) -> u x -> Type
IsSubset {t} u v x p = v x

public export
SetOp1 : {t : Type} -> (s : Set t) -> Type
SetOp1 {t} s = (x : t) -> s x -> t

public export
SetOp2 : {t : Type} -> (s : Set t) -> Type
SetOp2 {t} s = (x : t) -> s x -> (y : t) -> s y -> t
