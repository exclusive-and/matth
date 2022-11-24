
module Theory.Sets

import Theory.AxiomJ


public export
Set : (s : Type) -> Type
Set s = s -> Type

public export
element : {s : Type} -> (v : Set s) -> (x : s) -> Type
element {s} v x = v x

public export
IsSubset : {s : Type}
        -> (u, v : Set s)
        -> (x : s)
        -> element {s} u x
        -> Type
IsSubset {s} u v x p = element {s} v x
