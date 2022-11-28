
module AlgSet.Magma

import Theory.AxiomJ
import Theory.Sets


public export
IsClosed : {t : Type} -> (s : Set t) -> SetOp2 s -> Type
IsClosed {t} s m =
    (x : t) -> (p : s x) -> (y : t) -> (q : s y) -> s (m x p y q)

public export
record IsMagma (t : Type) (s : Set t) (m : SetOp2 s) where
    constructor MkMagmaProp
    
    isClosed : IsClosed s m

public export
record Magma (t : Type) (s : Set t) where
    constructor MkMagma
    mult : (x : t) -> s x -> (y : t) -> s y -> t

    isMagma : IsMagma t s mult

