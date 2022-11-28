
module AlgSet.Groups

import Theory.AxiomJ
import Theory.Sets


public export
HasInverse : {t : Type}
          -> (s : Set t)
          -> (inv : (x : t) -> s x -> t)
          -> Type
HasInverse {t} s inv = (x : t) -> s x -> s (inv x)

public export
record IsGroup (t : Type) (s : Set t) (e : t) (m : SetOp2 {t} s) where
    constructor MkGroupProp

    isMagma : IsMagma s g 

public export
record Group (t : Type) (s : Set t) where
    constructor MkGroup
    mult : (x : t) -> s x -> (y : t) -> s y -> t

    isGroup : IsGroup t s e inv mult
