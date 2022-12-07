
module AlgSet.Magma

import Theory.AxiomJ
import Theory.Sets


public export
IsClosed : {t : Type} -> (s : Set t) -> SetOp2 s -> Type
IsClosed {t} s m =
    (x : t) -> (p : s x) -> (y : t) -> (q : s y) -> s (m x p y q)

public export
record Magma (t : Type) where
    constructor MkMagma
    carrierSet : Set t
    magmaOp    : SetOp2 carrierSet
    isClosed   : IsClosed carrierSet magmaOp

public export
interface XMagma (r : Type -> Type) where
    xCarrier   : {t : Type} -> r t -> Set t
    xOperation : (rec : r t) -> SetOp2 (xCarrier rec)
    xIsClosed  : (rec : r t) -> IsClosed (xCarrier rec) (xOperation rec)

public export
xMagma : XMagma r => r t -> Magma t
xMagma r = MkMagma (xCarrier r) (xOperation r) (xIsClosed r)

public export
XMagma Magma where
    xCarrier   = carrierSet
    xOperation = magmaOp
    xIsClosed  = isClosed
