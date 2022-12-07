
module AlgSet.Magma

import Theory.AxiomJ
import Theory.Sets


public export
IsClosed : {t : Type} -> (s : Set t) -> (t -> t -> t) -> Type
IsClosed {t} s m =
    (x : t) -> (p : s x) -> (y : t) -> (q : s y) -> s (m x y)

public export
record Magma (t : Type) where
    constructor MkMagma
    carrierSet : Set t
    magmaOp    : t -> t -> t
    isClosed   : IsClosed carrierSet magmaOp

public export
interface XMagma (r : Type -> Type) where
    xCarrier   : {t : Type} -> r t -> Set t
    xOperation : (rec : r t) -> t -> t -> t
    xIsClosed  : (rec : r t) -> IsClosed (xCarrier rec) (xOperation rec)

public export
xMagma : XMagma r => r t -> Magma t
xMagma r = MkMagma (xCarrier r) (xOperation r) (xIsClosed r)

public export
XMagma Magma where
    xCarrier   = carrierSet
    xOperation = magmaOp
    xIsClosed  = isClosed


public export
record SubMagma (t : Type) where
    constructor MkSubMagma
    superMagma : Magma t
    subset     : Set t
    isSubset   : IsSubset subset (carrierSet superMagma)
    isClosed   : IsClosed subset (magmaOp superMagma)

public export
XMagma SubMagma where
    xCarrier     = subset
    xOperation m = let super = superMagma m in magmaOp super
    xIsClosed    = isClosed
