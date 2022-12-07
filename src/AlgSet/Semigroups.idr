
module AlgSet.Semigroups

import Theory.AxiomJ
import Theory.Sets
import AlgSet.Magma

%hide Prelude.Algebra.Semigroup


public export
IsAssociative : {t : Type} -> (t -> t -> t) -> Type
IsAssociative {t} m = (x : t)
                   -> (y : t)
                   -> (z : t)
                   -> Id (m x (m y z)) (m (m x y) z)

public export
record Semigroup (t : Type) where
    constructor MkSemigroup
    carrierSet      : Set t
    semigroupOp     : t -> t -> t
    isClosed        : IsClosed carrierSet semigroupOp
    isAssociative   : IsAssociative semigroupOp

public export
interface XMagma r => XSemigroup (r : Type -> Type) where
    xIsAssociative  : (rec : r t) -> IsAssociative (xOperation rec)

public export
xSemigroup : XSemigroup r => r t -> Semigroup t
xSemigroup r =
    MkSemigroup
        (xCarrier r) (xOperation r) (xIsClosed r) -- Magma laws
        (xIsAssociative r)                        -- Semigroup laws

public export
XMagma Semigroup where
    xCarrier   = carrierSet
    xOperation = semigroupOp
    xIsClosed  = isClosed

public export
XSemigroup Semigroup where
    xIsAssociative = isAssociative


public export
record SubSemigroup (t : Type) where
    constructor MkSubMagma
    superSemigroup : Semigroup t
    subset         : Set t
    isSubset       : IsSubset subset (carrierSet superSemigroup)
    isClosed       : IsClosed subset (semigroupOp superSemigroup)

public export
XMagma SubSemigroup where
    xCarrier     = subset
    xOperation m = let super = superSemigroup m in semigroupOp super
    xIsClosed    = isClosed

public export
XSemigroup SubSemigroup where
    xIsAssociative m =
      let
        super = superSemigroup m
      in
        isAssociative super

