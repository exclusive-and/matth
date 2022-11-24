
module Algebra.Properties

import Theory.AxiomJ

%hide Prelude.Algebra.Monoid
%hide Prelude.Algebra.Semigroup


public export
isAssociative : {a : Type} -> (m : a -> a -> a) -> Type
isAssociative {a} m = (x, y, z : a) -> Id (m x (m y z)) (m (m x y) z)

public export
isCommutative : {a : Type} -> (m : a -> a -> a) -> Type
isCommutative {a} m = (x, y : a) -> Id (m x y) (m y x)

public export
hasIdentity : {a : Type} -> (e : a) -> (m : a -> a -> a) -> Type
hasIdentity {a} e m = (x : a) -> Id (m e x) x

public export
isInvertible : {a : Type}
            -> (e : a)
            -> (m : a -> a -> a)
            -> (inv : a -> a)
            -> Type
isInvertible {a} e m inv = (x : a) -> Id e (m (inv x) x)

public export
isHomomorphic : {a, b : Type}
             -> (m : a -> a -> a)
             -> (n : b -> b -> b)
             -> (f : a -> b)
             -> Type
isHomomorphic {a} {b} m n f =
    (x, y : a) -> Id (f (m x y)) (n (f x) (f y))

