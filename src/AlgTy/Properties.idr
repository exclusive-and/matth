
module AlgTy.Properties

import Theory.AxiomJ
import Theory.Sets

%hide Prelude.Algebra.Monoid
%hide Prelude.Algebra.Semigroup
%hide Prelude.Nat.Nat
%hide Prelude.Nat.plus
%hide Prelude.Nat.mult


public export
IsAssociative : {a : Type} -> (m : a -> a -> a) -> Type
IsAssociative {a} m = (x, y, z : a) -> Id (m x (m y z)) (m (m x y) z)

public export
IsCommutative : {a : Type} -> (m : a -> a -> a) -> Type
IsCommutative {a} m = (x, y : a) -> Id (m x y) (m y x)

public export
HasIdentity : {a : Type} -> (e : a) -> (m : a -> a -> a) -> Type
HasIdentity {a} e m = (x : a) -> Id (m e x) x

public export
IsInvertible : {a : Type}
            -> (e : a)
            -> (m : a -> a -> a)
            -> (inv : a -> a)
            -> Type
IsInvertible {a} e m inv = (x : a) -> Id e (m (inv x) x)

public export
IsDistributive : {a : Type}
              -> (m : a -> a -> a)
              -> (n : a -> a -> a)
              -> Type
IsDistributive {a} m n =
    (x, y, z : a) -> Id (m x (n y z)) (n (m x y) (m x z))

public export
IsHomomorphic : {a, b : Type}
             -> (m : a -> a -> a)
             -> (n : b -> b -> b)
             -> (f : a -> b)
             -> Type
IsHomomorphic {a} {b} m n f =
    (x, y : a) -> Id (f (m x y)) (n (f x) (f y))

