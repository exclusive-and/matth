
module Theory.AxiomJ

%default total

||| Identity type.
public export
data Id : a -> a -> Type where
    Refl : Id x x


||| Axiom J.
public export
axiomJ : {a : Type}
      -> (prop : (x, y : a) -> Id x y -> Type)
      -> (base : (x : a) -> prop x x Refl)
      -> ((x, y : a) -> (p : Id x y) -> prop x y p)

axiomJ prop base x x Refl = base x


||| Transport axiom.
public export
transport : {prop : a -> Type}
         -> {x, y : a}
         -> (p : Id x y)
         -> (prop x -> prop y)

transport {prop} {x} {y} p =
    axiomJ (\u, v, q => prop u -> prop v) (\a, z => z) x y p


||| Congruence relation for functions.
public export
congruence : {f : a -> b}
          -> {x, y : a}
          -> Id x y
          -> Id (f x) (f y)

congruence {f} {x} {y} p =
    axiomJ (\x, y, p => Id (f x) (f y)) (\x => Refl) x y p


||| Symmetry of equality.
public export
symmetric : {x, y : a}
         -> Id x y
         -> Id y x
symmetric {x} {y} p =
    axiomJ (\x, y, p => Id y x) (\x => Refl) x y p


||| Composition of equality.
public export
compose : {x, y, z : a}
       -> Id x y
       -> Id y z
       -> Id x z

compose {x} {y} {z} p1 q1 =
    axiomJ xyProp xyBase x y p1 z q1
  where
    -- Prop: For some x, z where x = z, conclude x = z
    xzProp : (x, z : a) -> Id x z -> Type
    xzProp x z q = Id x z

    -- Base: From x = x, conclude x = x
    xzBase : (x : a) -> xzProp x x Refl
    xzBase x = Refl

    -- Prop: For some x, y where x = y, conclude
    --       for some z where y = z, conclude x = z
    xyProp : (x, y : a) -> Id x y -> Type
    xyProp x y p = (z : a) -> Id y z -> Id x z

    -- Base: From x = z, conclude x = z
    xyBase : (x, z : a) -> (q : Id x z) -> xzProp x z q
    xyBase x z q = axiomJ xzProp xzBase x z q


public export
eqToId : {a : Type} -> {x, y : a} -> x = y -> Id x y
eqToId Refl = Refl

public export
idToEq : {a : Type} -> {x, y : a} -> Id x y -> x = y
idToEq Refl = Refl

public export
refl : Id x x
refl = Refl
