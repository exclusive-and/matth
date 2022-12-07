
module Convolution

import Prelude.List


||| Convenience function for performing a 'zipWith', but without
||| truncating at the shortest list.
public export
openZipWith : (a -> c)
           -> (b -> c)
           -> (a -> b -> c)
           -> List a -> List b -> List c

openZipWith f1 f2 f xs Nil = map f1 xs
openZipWith f1 f2 f Nil ys = map f2 ys

openZipWith f1 f2 f (x :: xs) (y :: ys) =
    (f x y) :: openZipWith f1 f2 f xs ys

||| Convolutions, done using products of polynomials.
|||
||| (a + x * A) * (b + x * B)
|||     = a * b + x * (a * B + b * A + x * (A * B))
|||
||| Note: in the representation of polynomials as lists, x * k == Nil :: k
public export
convolveWith : {a, b, c : Type}
            -> (a -> b -> c)
            -> List a -> List b -> List (List c)

convolveWith f Nil _ = Nil
convolveWith f _ Nil = Nil

convolveWith {a} {b} {c} f (x :: xs) (y :: ys) =
  let
    z  = go1 x y
    zs = comb (goR x ys) $ comb (Nil :: convolveWith f xs ys) $ goL xs y
  in
    z :: zs
  where
    comb : List (List c) -> List (List c) -> List (List c)
    comb = openZipWith id id (++)

    go1 : a -> b -> List c
    go1 x y = f x y :: Nil

    goL : List a -> b -> List (List c)
    goL xs y = map (\x => go1 x y) xs

    goR : a -> List b -> List (List c)
    goR x ys = map (\y => go1 x y) ys
