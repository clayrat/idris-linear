module Vects

%language LinearTypes
%default total
%access public export

data LVect : (len : Nat) -> (elem : Type) -> Type where
  ||| Empty vector
  Nil  : LVect Z elem
  ||| A non-empty vector of length `S len`, consisting of a head element and
  ||| the rest of the list, of length `len`.
  (::) : (1 x : elem) -> (1 xs : LVect len elem) -> LVect (S len) elem

(++) : (xs : LVect m elem) -> (ys : LVect n elem) -> LVect (m + n) elem
(++) []      ys = ys
(++) (x::xs) ys = x :: xs ++ ys
    
take : (n : Nat) -> LVect (n + m) elem -> LVect n elem
take Z     xs        = []
take (S k) (x :: xs) = x :: take k xs

drop : (n : Nat) -> LVect (n + m) elem -> LVect m elem
drop Z     xs        = xs
drop (S k) (x :: xs) = drop k xs
  
splitAt : (n : Nat) -> (xs : LVect (n + m) elem) -> (LVect n elem, LVect m elem)
splitAt n xs = (take n xs, drop n xs)
