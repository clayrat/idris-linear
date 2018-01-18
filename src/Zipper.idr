module Zipper

import Lists
import Vects

%language LinearTypes
%default total

-- http://requestforlogic.blogspot.com/2011/08/holey-data-part-33-type-of-one-hole.html

-- TODO https://michaeldadams.org/papers/scrap_your_zippers/

data Employee : Type where
  E : (1 name : String) -> (1 salary : Int) -> Employee

data Dept : Type where
  D : (1 boss : Employee) -> (1 subs : LList Employee) -> Dept

data DeptZipper : Type -> Type where
  MkDZ : (1 z : ((1 x : t) -> Dept)) -> t -> DeptZipper t
    
dept : Dept
dept = D (E "Agamemnon" 5000) [E "Menelaus" 3000, E "Achilles" 2000, E "Odysseus" 2000]

dzip : DeptZipper Dept
dzip = MkDZ id dept

ezip : DeptZipper Employee
ezip =
  let 
    MkDZ f d = dzip 
    D boss subord = d
    in
  MkDZ (\h => f (D h subord)) boss

nzip : DeptZipper String
nzip =
  let 
    MkDZ f e = ezip
    (E name salary) = e
    in
  MkDZ (\h => f (E h salary)) name

rev : Dept
rev = 
  let MkDZ f n = nzip in
   f "King Agamemnon"

-- polymorphic   

data Zipper : (Type -> Type) -> Type -> Type where
  MkZipper : ((1 x : a) -> f a) -> a -> Zipper f a

to : Zipper f a -> f a
to (MkZipper f x) = f x

-- there's no linear `let` :(
listZipper : (xs : LList a) -> (m : Nat) -> Zipper LList a
listZipper xs m = 
  MkZipper (\e => ((take m xs) ++ e :: (tail $ drop m xs))) 
           (head $ drop m xs)

-- no let + rewrite messes things up
{-
vectZipper :(xs : LVect (S n) a) -> (m : Nat) -> S n = m + S p -> Zipper (LVect (S n)) a
vectZipper {a} {p} xs m prf = 
  let (l, cr) = splitAt {m=S p} m (rewrite sym prf in xs)
      (c :: r) = cr
   in
  MkZipper (\e => rewrite prf in l ++ e :: r) c
-}