module Lists

import Control.Pipeline

%language LinearTypes

%default total

data LList : a -> Type where
    Nil : LList a
    (::) : (1 x : a) -> (1 l : LList a) -> LList a
  
(++) : (1 xs : LList a) -> (1 ys : LList a) -> LList a
(++) [] ys = ys
(++) (x :: xs) ys = x :: (xs ++ ys)

DList : Type -> Type
DList t = (1 x : LList t) -> LList t

z1 : DList Int
z1 x = x

z2 : DList Int
z2 x = 5 :: 9 :: 12 :: x

Semigroup (DList a) where
  (<+>) = (.)

Monoid (DList a) where
  neutral = id

infixr 5 :+
(:+) : DList a -> a -> DList a
(:+) dl x = \hole => dl (x :: hole)

fro : LList a -> DList a
fro l = \hole => l ++ hole

to : DList a -> LList a
to x = x Nil  

-- Dutch National Flag Problem
-- a generalization of what happens in a Quicksort partition step

-- You have a list of red, white, and blue tagged numbers. You want to stably sort these to put red first, white second, and blue third.
-- The catch is that you can't use append, because you're only allowed to iterate over the initial unpartitioned list, and you're only allowed to iterate over that list one time. 

data ColoredInt : Type where
 Red : (1 i : Int) -> ColoredInt
 White: (1 i : Int) -> ColoredInt
 Blue: (1 i : Int) -> ColoredInt

dutch0 : (reds : DList ColoredInt) -> (whites : DList ColoredInt) -> (blues : DList ColoredInt) -> (xs : LList ColoredInt) -> Lazy $ LList ColoredInt
dutch0 reds whites blues [] = to (reds <+> whites <+> blues)
dutch0 reds whites blues (x@(Red   _) :: xs) = dutch0 (reds :+ x) whites blues xs
dutch0 reds whites blues (x@(White _) :: xs) = dutch0 reds (whites :+ x) blues xs
dutch0 reds whites blues (x@(Blue  _) :: xs) = dutch0 reds whites (blues :+ x) xs

dutch : LList ColoredInt -> LList ColoredInt
dutch xs = dutch0 neutral neutral neutral xs

testDutch : LList ColoredInt
testDutch = dutch $ [White 4, Blue 6, Red 1, White 5, Blue 7, Red 2, Red 3, Blue 8]
-- [Red 1, Red 2, Red 3, White 4, White 5, Blue 6, Blue 7, Blue 8] : LList ColoredInt

-- difference queues

DQueue : Type -> Type 
DQueue = DList

new : DQueue t
new = neutral

push : (x : t) -> DQueue t -> DQueue t
push x q = q :+ x

data QMaybe : Type -> Type where
  QNothing : QMaybe t
  QJust : (1 x : t) -> (1 q : DQueue t) -> QMaybe t

pop : DQueue t -> QMaybe t
pop q with (to q)
  | [] = QNothing
  | (x :: l) = QJust x (fro l)

partial
getq : QMaybe t -> DQueue t
getq (QJust _ q) = q

toMaybe : QMaybe t -> Maybe t
toMaybe QNothing = Nothing
toMaybe (QJust x _) = Just x

partial
testQueue : Maybe Int
testQueue = new {t=Int}
         |> push 3 
         |> pop |> getq
         |> push 8 
         |> push 9
         |> push 12 
         |> pop |> toMaybe