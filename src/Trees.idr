module Trees

%language LinearTypes
%default total

data Tree0 : Type where
  Leaf0 : Tree0
  Node0 : (1 l : Tree0) -> (1 r : Tree0) -> Tree0

data Path : Type where
    Top : Path
    Left : (1 p : Path) -> (1 r : Tree0) -> Path
    Right : (1 l : Tree0) -> (1 p : Path) -> Path
  
enlin : Path -> (1 t : Tree0) -> Tree0 
enlin Top = \t => t
enlin (Left p r) = \t => enlin p (Node0 t r)
enlin (Right l p) = \t => enlin p (Node0 l t)

data Tree : Type -> Type where
  Leaf : Tree a
  Node : (x : a) -> (1 l : Tree a) -> (1 r : Tree a) -> Tree a

DTree : Type -> Type
DTree a = (1 x : Tree a) -> Tree a

empty : DTree a
empty = \t => t

binsert : Ord t => Tree t -> t -> Tree t
binsert Leaf y = Node y Leaf Leaf
binsert (Node x l r) y = 
  if y < x 
    then Node x (binsert l y) r
    else if x < y 
      then Node x l (binsert r y)
      else Node x l r

hfunBinsert : Ord a => Tree a -> a -> Tree a
hfunBinsert t y = binsert1 t y empty
  where
  binsert1 : Tree a -> a -> DTree a -> Tree a
  binsert1 Leaf y k = k (Node y Leaf Leaf) 
  binsert1 (Node x l r) y k = 
    if y < x 
      then binsert1 l y (\t => k (Node x t r))
      else if x < y
        then binsert1 r y (\t => k (Node x l t))
        else k (Node x l r) 

addone : Num a => Tree a -> Tree a
addone  Leaf        = Leaf
addone (Node x l r) = Node (x+1) (addone l) (addone r)

hfunAddone : Num a => Tree a -> Tree a
hfunAddone  Leaf        = Leaf
hfunAddone (Node x l r) = addone1 r (\t => Node (x+1) (hfunAddone l) t)
  where
  addone1 : Tree a -> DTree a -> Tree a
  addone1  Leaf k        = k Leaf
  addone1 (Node x l r) k = addone1 r (\t => Node (x+1) (hfunAddone l) t)
