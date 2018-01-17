module Trees

%language LinearTypes
%default total

data Tree : Type where
  Leaf : Tree
  Node : (1 l : Tree) -> (1 r : Tree) -> Tree

data Path : Type where
    Top : Path
    Left : (1 p : Path) -> (1 r : Tree) -> Path
    Right : (1 l : Tree) -> (1 p : Path) -> Path
  
enlin : Path -> (1 t : Tree) -> Tree 
enlin Top = \t => t
enlin (Left p r) = \t => enlin p (Node t r)
enlin (Right l p) = \t => enlin p (Node l t)