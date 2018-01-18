module Main 

%language LinearTypes
%default total

g1 : ((1 x : a) -> a -> r) -> (1 x : a) -> a -> r
g1 k x y = k x y

{-
g2 : ((1 x : a) -> a -> r) -> (1 x : a) -> a -> r
g2 k x y = k y x
-}

g3 : ((1 x : a) -> a -> r) -> (0 x : a) -> a -> r
g3 k x y = k y y

f : (1 x : a) -> a
f x = x

g4 : ((1 x : a) -> a -> r) -> (1 x : a) -> a -> r
g4 k x y = k x (f y)

g5 : ((1 x : a) -> a -> r) -> (1 x : a) -> a -> r
g5 k x y = k (f x) y

{-
g6 : ((1 x : a) -> a -> r) -> (1 x : a) -> a -> r
g6 k x y = k y (f x)
-}

data AEither : (a : Type) -> (b : Type) -> Type where
  ALeft : (1 x : a) -> AEither a b
  ARight : (1 y : b) -> AEither a b

MPair : (a : Type) -> (b : Type) -> Type
MPair a b = (1 ae : AEither ((1 x : a) -> IO ()) ((1 y : b) -> IO ())) -> IO ()  

lif : (1 s : Bool) -> (1 p : MPair a a) -> ((1 x : a) -> IO ()) -> IO ()
lif True  p k = p (ALeft k)
lif False p k = p (ARight k)