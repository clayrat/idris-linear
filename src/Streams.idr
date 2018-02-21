module Streams

%language LinearTypes
%default total

data Eff = MkEff (IO ())

--interface LMonoid ty where
--  mappend : (1 x : ty) -> (1 y : ty) -> ty
--  mempty : ty
--  
--LMonoid Eff where

N : Type -> Type
N a = (1 x : a) -> Eff

NN : Type -> Type
NN = N . N

shift : (1 x : a) -> NN a
shift x k = k x

unshift : (1 x : N (NN a)) -> N a
unshift k x = k $ shift x

-- TODO not strictly positive, so most stuff is partial from here on
-- TODO Inf ?
mutual 
  data Source : Type -> Type where
    Nil : Source a
    (::) : (1 x : a) -> (1 y : N (Sink a)) -> Source a
 
  data Sink : Type -> Type where
    Full : Sink a
    Cont : (1 x : N (Source a)) -> Sink a

infixr 5 &    
(&) : Type -> Type -> Type
(&) a b = N (Either (N a) (N b))    

partial
await : (1 x : Source a) -> (1 y : Eff & ((1 t : a) -> (1 s : Source a) -> Eff)) -> Eff
await []        r = r $ Left id
await (x :: xs) r = r $ Right $ \c => xs (Cont (c x))

partial
yield : a -> (1 y : Sink a) -> NN (Sink a)
yield x (Cont c) k = c (x :: k)
yield _  Full    k = k Full

Src : Type -> Type
Src = N . Sink

Snk : Type -> Type
Snk = N . Src

fwd : (1 x : Src a) -> N (Snk a)
fwd = shift

Snk0 : Type -> Type
Snk0 = N . Source

partial
flipSnk : ((1 t : Snk0 a) -> Snk0 b) -> (1 s : Src b) -> Src a
flipSnk _ s  Full    = s Full
flipSnk f s (Cont k) = s $ Cont $ f k

flipSrc : ((1 t : Src a) -> Src b) -> (1 s : Snk b) -> Snk a
flipSrc f snk src = snk (f src)

mutual 
  partial
  mapSnk0 : ((1 x : b) -> a) -> (1 y : Snk0 a) -> Snk0 b
  mapSnk0 _ snk  []      = snk []
  mapSnk0 f snk (a :: s) = snk $ f a :: mapSrc f s
  
  partial
  mapSrc : ((1 x : a) -> b) -> (1 y : Src a) -> Src b
  mapSrc f = flipSnk (mapSnk0 f)

partial
mapSnk : ((1 x : b) -> a) -> (1 y : Snk a) -> Snk b
mapSnk f = flipSrc (mapSrc f)

partial
nnIntro : (1 x : Src a) -> Src (NN a)
nnIntro = mapSrc shift

partial
nnElim0 : (1 x : Snk (NN a)) -> Snk a
nnElim0 = mapSnk shift

mutual 
  partial
  nnElim : (1 x : Src (NN a)) -> Src a
  nnElim = flipSnk nnIntro0

  partial
  nnIntro0 : (1 x : Snk0 a) -> Snk0 (NN a)
  nnIntro0 k []        = k []
  nnIntro0 k (x :: xs) = x $ \x0 => k (x0 :: nnElim xs)