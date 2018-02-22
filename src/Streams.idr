module Streams

%language LinearTypes
%default partial

data Eff = MkEff (IO ())

interface LMonoid t where
  mappend : (1 x : t) -> (1 y : t) -> t
  mempty : t
  
LMonoid Eff where
  mappend (MkEff x) (MkEff y) = MkEff (x *> y)
  mempty = MkEff $ pure ()

total  
N : Type -> Type
N a = (1 x : a) -> Eff

total
NN : Type -> Type
NN = N . N

total
shift : (1 x : a) -> NN a
shift x k = k x

total
unshift : (1 x : N (NN a)) -> N a
unshift k x = k $ shift x

-- TODO not strictly positive, hence most of the stuff is partial in here
mutual 
  data Source : Type -> Type where
    Nil : Source a
    (::) : (1 x : a) -> (1 y : N (Sink a)) -> Source a
 
  data Sink : Type -> Type where
    Full : Sink a
    Cont : (1 x : N (Source a)) -> Sink a

infixr 5 &    
total
(&) : Type -> Type -> Type
(&) a b = N (Either (N a) (N b))    

await : (1 x : Source a) -> (1 y : Eff & ((1 t : a) -> (1 s : Source a) -> Eff)) -> Eff
await []        r = r $ Left id
await (x :: xs) r = r $ Right $ \c => xs (Cont (c x))

yield : a -> (1 y : Sink a) -> NN (Sink a)
yield x (Cont c) k = c (x :: k)
yield _  Full    k = k Full

total
Src : Type -> Type
Src = N . Sink

total
Snk : Type -> Type
Snk = NN . Sink

total
fwd : (1 x : Src a) -> N (Snk a)
fwd = shift

total
Snk0 : Type -> Type
Snk0 = N . Source

flipSnk : ((1 t : Snk0 a) -> Snk0 b) -> (1 s : Src b) -> Src a
flipSnk _ s  Full    = s Full
flipSnk f s (Cont k) = s $ Cont $ f k

total
flipSrc : ((1 t : Src a) -> Src b) -> (1 s : Snk b) -> Snk a
flipSrc f snk src = snk (f src)

mutual 
  mapSnk0 : ((1 x : b) -> a) -> (1 y : Snk0 a) -> Snk0 b
  mapSnk0 _ snk  []      = snk []
  mapSnk0 f snk (a :: s) = snk $ f a :: mapSrc f s
  
  mapSrc : ((1 x : a) -> b) -> (1 y : Src a) -> Src b
  mapSrc f = flipSnk (mapSnk0 f)

mapSnk : ((1 x : b) -> a) -> (1 y : Snk a) -> Snk b
mapSnk f = flipSrc (mapSrc f)

nnIntro : (1 x : Src a) -> Src (NN a)
nnIntro = mapSrc shift

nnElim0 : (1 x : Snk (NN a)) -> Snk a
nnElim0 = mapSnk shift

mutual 
  nnElim : (1 x : Src (NN a)) -> Src a
  nnElim = flipSnk nnIntro0

  nnIntro0 : (1 x : Snk0 a) -> Snk0 (NN a)
  nnIntro0 k []        = k []
  nnIntro0 k (x :: xs) = x $ \x0 => k (x0 :: nnElim xs)

-- effect-free  

empty : Src a   
empty  Full    = mempty
empty (Cont k) = k []

-- in the paper `a` is linear but this seems wrong
cons : a -> (1 y : Src a) -> Src a
cons x s s0 = yield x s0 s

mutual 
  takeSrc : Int -> (1 x : Src a) -> Src a
  takeSrc 0 s t = s Full `mappend` empty t
  takeSrc i s t = flipSnk (takeSnk0 i) s t

  takeSnk0 : Int -> (1 x : Snk0 a) -> Snk0 a
  takeSnk0 _ s  []       = s []
  takeSnk0 i s (a :: s0) = s $ a :: (takeSrc (i - 1) s0)

takeSnk : Int -> (1 x : Snk a) -> Snk a
takeSnk n = flipSrc (takeSrc n)

mutual
  appendSrc : (1 x : Src a) -> (1 y : Src a) -> Src a
  appendSrc s1 s2  Full    = s1 Full `mappend` s2 Full
  appendSrc s1 s2 (Cont s) = s1 (Cont (forwardThenSnk0 s s2))
  
  forwardThenSnk0 : (1 x : Snk0 a) -> (1 y : Src a) -> Snk0 a
  forwardThenSnk0 snk0 src [] = src (Cont snk0)
  forwardThenSnk0 snk0 src (a :: s) = snk0 (a :: (appendSrc s src))

-- `s2` is linear in the paper but this doesn't work out for `forwardThenSrc`
-- as in `cons` above, the result of `appendSnk0 s2` is then linear, but gets passed as a non-linear argument of `flipSnk`
mutual 
  appendSnk0 : (1 s1 : Snk0 a) -> (s2 : Snk0 a) -> Snk0 a
  appendSnk0 s1 s2 [] = s1 [] `mappend` s2 []
  appendSnk0 s1 s2 (a :: s) = s1 (a :: (forwardThenSrc s2 s))
  
  forwardThenSrc : (s2 : Snk0 a) -> (1 s : Src a) -> Src a
  forwardThenSrc s2 = flipSnk (appendSnk0 s2)

-- this is no longer definable due to `forwardThenSrc` not being linear in first argument   
--appendSnk : (1 t1 : Snk a) -> (1 t2 : Snk a) -> Snk a
--appendSnk t1 t2 s = t1 $ \x => case x of 
--                                 Full   => t2 empty `mappend` s Full
--                                 Cont k => flipSrc (forwardThenSrc k) t2 s
--
--LMonoid (Snk a) where
--  mappend = appendSnk
--  mempty = shift Full

LMonoid (Src a) where
  mappend = appendSrc
  mempty = empty

interface Drop a where 
  drop : (1 x : a) -> (1 y : b) -> b

mutual   
  zipSource : (Drop a, Drop b) => (1 s1 : Source a) -> (1 s2 : Source b) -> NN (Source (a,b))
  zipSource []        []        t = t []
  zipSource []        (x :: xs) t = drop x (xs Full `mappend` t [])
  zipSource (x :: xs) []        t = drop x (xs Full `mappend` t [])
  zipSource (x :: xs) (y :: ys) t = t ((x,y) :: zipSrc xs ys)
  
  zipSrc : (Drop a, Drop b) => (1 s1 : Src a) -> (1 s2 : Src b) -> Src (a, b)
  zipSrc s1 s2  Full    = s1 Full `mappend` s2 Full
  zipSrc s1 s2 (Cont k) = s1 $ Cont $ \sa => 
                          s2 $ Cont $ \sb => zipSource sa sb k

forkSnk : (Drop a, Drop b) => (1 t : Snk (a, b)) -> (1 s1 : Src a) -> Snk b
forkSnk t s1 s2 = t (zipSrc s1 s2)

forkSnk0 : (Drop a, Drop b) => (1 t : Snk0 (a, b)) -> (1 s1 : Src a) -> Snk0 b
forkSnk0 sab ta tb = ta $ Cont $ \ta0 => zipSource ta0 tb sab

mutual
  forkSource : (1 s : Source (a,b)) -> (1 t1 : N (Source a)) -> (1 t2 : N (Source b)) -> Eff
  forkSource []            t1 t2 = t1 [] `mappend` t2 []
  forkSource ((a,b) :: xs) t1 t2 = t1 $ a :: (\sa0 => t2 $ b :: (\sb0 => forkSrc0 xs sa0 sb0))
  
  forkSrc0 : (1 sab : Src (a, b)) -> (1 ta : Sink a) -> Src b
  forkSrc0 sab  Full     tb        = empty tb `mappend` sab Full
  forkSrc0 sab ta         Full     = empty ta `mappend` sab Full
  forkSrc0 sab (Cont ta) (Cont tb) = sab $ Cont $ \sab0 => forkSource sab0 ta tb

zipSnk0 : (1 ta : Snk0 a) -> (1 tb : Snk0 b) -> Snk0 (a, b)
zipSnk0 ta tb sab = forkSource sab ta tb

zipSnk : (1 ta : Snk a) -> (1 tb : Snk b) -> Snk (a, b)
zipSnk a b c = a $ \a0 => b $ \b0 => zipSnk (shift a0) (shift b0) c

forkSrc : (1 sab : Src (a, b)) -> (1 ta : Snk a) -> Src b
forkSrc sab ta tb = ta $ \x => forkSrc0 sab x tb

-- TODO this is currently impossible to define in Idris since you can't do linear destructuring `let`s
--mutual
--  collapseSnk0 : ((1 x : a) -> (b, c)) -> (1 t1 : Snk0 b) -> (1 t2 : Snk0 c) -> Snk0 a
--  collapseSnk0 _    t1 t2 [] = t1 [] `mappend` t2 []
--  collapseSnk0 dup  t1 t2 (x :: xs) = let 1 (y, z) = dup x in t1 (y :: (\c1 => t2 (z :: tee0 dup xs c1)))
--  
--  tee0 : ((1 x : a) -> (b, c)) -> Src a -> Sink b -> Src c
--  tee0 deal s1 t1 Full = s1 Full `mappend` empty t1
--  tee0 deal s1 Full t2 = s1 Full `mappend` empty t2
--  tee0 deal s1 (Cont t1) (Cont t2) = s1 $ Cont $ collapseSnk0 deal t1 t2
--
-- again, `s` can't be linear here
--tee : ((1 x :a) -> (b, c)) -> (1 s : Src a) -> (1 t1 : Snk b) -> Src c
--tee f s t1 t2 = t1 $ \t => tee0 f s t t2
