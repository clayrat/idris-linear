module Streams

import Lists

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
    (::) : (1 x : a) -> (1 s : N (Sink a)) -> Source a
 
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

flipSnk0 : ((1 t : Snk0 a) -> Snk0 b) -> (1 s : Src b) -> Src a
flipSnk0 _ s  Full    = s Full 
flipSnk0 f s (Cont k) = s $ Cont $ f k

total
flipSrc : (1 f : (1 t : Src a) -> Src b) -> (1 s : Snk b) -> Snk a
flipSrc f snk src = snk (f src)

mutual 
  mapSnk0 : ((1 x : b) -> a) -> (1 y : Snk0 a) -> Snk0 b
  mapSnk0 _ snk  []      = snk []
  mapSnk0 f snk (a :: s) = snk $ f a :: mapSrc f s
  
  mapSrc : ((1 x : a) -> b) -> (1 y : Src a) -> Src b
  mapSrc f = flipSnk0 (mapSnk0 f)

mapSnk : ((1 x : b) -> a) -> (1 y : Snk a) -> Snk b
mapSnk f = flipSrc (mapSrc f)

nnIntro : (1 x : Src a) -> Src (NN a)
nnIntro = mapSrc shift

nnElim0 : (1 x : Snk (NN a)) -> Snk a
nnElim0 = mapSnk shift

mutual 
  nnElim : (1 x : Src (NN a)) -> Src a
  nnElim = flipSnk0 nnIntro0

  nnIntro0 : (1 x : Snk0 a) -> Snk0 (NN a)
  nnIntro0 k []        = k []
  nnIntro0 k (x :: xs) = x $ \x0 => k (x0 :: nnElim xs)

-- effect-free  

empty : Src a   
empty  Full    = mempty
empty (Cont k) = k []

cons : a -> (1 y : Src a) -> Src a
cons x s s0 = yield x s0 s

-- TODO Int -> Nat here and on?
mutual 
  takeSrc : Int -> (1 x : Src a) -> Src a
  takeSrc 0 s t = s Full `mappend` empty t
  takeSrc i s t = flipSnk0 (takeSnk0 i) s t

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

mutual
  forwardThenSrc : (1 t2 : Snk a) -> (1 s : Src a) -> Src a
  forwardThenSrc t2 s Full = t2 s
  forwardThenSrc t2 s (Cont t1) = s $ Cont $ appendSnk0 t1 t2

  appendSnk0 : (1 t1 : Snk0 a) -> (1 t2 : Snk a) -> Snk0 a
  appendSnk0 t1 t2 [] = t1 Nil `mappend` t2 empty
  appendSnk0 t1 t2 (a :: s) = t1 (a :: forwardThenSrc t2 s)

appendSnk : (1 t1 : Snk a) -> (1 t2 : Snk a) -> Snk a
appendSnk t1 t2 s = t1 (forwardThenSrc t2 s)

LMonoid (Snk a) where
  mappend = appendSnk
  mempty = shift Full

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

-- TODO can't be defined - linear `next` is passed as non-linear `scanSrc.b` 
--mutual 
--  scanSrc : (b -> (1 x : a) -> (b, c)) -> b -> (1 s : Src a) -> Src c
--  scanSrc f z = flipSnk0 (scanSnk0 f z)
--
--  scanSnk0 : (b -> (1 x : a) -> (b, c)) -> b -> (1 t : Snk0 c) -> Snk0 a
--  scanSnk0 _ _ snk []        = snk []
--  scanSnk0 f z snk (a :: s)  = scanSnk0Aux f snk (f z a) s
--    
--  scanSnk0Aux : (b -> (1 x : a) -> (b, c)) -> (1 t : Snk0 c) -> (1 bc : (b, c)) -> Snk a
--  scanSnk0Aux f snk (next, y) s = snk $ y :: scanSrc f next s
--
--scanSnk : (b -> (1 x : a) -> (b, c)) -> b -> (1 s : Snk c) -> Snk a
--scanSnk f z = flipSrc (scanSrc f z)

-- TODO this asymmetry in parameter linearity here looks weird
mutual 
  foldSrc0 : ((y : b) -> (1 x : a) -> b) -> (1 z : b) -> (1 s : Src a) -> NN b
  foldSrc0 f z s nb = s (Cont (foldSnk1 f z nb))
  
  foldSnk1 : ((1 y : b) -> (1 x : a) -> b) -> (1 z : b) -> (1 nb : N b) -> Snk0 a
  foldSnk1 _ z nb []       = nb z
  foldSnk1 f z nb (a :: s) = foldSrc0 f (f z a) s nb

foldSnk0 : ((y : b) -> (1 x : a) -> b) -> b -> (1 s : N b) -> Snk a
foldSnk0 f z nb src = foldSrc0 f z src nb

mutual 
  dropSrc : Drop a => Int -> (1 s : Src a) -> Src a
  dropSrc i = flipSnk0 (dropSnk0 i)
  
  dropSnk0 : Drop a => Int -> (1 s : Snk0 a) -> Snk0 a
  dropSnk0 0 s s0 = s s0
  dropSnk0 _ s [] = s []
  dropSnk0 i s (x :: s0) = drop x (dropSrc (i-1) s0 (Cont s))

dropSnk : Drop a => Int -> (1 s : Snk a) -> Snk a
dropSnk i = flipSrc (dropSrc i)

fromList : (1 l : List a) -> Src a
fromList = foldr cons empty

mutual
  toList : (1 s : Src a) -> NN (LList a)
  toList s k = s (Cont $ toListSnk0 k)

-- TODO changed arg to linear and the returned structure to `LList`, otherwise we are not allowed to prepend the linear `x`  
  toListSnk0 : (1 k : N (LList a)) -> Snk0 a
  toListSnk0 k [] = k []
  toListSnk0 k (x :: xs) = toList xs $ \xs0 => k (x :: xs0)

-- TODO these shouldn't work! eta-contraction seems to bypass rig checker
reverse0 : (1 s : String) -> String
reverse0 = prim__strRev
strCons0 : (1 c : Char) -> (1 s : String) -> String
strCons0 = prim__strCons

-- TODO we need linear `strCons` and `reverse` for this to work ^^
mutual   
  unlinesSnk0 : (1 acc : String) -> Snk0 String -> Snk0 Char
  unlinesSnk0 acc s [] = s (acc :: empty)
  unlinesSnk0 acc s ('\n' :: s0) = s (reverse0 acc :: linesSrc s0)
  unlinesSnk0 acc s (c :: s0) = s0 (Cont $ unlinesSnk0 (strCons0 c acc) s)

  unlinesSnk1 : Snk0 String -> Snk0 Char
  unlinesSnk1 = unlinesSnk0 ""
  
  linesSrc : (1 s : Src Char) -> Src String
  linesSrc = flipSnk0 unlinesSnk1

unlinesSnk : (1 s : Snk String) -> Snk Char  
unlinesSnk = flipSrc linesSrc 

mutual
  collapseSnk0 : ((1 x : a) -> (b, c)) -> (1 t1 : Snk0 b) -> (1 t2 : Snk0 c) -> Snk0 a
  collapseSnk0 _    t1 t2 [] = t1 [] `mappend` t2 []
  collapseSnk0 dup  t1 t2 (x :: xs) = collapseSnk0Aux dup t1 t2 (dup x) xs -- TODO linear destructuring `let`s ?

  collapseSnk0Aux : ((1 x : a) -> (b, c)) -> (1 t1 : Snk0 b) -> (1 t2 : Snk0 c) -> (1 bc : (b, c)) -> Snk a
  collapseSnk0Aux dup t1 t2 (y, z) xs = t1 (y :: (\c1 => t2 (z :: tee0 dup xs c1)))

  -- TODO made `Src a` and `Sink b` linear
  tee0 : ((1 x : a) -> (b, c)) -> (1 s1 : Src a) -> (1 t1 : Sink b) -> Src c
  tee0 deal s1 t1         Full     = s1 Full `mappend` empty t1
  tee0 deal s1  Full     t2        = s1 Full `mappend` empty t2
  tee0 deal s1 (Cont t1) (Cont t2) = s1 $ Cont $ collapseSnk0 deal t1 t2

tee : ((1 x : a) -> (b, c)) -> (1 s : Src a) -> (1 t1 : Snk b) -> Src c
tee f s t1 t2 = t1 $ \t => tee0 f s t t2

collapseSnk : ((1 x : a) -> (b, c)) -> (1 t1 : Snk b) -> (1 t2 : Snk c) -> Snk a
collapseSnk f t1 t2 s = t2 (tee f s t1)

