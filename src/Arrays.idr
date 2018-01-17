module Lists

%language LinearTypes
%default total

data MArray a = MkMArray
data Array a = MKArray

newMArray : Int -> (1 mab : (1 ma : MArray a) -> b) -> b

write : (1 ma : MArray a) -> (Int, a) -> MArray a

read : (1 ma : MArray a) -> Int -> (MArray a,a)

freeze : (1 ma : MArray a) -> Array a

lfoldl : ((1 x : a) -> (1 y : b) -> a) -> (1 x : a) -> (1 ys : List b) -> a    
lfoldl _ q []      = q
lfoldl f q (x::xs) = lfoldl f (f q x) xs

array : Int -> List (Int, a) -> Array a
array size pairs = newMArray size (\ma => freeze (lfoldl write ma pairs))