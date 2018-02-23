module ConcIO.Res

%access public export 

infix 5 @@

data Res : (a : Type) -> (a -> Type) -> Type where
  (@@) : (val : a) -> k val -> Res a k

IntOrString : Type
IntOrString = Res Bool $ \ok => if ok then Int else String