module ConcIO.Door2

import ConcIO.Res

%language LinearTypes
%default total

data DoorState = Opened | Closed

data DoorH : DoorState -> Type where
  MkDH : (s : DoorState) -> DoorH s

data DoorCmd : Type -> Type where
  Open  : (1 d : DoorH Closed) -> DoorCmd (Res Bool $ \ok => if ok then DoorH Opened else DoorH Closed)
  Knock : (1 d : DoorH Closed) -> DoorCmd (DoorH Closed)
  Close : (1 d : DoorH Opened) -> DoorCmd (DoorH Closed)

data DoorLang : Type -> Type where
  Pure   : (1 x : a) -> DoorLang a
  Action : (1 c : DoorCmd a) -> DoorLang a
  (>>=)  : (1 l : DoorLang a) -> ((1 x : a) -> DoorLang b) -> DoorLang b

doorOK : (h : DoorH Closed) -> DoorLang (DoorH Closed)
doorOK h = do h <- Action (Knock h)
              (True @@ h) <- Action (Open h) | (False @@ h) => Pure h
              h <- Action (Close h)
              Pure h

-- still doesn't compile
{-
doorBad : (h : DoorH Closed) -> DoorLang (DoorH Closed)
doorBad h = do h <- Action (Knock h)
               (True @@ hbad) <- Action (Open h) | (False @@ h) => Pure h
               h <- Action (Close hbad)
               h <- Action (Close hbad)
               Pure h
-}      
