module ConcIO.Door1

%language LinearTypes
%default total

data DoorState = Opened | Closed

data DoorH : DoorState -> Type where
  MkDH : (s : DoorState) -> DoorH s

data DoorCmd : Type -> Type where
  Open  : (1 d : DoorH Closed) -> DoorCmd (DoorH Opened)
  Knock : (1 d : DoorH Closed) -> DoorCmd (DoorH Closed)
  Close : (1 d : DoorH Opened) -> DoorCmd (DoorH Closed)

data DoorLang : Type -> Type where
  Pure   : (1 x : a) -> DoorLang a
  Action : (1 c : DoorCmd a) -> DoorLang a
  (>>=)  : (1 l : DoorLang a) -> ((1 x : a) -> DoorLang b) -> DoorLang b

doorOK : (h : DoorH Closed) -> DoorLang (DoorH Closed)
doorOK h = do h <- Action (Knock h)
              h <- Action (Open h)
              h <- Action (Close h)
              Pure h

{-
-- no longer compiles, because we discard the `h` after first close
doorBad : (h : DoorH Closed) -> DoorLang (DoorH Closed)
doorBad h = do h <- Action (Knock h)
               hbad <- Action (Open h)
               h <- Action (Close hbad)
               h <- Action (Close hbad)
               Pure h

-- also doesn't compile, now because we're actually reusing `hbad`
consume : (1 d : DoorH Closed) -> DoorLang ()

doorBad2 : (h : DoorH Closed) -> DoorLang (DoorH Closed)
doorBad2 h = do h <- Action (Knock h)
                hbad <- Action (Open h)
                h <- Action (Close hbad)
                () <- consume h
                h <- Action (Close hbad)
                Pure h
-}
