module ConcIO.Door0

%default total

data DoorState = Opened | Closed

data DoorH : DoorState -> Type where
  MkDH : (s : DoorState) -> DoorH s

data DoorCmd : Type -> Type where
  Open  : DoorH Closed -> DoorCmd (DoorH Opened)
  Knock : DoorH Closed -> DoorCmd ()
  Close : DoorH Opened -> DoorCmd (DoorH Closed)

data DoorLang : Type -> Type where
  Pure   : a -> DoorLang a
  Action : DoorCmd a -> DoorLang a
  (>>=)  : DoorLang a -> (a -> DoorLang b) -> DoorLang b

doorOK : DoorH Closed -> DoorLang ()
doorOK h = do Action (Knock h)
              h <- Action (Open h)
              h <- Action (Close h)
              Pure ()

doorBad : DoorH Closed -> DoorLang ()
doorBad h = do Action (Knock h)
               hbad <- Action (Open h)
               h <- Action (Close hbad)
               h <- Action (Close hbad)
               Pure ()

