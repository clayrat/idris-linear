module ConcIO.Channel

import Data.List
import ConcIO.Res

%language LinearTypes
%default total

data PID = MkPID Ptr

data Actions : Type where
  DoListen : (client : proc) -> Actions -> Actions
  DoSend   : (dest : proc) -> (a : Type) -> (a -> Actions) -> Actions
  DoRecv   : (src : proc) -> (a : Type) -> (a -> Actions) -> Actions
  DoRec    : Inf Actions -> Actions
  End      : Actions

data Channel : (src : proc) -> (dest : proc) -> Actions -> Type where
  MkChan : (t : PID) -> Channel src dest a

data RChannel : (dest : proc) -> Actions -> Type where
  MkRChan : (t : PID) -> RChannel dest a
  
data Cmd : proc -> List proc -> List proc -> Type -> Type where 
  Connect : RChannel srv p -> Cmd me xs (srv :: xs) (Channel me srv p)
  Close   : Channel me srv End -> {auto prf : Elem srv xs} -> Cmd me xs (dropElem xs prf) ()
  Listen  : Channel me t (DoListen t k) -> {auto prf : Elem t xs} -> Cmd me xs xs (Res Bool $ \ok => if ok then Channel me t k 
                                                                                                           else Channel me t (DoListen t k))
  Send    : (val : a) -> Channel me t (DoSend t a k) -> Cmd me xs xs (Channel me t (k val))
  Recv    : Channel me t ( DoRecv t a k) -> Cmd me xs xs (Res a $ \v => Channel me t (k v))
  Print   : String -> Cmd me xs xs ()
  GetLine : Cmd me xs xs String