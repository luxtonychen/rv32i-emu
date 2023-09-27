module LinMem

import System.FFI
import BitsVec
import Data.Fin
import LinContext

import FinUtils
import Data.Stream
import Data.List

lib_mem : String -> String
lib_mem fn = "C:" ++ fn ++ ",lib_mem"

export
MemTy : Type
MemTy = Ptr Bits8

%name MemTy mem_, mem1_, mem2_

export
LinMem : Type
LinMem = !* MemTy

%name LinMem mem, mem1, mem2

public export
AddrTy : Type
AddrTy = Bits32

%foreign (lib_mem "mem_create")
mem_create' : AddrTy -> MemTy

%foreign (lib_mem "mem_read_32_val")
mem_read_32_val : Bits8 -> Bits64 -> MemTy -> Bits64

%foreign (lib_mem "mem_write_32")
mem_write_32 : Bits8 -> Bits64 -> Bits8 -> Bits64 -> MemTy -> MemTy

export
mem_read_word : {n:_} -> (addr: BitsVec n) -> (1 _: LinMem) -> Res (BitsVec 32) (const LinMem)
mem_read_word (MkBitsVec addr) (MkBang mem_) = (MkBitsVec $ mem_read_32_val (lenToBits n) addr mem_) # (MkBang mem_)
       
export
mem_write_word : {n:_} -> (addr: BitsVec n) -> (dat: BitsVec 32) -> (1 _: LinMem) -> LinMem
mem_write_word {n} (MkBitsVec addr) (MkBitsVec dat) (MkBang mem) = MkBang $ mem_write_32 (lenToBits n) addr 32 dat mem

%foreign (lib_mem "mem_free")
mem_free' : MemTy -> ()

%foreign (lib_mem "mem_save_2")
mem_save' : String -> MemTy -> MemTy


%foreign (lib_mem "mem_load_2")
mem_load' : String -> MemTy

-- contract for memory components
public export
interface Mem mem where
  mem_create : AddrTy -> mem
  mem_load   : String -> mem
  mem_save   : String -> mem -@ mem
  mem_read   : {n:_} -> (addr: BitsVec n) -> (1 _: mem) -> Res (BitsVec 32) (const mem)
  mem_write  : {n:_} -> (addr: BitsVec n) -> (dat: BitsVec 32) -> (1 _: mem) -> mem
  
  -- read a memory should not change its state
  mem_read_elim : {n:_} -> (addr: BitsVec n) -> (1 m: mem) 
               -> (proj2 $ mem_read addr m) = m
  
  -- read after write should produce the writen value
  mem_write_elim1 : {n:_} -> (addr: BitsVec n) -> (dat : BitsVec 32) -> (1 m: mem) 
                 -> (mem_read addr $ mem_write addr dat m) = dat # (mem_write addr dat m)
  
  -- a sequence of write operation should produce the most recent value
  mem_write_elim2 : {n:_} -> (addr: BitsVec n) -> (dat' : BitsVec 32) -> (dat : BitsVec 32) -> (1 m: mem) 
                 -> (mem_write addr dat $ mem_write addr dat' m) = mem_write addr dat m

public export                  
Mem LinMem where
  mem_create = MkBang . mem_create'
  mem_load   = MkBang . mem_load'
  mem_save str (MkBang mem_) = MkBang $ mem_save' str mem_
  mem_read  = mem_read_word
  mem_write = mem_write_word
  mem_read_elim   = believe_me ()
  mem_write_elim1 = believe_me ()
  mem_write_elim2 = believe_me ()
  

export
consume' : LinMem -@ ()
consume' (MkBang mem) = mem_free' mem

export
Consumable LinMem where
  consume = consume'
