module RegFile

import BitsVec
import Mem
import Data.Vect

public export
RegFile : Type
RegFile = MemTy

export
regf_read : (idx : BitsVec) -> (regf : RegFile) -> BitsVec
regf_read (MkBitsVec len val) regf with (val * 4) --32bits reg in byte addressed mem
  regf_read (MkBitsVec len val) regf | idx' with ((val>0) && (val<32))
    regf_read (MkBitsVec len val) regf | idx' | False = MkBitsVec 32 0
    regf_read (MkBitsVec len val) regf | idx' | True = mem_read_word (MkBitsVec 7 idx') regf

export
regf_write : (idx : BitsVec) -> (dat:BitsVec) -> (regf : RegFile) -> IO RegFile
regf_write (MkBitsVec len val) dat regf with (val * 4) --32bits reg
  regf_write (MkBitsVec len val) dat regf | idx' with ((val>0) && (val<32))
    regf_write (MkBitsVec len val) dat regf | idx' | False = pure regf
    regf_write (MkBitsVec len val) dat regf | idx' | True = mem_write_word (MkBitsVec 7 idx') dat regf
    
export
regf_read' : (BitsVec, RegFile) -> (BitsVec, RegFile)
regf_read' ((MkBitsVec len val), regf) with (val * 4) --32bits reg in byte addressed mem
  regf_read' ((MkBitsVec len val), regf) | idx' with ((val>0) && (val<32))
    regf_read' ((MkBitsVec len val), regf) | idx' | False = (MkBitsVec 32 0, regf)
    regf_read' ((MkBitsVec len val), regf) | idx' | True = ((mem_read_word (MkBitsVec 7 idx') regf), regf)

export
regf_write' : ((BitsVec, BitsVec), RegFile) -> ((), IO RegFile)
regf_write' (((MkBitsVec len val), dat), regf) with (val * 4) --32bits reg
  regf_write' (((MkBitsVec len val), dat), regf) | idx' with ((val>0) && (val<32))
    regf_write' (((MkBitsVec len val), dat), regf) | idx' | False = ((), pure regf)
    regf_write' (((MkBitsVec len val), dat), regf) | idx' | True = ((), mem_write_word (MkBitsVec 7 idx') dat regf)
    

test : IO()
test = let mem1 = mem_create (4*32)
           mem2 = mem_create (4*32)
       in do 
             mem1' <- regf_write (MkBitsVec 5 31) (MkBitsVec 32 0xFFFFFFFF) mem1
             mem_diff mem1' mem2
             mem_free mem1
             mem_free mem2
