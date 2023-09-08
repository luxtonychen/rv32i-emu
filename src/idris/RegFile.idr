module RegFile

import Data.Fin
import BitsVec
import Mem

public export
RegFile : Type
RegFile = MemTy

export
regf_read : (BitsVec n, RegFile) -> (BitsVec 32, RegFile)
regf_read ((MkBitsVec val), regf) with (val * 4) --32bits reg in byte addressed mem
  regf_read ((MkBitsVec val), regf) | idx' with ((val>0) && (val<32))
    regf_read ((MkBitsVec val), regf) | idx' | False = (MkBitsVec 0, regf)
    regf_read ((MkBitsVec val), regf) | idx' | True = mem_read_word {n=7} ((MkBitsVec idx'), regf)

export
regf_write : ((BitsVec n, BitsVec 32), RegFile) -> ((), IO RegFile)
regf_write (((MkBitsVec val), dat), regf) with (val * 4) --32bits reg
  regf_write (((MkBitsVec val), dat), regf) | idx' with ((val>0) && (val<32))
    regf_write (((MkBitsVec val), dat), regf) | idx' | False = ((), pure regf)
    regf_write (((MkBitsVec val), dat), regf) | idx' | True = mem_write_word {n=7} (((MkBitsVec idx'), dat), regf)
