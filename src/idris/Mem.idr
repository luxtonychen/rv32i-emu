module Mem

import System.FFI
import BitsVec
import Data.Fin

lib_mem : String -> String
lib_mem fn = "C:" ++ fn ++ ",lib_mem"

export
MemTy : Type
MemTy = Ptr Bits8

public export
AddrTy : Type
AddrTy = Bits32

export
%foreign (lib_mem "mem_create")
mem_create : AddrTy -> MemTy

%foreign (lib_mem "mem_read_32_val")
mem_read_32_val : Bits8 -> Bits64 -> MemTy -> Bits64

%foreign (lib_mem "mem_write_32")
mem_write_32 : Bits8 -> Bits64 -> Bits8 -> Bits64 -> MemTy -> MemTy

%foreign (lib_mem "mem_write_32")
prim__mem_write_32 : Bits8 -> Bits64 -> Bits8 -> Bits64 -> MemTy -> PrimIO MemTy

export
mem_read_word : {n: _} -> (BitsVec n, MemTy) -> (BitsVec 32, MemTy)
mem_read_word {n} ((MkBitsVec val), mem) = (MkBitsVec $ mem_read_32_val (lenToBits n) val mem,
                                            mem)

export
mem_write_word : {n: _} -> ((BitsVec n, BitsVec 32), MemTy) -> ((), IO MemTy)
mem_write_word {n} (((MkBitsVec val1), (MkBitsVec val2)), mem)
  = ((), primIO $ prim__mem_write_32 (lenToBits n) val1 32 val2 mem)
  
%foreign (lib_mem "mem_free")
prim__mem_free : MemTy -> PrimIO ()

export
mem_free : MemTy -> IO()
mem_free mem = primIO  $ prim__mem_free mem

%foreign (lib_mem "mem_save_2")
prim__mem_save : String -> MemTy -> PrimIO MemTy

export
mem_save : String -> MemTy -> IO MemTy
mem_save str mem = primIO $ prim__mem_save str mem

export
%foreign (lib_mem "mem_load_2")
mem_load : String -> MemTy
