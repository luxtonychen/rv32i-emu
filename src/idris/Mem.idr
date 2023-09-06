module Mem

import System.FFI
import BitsVec

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
mem_read_word : (addr:BitsVec) -> MemTy -> BitsVec
mem_read_word (MkBitsVec len val) mem = MkBitsVec 32 $ mem_read_32_val len val mem

export
mem_read_word' : (BitsVec, MemTy) -> (BitsVec, MemTy)
mem_read_word' ((MkBitsVec len val), mem) = (MkBitsVec 32 $ mem_read_32_val len val mem, mem)

export
mem_write_word : (addr:BitsVec) -> (dat:BitsVec) -> MemTy -> IO MemTy
mem_write_word (MkBitsVec len1 val1) (MkBitsVec len2 val2) mem 
  = primIO $ prim__mem_write_32 len1 val1 len2 val2 mem
  
export
mem_write_word' : ((BitsVec, BitsVec), MemTy) -> ((), IO MemTy)
mem_write_word' (((MkBitsVec len1 val1), (MkBitsVec len2 val2)), mem)
  = ((), primIO $ prim__mem_write_32 len1 val1 len2 val2 mem)

%foreign (lib_mem "mem_diff")
prim__mem_diff : MemTy -> MemTy -> PrimIO ()

export
mem_diff : MemTy -> MemTy -> IO()
mem_diff mem1 mem2 = primIO  $ prim__mem_diff mem1 mem2

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

record IsMem (mem_ty : Type) (addr_ty : Type) (val_ty : Type) where
  constructor MkMem
  read  : addr_ty -> mem_ty -> val_ty
  write : addr_ty -> val_ty -> mem_ty -> mem_ty
  functional_prop : (addr : addr_ty) -> (val : val_ty) -> (mem : mem_ty) 
                  -> ((read addr $ write addr val mem) = val)
  overwrite_prop  : forall val0 . (addr : addr_ty) -> (val : val_ty) -> (mem : mem_ty) 
                  -> ((write addr val $ write addr val0 mem) = (write addr val mem))



test : IO()
test = let mem1 = mem_create (4*32)
           mem2 = mem_create (4*32)
       in do 
             mem1' <- mem_write_word (MkBitsVec 8 (31*4)) (MkBitsVec 32 0xFFFFFFFF) mem1
             mem_diff mem1' mem2
             _ <- mem_save "mem_test" mem1'
             mem_free mem1
             mem_free mem2
           
