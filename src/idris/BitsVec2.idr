module BitsVec2

import System.FFI
import Data.Fin
import Fin65ToBits


LenTy : Type
LenTy = Fin 65

-- BitsVec of length 0 - 64
record BitsVec (len : LenTy) where
  constructor MkBitsVec
  val : Bits64

lenToBits : LenTy -> Bits8
lenToBits = fin65ToBits

sub : LenTy -> LenTy -> LenTy
sub x y with (x > y)
  sub x y | False = 0
  sub x y | True = (x - y)
  
add : LenTy -> LenTy -> LenTy
add x y = 
  let x' = finToNat x
      y' = finToNat y 
  in case (x' + y') > 64 of
          False => x + y
          True => 64

bv_get_len : {n : _} -> BitsVec n -> Nat
bv_get_len {n} x = finToNat n

lib_bv : String -> String
lib_bv fn = "C:" ++ fn ++ ",lib_bits_vec"

UnaryValFn : Type
UnaryValFn = Bits8 -> Bits64 -> Bits64

BinaryValFn : Type
BinaryValFn = Bits8 -> Bits64 -> UnaryValFn

%foreign (lib_bv "bv_get_range_val")
bv_get_range_val : Bits8 -> Bits8 -> UnaryValFn

export
bv_get_range : {n: _} -> (lb: LenTy) -> (ub: LenTy) -> BitsVec n -> BitsVec (ub `sub` lb)
bv_get_range {n} lb ub (MkBitsVec val) = 
  let lb'  = lenToBits lb 
      ub'  = lenToBits ub 
      n'   = lenToBits n
      val' = (bv_get_range_val lb' ub' n' val)
  in MkBitsVec val'
  
%foreign (lib_bv "bv_sign_ext_val")
bv_sign_ext_val : UnaryValFn

export
bv_sign_ext : {n: _} -> BitsVec n -> BitsVec 64
bv_sign_ext {n} (MkBitsVec val) = 
  let n'   = lenToBits n 
      val' = (bv_sign_ext_val n' val)
  in MkBitsVec val'
  
%foreign (lib_bv "bv_zero_ext_val")
bv_zero_ext_val : UnaryValFn

export
bv_zero_ext : {n: _} -> BitsVec n -> BitsVec 64
bv_zero_ext {n} (MkBitsVec val) = 
  let n'   = lenToBits n 
      val' = (bv_zero_ext_val n' val)
  in MkBitsVec val'
  
    
%foreign (lib_bv "bv_and_val")
bv_and_val : BinaryValFn

export
bv_and : {n: _} -> BitsVec n -> BitsVec n -> BitsVec n
bv_and {n} (MkBitsVec v1) (MkBitsVec v2) = 
  let n' = lenToBits n 
      val = bv_and_val n' v1 n' v2 
  in MkBitsVec val

%foreign (lib_bv "bv_or_val")
bv_or_val : BinaryValFn

export
bv_or : {n: _} -> BitsVec n -> BitsVec n -> BitsVec n
bv_or {n} (MkBitsVec v1) (MkBitsVec v2) = 
  let n' = lenToBits n 
      val = bv_or_val n' v1 n' v2 
  in MkBitsVec val

%foreign (lib_bv "bv_xor_val")
bv_xor_val : BinaryValFn

export
bv_xor : {n: _} -> BitsVec n -> BitsVec n -> BitsVec n
bv_xor {n} (MkBitsVec v1) (MkBitsVec v2) = 
  let n' = lenToBits n 
      val = bv_xor_val n' v1 n' v2 
  in MkBitsVec val

%foreign (lib_bv "bv_add_val")
bv_add_val : BinaryValFn

export
bv_add : {n: _} -> BitsVec n -> BitsVec n -> BitsVec (n `add` 1)
bv_add {n} (MkBitsVec v1) (MkBitsVec v2) = 
  let n' = lenToBits n 
      val = bv_add_val n' v1 n' v2 
  in MkBitsVec val

%foreign (lib_bv "bv_sub_val")
bv_sub_val : BinaryValFn

export
bv_sub : {n: _} -> BitsVec n -> BitsVec n -> BitsVec (n `add` 1)
bv_sub {n} (MkBitsVec v1) (MkBitsVec v2) = 
  let n' = lenToBits n 
      val = bv_sub_val n' v1 n' v2 
  in MkBitsVec val

%foreign (lib_bv "bv_complement_val")
bv_complement_val : UnaryValFn

bv_complement : {n: _} -> BitsVec n -> BitsVec n
bv_complement {n} (MkBitsVec val) = 
let n'   = lenToBits n 
    val' = bv_complement_val n' val
  in MkBitsVec val'

%foreign (lib_bv "bv_concatenate_val")
bv_concatenate_val : BinaryValFn

export
bv_concatenate : {m: _} -> {n: _} -> BitsVec m -> BitsVec n -> BitsVec (m `add` n)
bv_concatenate {m} {n} (MkBitsVec x) (MkBitsVec sht) = 
  let m' = lenToBits m 
      n' = lenToBits n
      y  = bv_concatenate_val m' x n' sht
  in MkBitsVec y

%foreign (lib_bv "bv_srl_val")
bv_srl_val : BinaryValFn

export
bv_srl : {n: _} -> {m:_} -> BitsVec n -> BitsVec m -> BitsVec n
bv_srl {n} {m} (MkBitsVec v1) (MkBitsVec v2) = 
  let n' = lenToBits n 
      m' = lenToBits m
      val = bv_srl_val n' v1 n' v2 
  in MkBitsVec val

%foreign (lib_bv "bv_sra_val")
bv_sra_val : BinaryValFn

export
bv_sra : {n: _} -> {m:_} -> BitsVec n -> BitsVec m -> BitsVec n
bv_sra {n} {m} (MkBitsVec v1) (MkBitsVec v2) = 
  let n' = lenToBits n 
      m' = lenToBits m
      val = bv_sra_val n' v1 n' v2 
  in MkBitsVec val

%foreign (lib_bv "bv_sll_val")
bv_sll_val : BinaryValFn

export
bv_sll : {n: _} -> {m:_} -> BitsVec n -> BitsVec m -> BitsVec n
bv_sll {n} {m} (MkBitsVec v1) (MkBitsVec v2) = 
  let n' = lenToBits n 
      m' = lenToBits m
      val = bv_sll_val n' v1 n' v2 
  in MkBitsVec val

%foreign (lib_bv "bv_lt_val")
bv_lt_val : BinaryValFn

export
bv_lt : {n: _} -> BitsVec n -> BitsVec n -> BitsVec 1
bv_lt {n} (MkBitsVec v1) (MkBitsVec v2) = 
  let n' = lenToBits n 
      val = bv_lt_val n' v1 n' v2 
  in MkBitsVec val

%foreign (lib_bv "bv_ltu_val")
bv_ltu_val : BinaryValFn

export
bv_ltu : {n: _} -> BitsVec n -> BitsVec n -> BitsVec 1
bv_ltu {n} (MkBitsVec v1) (MkBitsVec v2) = 
    let n'  = lenToBits n 
        val = bv_ltu_val n' v1 n' v2 
    in MkBitsVec val
  
%foreign (lib_bv "bv_to_string")
bv_to_string' : Bits8 -> Bits64 -> String

export
bv_to_string : {n: _} -> BitsVec n -> String
bv_to_string {n} (MkBitsVec val) = bv_to_string' (lenToBits n) val
  
%foreign (lib_bv "bv_print")
prim__bv_print : Bits8 -> Bits64 -> PrimIO()

export
bv_print : {n: _} -> BitsVec n -> IO()
bv_print {n} (MkBitsVec val) = primIO $ prim__bv_print (lenToBits n) val
   
export
{n:_} -> Show (BitsVec n) where
  show {n} x = bv_to_string x
--   --(MkBitsVec len val) 
  
export
Eq (BitsVec n) where
  (==) (MkBitsVec m) (MkBitsVec n) = m == n
