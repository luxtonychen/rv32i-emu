module BitsVec

import System.FFI

public export
record BitsVec where
  constructor MkBitsVec
  len : Bits8
  val : Bits64

export
Show BitsVec where
  show (MkBitsVec len val) = show(val) ++ "{" ++ show(len) ++ "}"
  
export
Eq BitsVec where
  (==) bv1 bv2 = (bv1.len == bv2.len) && (bv1.val == bv2.val)
  

UnaryLenFn : Type
UnaryLenFn = Bits8 -> Bits64 -> Bits8

UnaryValFn : Type
UnaryValFn = Bits8 -> Bits64 -> Bits64

BinaryLenFn : Type
BinaryLenFn = Bits8 -> Bits64 -> UnaryLenFn

BinaryValFn : Type
BinaryValFn = Bits8 -> Bits64 -> UnaryValFn

pack : (a -> b -> c) -> (a -> b -> d) -> a -> b -> (c, d)
pack f g x y = (f x y, g x y)

pack2 : (a -> b -> c -> d -> e) -> (a -> b -> c -> d -> f) -> a -> b -> c -> d -> (e, f)
pack2 f g x y z v = (f x y z v, g x y z v)

lib_bv : String -> String
lib_bv fn = "C:" ++ fn ++ ",lib_bits_vec"

UnaryFnWarpTy : Type
UnaryFnWarpTy = (Bits8 -> Bits64 -> (Bits8, Bits64)) -> BitsVec -> BitsVec

BinaryFnWarpTy : Type
BinaryFnWarpTy = (Bits8 -> Bits64 -> Bits8 -> Bits64 -> (Bits8, Bits64)) -> BitsVec -> BitsVec -> BitsVec

unaryFnWarp : UnaryFnWarpTy
unaryFnWarp f x with (f x.len x.val)
  unaryFnWarp f x | (len', val') = MkBitsVec len' val'
  
binaryFnWarp : BinaryFnWarpTy
binaryFnWarp f x y with (f x.len x.val y.len y.val)
  binaryFnWarp f x y | (len', val') = MkBitsVec len' val'
  
mkUnaryFn : UnaryLenFn -> UnaryValFn -> BitsVec -> BitsVec
mkUnaryFn f g =  unaryFnWarp $ pack f g

mkBinaryFn : BinaryLenFn -> BinaryValFn -> BitsVec -> BitsVec -> BitsVec
mkBinaryFn f g =  binaryFnWarp $ pack2 f g

%foreign (lib_bv "bv_get_range_len")
bv_get_range_len : Bits8 -> Bits8 -> UnaryLenFn

%foreign (lib_bv "bv_get_range_val")
bv_get_range_val : Bits8 -> Bits8 -> UnaryValFn

export
bv_get_range : (lb:Bits8) -> (ub:Bits8) -> BitsVec -> BitsVec
bv_get_range lb ub = mkUnaryFn (bv_get_range_len lb ub) (bv_get_range_val lb ub)

%foreign (lib_bv "bv_sign_ext_len")
bv_sign_ext_len : UnaryLenFn

%foreign (lib_bv "bv_sign_ext_val")
bv_sign_ext_val : UnaryValFn

export
bv_sign_ext : BitsVec -> BitsVec
bv_sign_ext = mkUnaryFn bv_sign_ext_len bv_sign_ext_val

%foreign (lib_bv "bv_zero_ext_len")
bv_zero_ext_len : UnaryLenFn

%foreign (lib_bv "bv_zero_ext_val")
bv_zero_ext_val : UnaryValFn

export
bv_zero_ext : BitsVec -> BitsVec
bv_zero_ext = mkUnaryFn bv_zero_ext_len bv_zero_ext_val

%foreign (lib_bv "bv_and_len")
bv_and_len : BinaryLenFn

%foreign (lib_bv "bv_and_val")
bv_and_val : BinaryValFn

export
bv_and : BitsVec -> BitsVec -> BitsVec
bv_and = mkBinaryFn bv_and_len bv_and_val

%foreign (lib_bv "bv_or_len")
bv_or_len : BinaryLenFn

%foreign (lib_bv "bv_or_val")
bv_or_val : BinaryValFn

export
bv_or : BitsVec -> BitsVec -> BitsVec
bv_or = mkBinaryFn bv_or_len bv_or_val

%foreign (lib_bv "bv_xor_len")
bv_xor_len : BinaryLenFn

%foreign (lib_bv "bv_xor_val")
bv_xor_val : BinaryValFn

export
bv_xor : BitsVec -> BitsVec -> BitsVec
bv_xor = mkBinaryFn bv_xor_len bv_xor_val


%foreign (lib_bv "bv_add_len")
bv_add_len : BinaryLenFn

%foreign (lib_bv "bv_add_val")
bv_add_val : BinaryValFn

export
bv_add : BitsVec -> BitsVec -> BitsVec
bv_add = mkBinaryFn bv_add_len bv_add_val

%foreign (lib_bv "bv_sub_len")
bv_sub_len : BinaryLenFn

%foreign (lib_bv "bv_sub_val")
bv_sub_val : BinaryValFn

export
bv_sub : BitsVec -> BitsVec -> BitsVec
bv_sub = mkBinaryFn bv_sub_len bv_sub_val

%foreign (lib_bv "bv_complement_len")
bv_complement_len : Bits8 -> Bits64 -> Bits8

%foreign (lib_bv "bv_complement_val")
bv_complement_val : UnaryValFn

bv_complement : BitsVec -> BitsVec
bv_complement = mkUnaryFn bv_complement_len bv_complement_val

%foreign (lib_bv "bv_concatenate_len")
bv_concatenate_len : BinaryLenFn

%foreign (lib_bv "bv_concatenate_val")
bv_concatenate_val : BinaryValFn

export
bv_concatenate : BitsVec -> BitsVec -> BitsVec
bv_concatenate = mkBinaryFn bv_concatenate_len bv_concatenate_val

%foreign (lib_bv "bv_srl_len")
bv_srl_len : BinaryLenFn

%foreign (lib_bv "bv_srl_val")
bv_srl_val : BinaryValFn

export
bv_srl : BitsVec -> BitsVec -> BitsVec
bv_srl = mkBinaryFn bv_srl_len bv_srl_val

%foreign (lib_bv "bv_sra_len")
bv_sra_len : BinaryLenFn

%foreign (lib_bv "bv_sra_val")
bv_sra_val : BinaryValFn

export
bv_sra : BitsVec -> BitsVec -> BitsVec
bv_sra = mkBinaryFn bv_sra_len bv_sra_val

%foreign (lib_bv "bv_sll_len")
bv_sll_len : BinaryLenFn

%foreign (lib_bv "bv_sll_val")
bv_sll_val : BinaryValFn

export
bv_sll : BitsVec -> BitsVec -> BitsVec
bv_sll = mkBinaryFn bv_sll_len bv_sll_val

%foreign (lib_bv "bv_lt_len")
bv_lt_len : BinaryLenFn

%foreign (lib_bv "bv_lt_val")
bv_lt_val : BinaryValFn

export
bv_lt : BitsVec -> BitsVec -> BitsVec
bv_lt = mkBinaryFn bv_lt_len bv_lt_val

%foreign (lib_bv "bv_ltu_len")
bv_ltu_len : BinaryLenFn

%foreign (lib_bv "bv_ltu_val")
bv_ltu_val : BinaryValFn

export
bv_ltu : BitsVec -> BitsVec -> BitsVec
bv_ltu = mkBinaryFn bv_ltu_len bv_ltu_val

%foreign (lib_bv "bv_print")
prim__bv_print : Bits8 -> Bits64 -> PrimIO()

export
bv_print : BitsVec -> IO()
bv_print (MkBitsVec len val) = primIO $ prim__bv_print len val
