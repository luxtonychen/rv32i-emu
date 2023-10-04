module NativeLinReg

import LinContext
import Data.Fin
import Data.Vect
import BitsVec

public export
interface IsReg (reg : Type -> Type) | reg where
  reg_make : ty -> reg ty
  reg_read : reg ty -@ Res ty (const $ reg ty)
  reg_write: ty -> reg ty -@ reg ty
  reg_prop_1: (v: ty) -> (r : reg ty) -> (reg_read . reg_write v) r = v # reg_write v r
  reg_prop_2: (v1: ty) -> (v2: ty) -> (r : reg ty) -> (reg_write v2 . reg_write v1) r = reg_write v2 r
  
-- An Implementation

public export  
record LinReg vTy where
  constructor Reg
  val : vTy

export
IsReg LinReg where
  reg_make = Reg
  reg_read (Reg val) = val # Reg val
  reg_write val' (Reg val) = Reg val'
  reg_prop_1 v (Reg val) = Refl
  reg_prop_2 v1 v2 (Reg val) = Refl

export
Consumable (LinReg vTy) where
  consume (Reg val) = ()
  
export
reg_update: (a -> a) -> LinReg a -@ LinReg a
reg_update f r = let v # r' = reg_read r in reg_write (f v) r'

  
RegF : (size: Nat) -> (ty: Type) -> Type
RegF size ty = LinVect size (LinReg ty)

regf_read' : Fin (S n) -> (RegF (S n) ty) -@ (Res ty (const $ RegF (S n) ty))
regf_read' idx = (val_app (index idx)) . unzip . (lin_map reg_read)

regf_read : {m:_} -> {n:_} -> ty -> BitsVec m -> (RegF (S n) ty) -@ (Res ty (const $ RegF (S n) ty))
regf_read {m} {n} x idx regf = 
  let idx' = (bv2Fin n idx) 
  in case idx' of
       Nothing => x # regf
       (Just i) => regf_read' i regf

    



