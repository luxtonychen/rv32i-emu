module LinRegf

import Data.Fin
import BitsVec
import LinMem
import LinContext

export
LinRegF : Type
LinRegF = LinMem

-- Mem LinRegF where
--   mem_write = mem_write_word
--   mem_read  = mem_read_word
--   mem_read_elim   = believe_me ()
--   mem_write_elim1 = believe_me ()
--   mem_write_elim2 = believe_me ()

export
lin_regf_read : (addr: BitsVec n) -> LinRegF -@ Res (BitsVec 32) (const LinRegF)
lin_regf_read (MkBitsVec val) regf = 
  let idx' = val * 4 
  in case ((val>0) && (val<32)) of
          False => (MkBitsVec 0) # regf
          True => mem_read {n=7} (MkBitsVec idx') regf

export
lin_regf_write : (addr: BitsVec n) -> (dat: BitsVec 32) -> LinRegF -@ LinRegF
lin_regf_write (MkBitsVec val) dat regf = 
  let idx' = val* 4 
  in case ((val>0) && (val<32)) of
          False => regf
          True =>  mem_write {n=7} (MkBitsVec idx') dat regf

public export
interface Mem regf => RegF regf where
  regf_read : (addr: BitsVec n) -> regf -@ Res (BitsVec 32) (const regf)
  regf_write : (addr: BitsVec n) -> (dat: BitsVec 32) -> regf -@ regf

  regf_read_zero : forall reg . ((MkBitsVec 0) # reg) = (regf_read {n=n} (MkBitsVec 0) reg)
  regf_write_zero : forall dat, reg . reg = (regf_write {n=n} (MkBitsVec 0) dat reg)

public export                 
RegF LinRegF where
  regf_read  = lin_regf_read
  regf_write = lin_regf_write
  regf_read_zero = Refl
  regf_write_zero = Refl
  
public export
Consumable LinRegF where
  consume regf = consume' regf
