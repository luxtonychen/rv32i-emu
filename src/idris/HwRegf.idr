module HwRegf

import public LinRegf
import LinContext
import BitsVec
import public HwSignal


regf_read' : RegIdx -> LinRegF -@ Res Dat $ const LinRegF
regf_read' Abst regf = Abst # regf
regf_read' (V addr) regf = 
  let (dat # regf') = regf_read addr regf 
  in (V dat) # regf'

regf_write' : RegIdx -> Dat -> LinRegF -@ LinRegF
regf_write' Abst _ regf = regf
regf_write' _ Abst regf = regf
regf_write' (V addr) (V dat) regf = regf_write addr dat regf

hwRegF : LinContext (RegIdx, RegIdx, RegIdx, Dat) LinRegF
      -@ LinContext (Dat, Dat) LinRegF
hwRegF (MkLC (rs1, rs2, rd, wdat) regf) = 
  let d1 # regf1 = regf_read'  rs1 regf
      d2 # regf2 = regf_read'  rs2 regf1
      regf_o     = regf_write' rd wdat regf2
  in MkLC (d1, d2) regf_o

public export
hw_regf_read : LinContext (BitsVec 5, BitsVec 5) LinRegF -@ LinContext (BitsVec 32, BitsVec 32) LinRegF
hw_regf_read (MkLC (r1, r2) regf) = 
  let dat1 # regf'  = regf_read r1 regf
      dat2 # regf'' = regf_read r2 regf'
  in MkLC (dat1, dat2) regf''

public export
hw_regf_write : LinContext (BitsVec 5, BitsVec 32) LinRegF -@ LinContext () LinRegF
hw_regf_write (MkLC (rd, dat) regf) = MkLC () (regf_write rd dat regf)
                  
hw_abst : (f : Dat -> Dat -> Dat)
       -> LinContext (RegIdx, RegIdx, RegIdx) LinRegF
       -@ LinContext () LinRegF
hw_abst f (MkLC (rs1, rs2, rd) regf) = 
  let MkLC (d1, d2) regf' = hwRegF (MkLC (rs1, rs2, rd, Abst) regf)
      MkLC _ regf_o       = hwRegF (MkLC (rs1, rs2, rd, f d1 d2) regf')
  in MkLC () regf_o
  
sw_abst : (f : Dat -> Dat -> Dat)
       -> LinContext (RegIdx, RegIdx, RegIdx) LinRegF
       -@ LinContext () LinRegF
sw_abst f (MkLC (rs1, rs2, rd) regf) = 
  let d1 # regf1 = regf_read' rs1 regf 
      d2 # regf2 = regf_read' rs2 regf1
      regf_o = regf_write' rd (f d1 d2) regf2
  in MkLC () regf_o
  
lemma3 : (regf_read' rs regf = d1 # regf') -> regf' = regf
lemma3 prf = believe_me prf

lemma2: (rd : RegIdx) -> (regf: LinRegF) -> (regf_write' rd Abst regf) = regf
lemma2 Abst regf = Refl
lemma2 (V x) regf = Refl

lemma1: (rs1 : RegIdx) -> (rs2 : RegIdx) -> (rd : RegIdx) -> (regf: LinRegF)
    -> (hwRegF (MkLC (rs1, rs2, rd, Abst) regf))
     = (let d1 # regf1 = regf_read' rs1 regf in let d2 # regf2 = regf_read' rs2 regf1 in MkLC (d1, d2) regf2)
lemma1 rs1 rs2 rd regf with (regf_read' rs1 regf)
  lemma1 rs1 rs2 rd regf | d1 # regf1 with (regf_read' rs2 regf1)
    lemma1 rs1 rs2 rd regf | d1 # regf1 | d2 # regf2 with (lemma2 rd regf2)
      lemma1 rs1 rs2 rd regf | d1 # regf1 | d2 # regf2 | prf = rewrite prf in Refl

equality : (f : Dat -> Dat -> Dat)
        -> (init : LinContext (RegIdx, RegIdx, RegIdx) LinRegF)
        -> (hw_abst f init) = (sw_abst f init)
equality f (MkLC (rs1, rs2, rd) regf) with (regf_read' rs1 regf) proof p1
  equality f (MkLC (rs1, rs2, rd) regf) | d1 # regf1' with (regf_read' rs2 regf1') proof p2
    equality f (MkLC (rs1, rs2, rd) regf) | d1 # regf1' | d2 # regf2' with (lemma2 rd regf2')
      equality f (MkLC (rs1, rs2, rd) regf) | d1 # regf1' | d2 # regf2' | prf with (lemma3 p1)
        equality f (MkLC (rs1, rs2, rd) regf) | d1 # regf1' | d2 # regf2' | prf | prf1 with (lemma3 p2)
          equality f (MkLC (rs1, rs2, rd) regf) | d1 # regf1' | d2 # regf2' | prf | prf1 | prf2 = 
            rewrite prf in 
            rewrite prf2 in rewrite prf1 in 
            rewrite p1 in rewrite p2 in 
            rewrite prf2 in rewrite prf1 in Refl

