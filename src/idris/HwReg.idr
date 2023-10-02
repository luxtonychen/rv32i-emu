module HwReg

import public NativeLinReg
import LinContext

record HwReg a where
  constructor MkReg
  1 reg : LinReg a
  1 read: LinContext () (LinReg a) -@ LinContext a (LinReg a)
  1 update: LinContext a (LinReg a) -@ LinContext () (LinReg a)
  
public export
hw_reg_read: LinContext () (LinReg a) -@ LinContext a (LinReg a)
hw_reg_read (MkLC () reg) = (fromLDPair . reg_read) reg

public export
hw_reg_write: LinContext a (LinReg a) -@ LinContext () (LinReg a)
hw_reg_write (MkLC val reg) = MkLC () $ reg_write val reg
