import Data.Fin
import FinUtils
import BitsVec
import LinMem
import LinRegf
import RV32I_Inst
import LinContext
import NativeLinReg
import Data.List
import System
import System.File
import Data.String
import HwRegf
import HwReg
import Language.Reflection

%ambiguity_depth 5

PC : Type
PC = LinReg (BitsVec 32)



Context: Type
Context = LPair LinMem (LPair LinRegF PC)

ContextExt: Type
ContextExt = LPair Context 
                   (LPair (LinReg $ BitsVec 1)       --sign
                  $ LPair (LinReg $ OP) -- op
                          (LPair (LinReg $ BitsVec 5) -- reg idx
                                 (LinReg $ BitsVec 32))) -- pc

bv_cast_32 : {n: _} -> BitsVec n -> BitsVec 32
bv_cast_32 = bv_get_range 0 32  

arith : AOP -> (BitsVec 32, BitsVec 32) -> BitsVec 32
arith ADD  = bv_cast_32 . uncurry bv_add
arith SUB  = bv_cast_32 . uncurry bv_sub
arith XOR  = uncurry bv_xor
arith OR   = uncurry bv_or 
arith AND  = uncurry bv_and   
arith SLL  = uncurry bv_sll   
arith SRL  = uncurry bv_srl   
arith SRA  = uncurry bv_sra   
arith SLT  = bv_cast_32  . uncurry bv_lt    
arith SLTU = bv_cast_32  . uncurry bv_ltu

r_i1_fn: (IDX, AOP, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 5, BitsVec 32)
      -> (BitsVec 5, BitsVec 32, BitsVec 32)
r_i1_fn (idx, op, op1, op2', imm, rd, pc_) = 
  let op2 = case idx of
              RR => op2'
              RI => imm
      res = arith op (op1, op2)
      pc_' = bv_cast_32 $ pc_ `bv_add` MkBitsVec 4
  in (rd, res, pc_')

ij_fn: (IOPJ, BitsVec 32, BitsVec 32, BitsVec 5, BitsVec 32)
    -> (BitsVec 5, BitsVec 32, BitsVec 32)
ij_fn (op, op1, imm, rd, pc_) = 
  let res = bv_cast_32 $ pc_ `bv_add` MkBitsVec 4
      pc_' = bv_cast_32 $ bv_add op1 imm
  in (rd, res, pc_')

i2_fn1 : (IOP2, BitsVec 32, BitsVec 32, BitsVec 5, BitsVec 32)
      -> (IOP2, BitsVec 32, BitsVec 5, BitsVec 32)
i2_fn1 (op, op1, imm, rd, pc_) = 
  let addr = (bv_cast_32 $ bv_add op1 imm)
  in (op, addr, rd, pc_)

i2_write_fn1: LinContext (IOP2, BitsVec 32, BitsVec 5, BitsVec 32) ContextExt
           -@ LinContext () ContextExt
i2_write_fn1 (MkLC (op, addr, rd, pc_) $ (mem # regf # pc) # (sign # saved_op # saved_reg_idx # saved_pc)) = 
  let
    pc' = reg_write addr pc
    sign' = reg_write (MkBitsVec 1) sign
    saved_op' = reg_write (I2 op) saved_op
    saved_pc' = reg_write pc_ saved_pc
    saved_reg_idx' = reg_write rd saved_reg_idx
  in MkLC () ((mem # regf # pc') # (sign' # saved_op' # saved_reg_idx' # saved_pc'))

i2_fn2: (IOP2, BitsVec 5, BitsVec 32, BitsVec 32)
     -> (BitsVec 5, BitsVec 32, BitsVec 32)
i2_fn2 (op, rd, pc_, mem_data) = 
  let res = case op of
        LB    => bv_cast_32 $ bv_sign_ext $ bv_get_range 0 8 mem_data
        LH    => bv_cast_32 $ bv_sign_ext $ bv_get_range 0 16 mem_data
        LW    => mem_data
        LBU   => bv_cast_32 $ bv_zero_ext $ bv_get_range 0 8 mem_data
        LHU   => bv_cast_32 $ bv_zero_ext $ bv_get_range 0 16 mem_data
      pc_' = bv_cast_32 $ pc_ `bv_add` MkBitsVec 4
  in (rd, res, pc_')
      
r_i_write_fn: LinContext (BitsVec 5, BitsVec 32, BitsVec 32) ContextExt
           -@ LinContext () ContextExt
r_i_write_fn (MkLC (rd, res, pc_) $ (mem # regf # pc) # (sign # rest))
  = MkLC () $ (mem # regf_write rd res regf # reg_write pc_ pc) 
            # (reg_write (MkBitsVec 0) sign # rest)
  
s1_fn: (SOP1, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32)
    -> (BitsVec 32, BitsVec 32, BitsVec 32)
s1_fn (op, op1, op2, imm, pc_) = 
  let addr = bv_cast_32 $ op1 `bv_add` imm 
      pc_' = (bv_cast_32 $ pc_ `bv_add` MkBitsVec 4)
  in (pc_', addr, op2)

s2_fn1: (SOP2, BitsVec 32, BitsVec 5, BitsVec 32, BitsVec 32)
     -> (SOP2, BitsVec 5, BitsVec 32, BitsVec 32)
s2_fn1 (op, op1, rs2, imm, pc_) = 
  let addr = bv_cast_32 $ op1 `bv_add` imm 
  in (op, rs2, pc_, addr)
  
s2_write_fn1: LinContext (SOP2, BitsVec 5, BitsVec 32, BitsVec 32) ContextExt
           -@ LinContext () ContextExt
s2_write_fn1 (MkLC (op, rs2, pc_, addr) $ (mem # regf # pc) # (sign # saved_op # saved_reg_idx # saved_pc)) = 
  let
    pc' = reg_write addr pc
    sign'          = reg_write (MkBitsVec 1) sign         
    saved_op'      = reg_write (S2 op) saved_op     
    saved_pc'      = reg_write pc_ saved_pc      
    saved_reg_idx' = reg_write rs2 saved_reg_idx
  in MkLC () ((mem # regf # pc') # (sign' # saved_op' # saved_reg_idx' # saved_pc'))

s2_fn2: (SOP2, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32)
     -> (BitsVec 32, BitsVec 32, BitsVec 32)
s2_fn2 (op, op2, pc_, addr, mem_data) = 
  let res = case op of 
        SB => bv_concatenate (bv_get_range 8 32 mem_data)  (bv_get_range 0 8 op2)
        SH => bv_concatenate (bv_get_range 16 32 mem_data) (bv_get_range 0 16 op2)
      pc_'  = (bv_cast_32 $ pc_ `bv_add` MkBitsVec 4)
  in (pc_', addr, res)
  
s_write_fn: LinContext (BitsVec 32, BitsVec 32, BitsVec 32) ContextExt
         -@ LinContext () ContextExt
s_write_fn (MkLC (pc_, addr, res) $ (mem # regf # pc) # (sign # rest)) 
  = MkLC () $ (mem_write addr res mem # regf # reg_write pc_ pc) 
             # (reg_write (MkBitsVec 0) sign # rest)

b_fn1: BOP -> BitsVec 32 -> BitsVec 32 -> BitsVec 1
b_fn1 BEQ  op1 op2 = bv_eq op1 op2
b_fn1 BNE  op1 op2 = bv_neg $ bv_eq op1 op2
b_fn1 BLT  op1 op2 = bv_lt op1 op2
b_fn1 BGE  op1 op2 = bv_neg $ bv_lt op1 op2
b_fn1 BLTU op1 op2 = bv_ltu op1 op2
b_fn1 BGEU op1 op2 = bv_neg $ bv_ltu op1 op2
      
b_fn : (BOP, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32)-> BitsVec 32
b_fn (op, op1, op2, imm', pc_) = 
  let b = case op of 
        BEQ  => (bv_lt op1 op2)  == (bv_lt op2 op1)
        BNE  => (bv_lt op1 op2)  /= (bv_lt op2 op1)
        BLT  => (bv_lt op1 op2)  == (MkBitsVec 1)
        BGE  => (bv_lt op1 op2)  /= (MkBitsVec 1)
        BLTU => (bv_ltu op1 op2) == (MkBitsVec 1)
        BGEU => (bv_ltu op1 op2) /= (MkBitsVec 1)
      pc_' = if b then bv_get_range 0 32 $ pc_ `bv_add` (bv_get_range 0 32 $ bv_sign_ext imm')
                  else bv_get_range 0 32 $ pc_ `bv_add` MkBitsVec 4
  in pc_'
  
b_write_fn : LinContext (BitsVec 32) ContextExt -@ LinContext () ContextExt
b_write_fn (MkLC pc_ $ (mem # regf # pc) # rest)
  = (MkLC () $ (mem # regf # reg_write pc_ pc) # rest)
         
u_fn : (UOP, BitsVec 32, BitsVec 5, BitsVec 32)
    -> (BitsVec 5, BitsVec 32, BitsVec 32)
u_fn (op, imm', rd, pc_) = 
  let res = case op of 
        LUI => imm'
        AUIPC => bv_get_range 0 32 $ bv_add pc_ imm'
      pc_' = (bv_cast_32 $ pc_ `bv_add` MkBitsVec 4)
  in (rd, res, pc_')
  
u_write_fn : LinContext (BitsVec 5, BitsVec 32, BitsVec 32) ContextExt
          -@ LinContext () ContextExt
u_write_fn (MkLC (rd, res, pc_) $ (mem # regf # pc) # rest)
  = (MkLC () $ (mem # regf_write rd res regf # reg_write pc_ pc) # rest)

    
j_fn: (JOP, BitsVec 32, BitsVec 5, BitsVec 32)
   -> (BitsVec 5, BitsVec 32, BitsVec 32)
j_fn  (op, imm, rd, pc_) = 
  let 
      pc_' = bv_cast_32 $ pc_ `bv_add` imm
      res  = bv_cast_32 $ pc_ `bv_add` MkBitsVec 4
  in (rd, res, pc_')
  
j_write_fn: LinContext (BitsVec 5, BitsVec 32, BitsVec 32) ContextExt
         -@ LinContext () ContextExt
j_write_fn (MkLC (rd, res, pc_) $ (mem # regf # pc) # rest) 
  = MkLC () $ (mem # regf_write rd res regf # reg_write pc_ pc) # rest

read_fn: LinContext () ContextExt 
      -@ LinContext 
           (OP, BitsVec 32, BitsVec 32, BitsVec 5, BitsVec 5, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 1) 
           ContextExt
read_fn (MkLC () ((mem # regf # pc) # (sign # op # reg_idx # saved_pc))) = 
  let sign_    # sign' = reg_read sign
      addr     # pc'   = reg_read pc
      pc_2     # saved_pc' = reg_read saved_pc
      pc_ = if (sign_ == (MkBitsVec 1)) then pc_2 else addr
      mem_data # mem'  = mem_read addr mem
      r'       # reg_idx' = reg_read reg_idx
      (MkInst opc1 rs1 rs2' rd imm) = decode mem_data
      rs2 = if (sign_ == (MkBitsVec 1)) then r' else rs2'
      opc2     # op'   = reg_read op
      op1      # regf' = regf_read rs1 regf
      op2      # regf'' = regf_read rs2 regf' 
      rd = if (sign_ == (MkBitsVec 1)) then r' else rd
      opc = if (sign_ == (MkBitsVec 1)) then opc2 else opc1
  in (MkLC (opc, op1, op2, rs2, rd, imm, pc_, addr, mem_data, sign_) 
           ((mem' # regf'' # pc') # (sign' # op' # reg_idx' # saved_pc')))

write_mem_fn: BitsVec 1 -> OP 
           -> LinContext (BitsVec 32, BitsVec 32) LinMem
           -@ LinContext () LinMem
write_mem_fn (MkBitsVec 1) (S2 _) (MkLC (addr, dat) mem) = MkLC () $ mem_write addr dat mem
write_mem_fn (MkBitsVec 0) (S1 _) (MkLC (addr, dat) mem) = MkLC () $ mem_write addr dat mem
write_mem_fn _  _ (MkLC (addr, dat) mem) = MkLC () mem

write_regf_fn: BitsVec 1 -> OP 
           -> LinContext (BitsVec 5, BitsVec 32) LinRegF
           -@ LinContext () LinRegF
write_regf_fn (MkBitsVec 0) (I2 _) (MkLC (rd, dat) regf) = MkLC () $ regf
write_regf_fn _             (S2 _) (MkLC (rd, dat) regf) = MkLC () $ regf
write_regf_fn _             (B _)  (MkLC (rd, dat) regf) = MkLC () $ regf
write_regf_fn _             _      (MkLC (rd, dat) regf) = MkLC () $ regf_write rd dat regf

write_pc_fn: BitsVec 1 -> OP 
          -> LinContext (BitsVec 32, BitsVec 32) PC
          -@ LinContext () PC
write_pc_fn (MkBitsVec 0) (S2 _) (MkLC (pc_, r_addr) pc) = MkLC () $ reg_write r_addr pc
write_pc_fn (MkBitsVec 0) (I2 _) (MkLC (pc_, r_addr) pc) = MkLC () $ reg_write r_addr pc
write_pc_fn _ _ (MkLC (pc_, r_addr) pc) = MkLC () $ reg_write pc_ pc

||| input ((addr, dat), (rd, res), (pc_, r_addr))
write_fn_1: BitsVec 1 -> OP 
          -> LinContext ((BitsVec 32, BitsVec 32), (BitsVec 5, BitsVec 32), (BitsVec 32, BitsVec 32)) Context
          -@ LinContext () Context
write_fn_1 sign_ opc = (fst >@ id) .
  (write_mem_fn sign_ opc) <||> (write_regf_fn sign_ opc) <||> (write_pc_fn sign_ opc)
        

write_sign_fn: BitsVec 1 -> OP 
            -> LinContext () (LinReg $ BitsVec 1)
            -@ LinContext () (LinReg $ BitsVec 1)
write_sign_fn (MkBitsVec 0) (S2 _) (MkLC () sign) = MkLC () $ reg_write (MkBitsVec 1) sign
write_sign_fn (MkBitsVec 0) (I2 _) (MkLC () sign) = MkLC () $ reg_write (MkBitsVec 1) sign
write_sign_fn _ _ (MkLC () sign) = MkLC () $ reg_write (MkBitsVec 0) sign

write_op_fn: BitsVec 1 -> OP 
          -> LinContext () (LinReg OP)
          -@ LinContext () (LinReg OP)
write_op_fn (MkBitsVec 0) (S2 x) (MkLC () op) = MkLC () $ reg_write (S2 x) op
write_op_fn (MkBitsVec 0) (I2 x) (MkLC () op) = MkLC () $ reg_write (I2 x) op
write_op_fn _ _ (MkLC () op) = MkLC () op

write_reg_idx_fn: BitsVec 1 -> OP 
               -> LinContext (BitsVec 5, BitsVec 5) (LinReg $ BitsVec 5)
               -@ LinContext () (LinReg $ BitsVec 5)
write_reg_idx_fn (MkBitsVec 0) (S2 _) (MkLC (rs2, rd) reg_idx) = MkLC () $ reg_write rs2 reg_idx
write_reg_idx_fn (MkBitsVec 0) (I2 _) (MkLC (rs2, rd) reg_idx) = MkLC () $ reg_write rd reg_idx
write_reg_idx_fn _ _ (MkLC (rs2, rd) reg_idx) = MkLC () reg_idx

write_saved_pc_fn: BitsVec 1 -> OP 
                -> LinContext (BitsVec 32) (LinReg $ BitsVec 32)
                -@ LinContext () (LinReg $ BitsVec 32)
write_saved_pc_fn (MkBitsVec 0) (S2 _) (MkLC (pc_) saved_pc) = MkLC () $ reg_write pc_ saved_pc
write_saved_pc_fn (MkBitsVec 0) (I2 _) (MkLC (pc_) saved_pc) = MkLC () $ reg_write pc_ saved_pc
write_saved_pc_fn _ _ (MkLC (pc_) saved_pc) = MkLC () saved_pc

write_fn_2: BitsVec 1 -> OP 
           -> LinContext ((), (), (BitsVec 5, BitsVec 5), BitsVec 32)
                         (LPair (LinReg $ BitsVec 1) $ LPair (LinReg $ OP)
                         (LPair (LinReg $ BitsVec 5) (LinReg $ BitsVec 32)))
           -@ LinContext () 
                         (LPair (LinReg $ BitsVec 1) $ LPair (LinReg $ OP)
                         (LPair (LinReg $ BitsVec 5) (LinReg $ BitsVec 32)))
write_fn_2 sign_ opc = (fst >@ id) .
  (write_sign_fn sign_ opc) <||> (write_op_fn sign_ opc) <||> 
  (write_reg_idx_fn sign_ opc) <||> (write_saved_pc_fn sign_ opc)
  
write_in_expand: ((BitsVec 32, BitsVec 32), (BitsVec 5, BitsVec 32), (BitsVec 32, BitsVec 32), BitsVec 5)
              -> (((BitsVec 32, BitsVec 32), (BitsVec 5, BitsVec 32), (BitsVec 32, BitsVec 32)), 
                  ((), (), (BitsVec 5, BitsVec 5), BitsVec 32)) 
write_in_expand ((addr, dat), (rd, res), (pc_, r_addr), rs2) 
  = (((addr, dat), (rd, res), (pc_, r_addr)), ((), (), (rs2, rd), pc_))

-- ((addr, dat), (rd, res), (pc_, r_addr), rs2)

write_fn: BitsVec 1 -> OP 
       -> LinContext ((BitsVec 32, BitsVec 32), (BitsVec 5, BitsVec 32), (BitsVec 32, BitsVec 32), BitsVec 5)
                     ContextExt
       -@ LinContext () ContextExt
write_fn sign_ opc = (fst >@ id) 
                   . ((write_fn_1 sign_ opc) <||> (write_fn_2 sign_ opc))
                   . (write_in_expand >@ id)



rv32i : LinContext () ContextExt -@ LinContext () ContextExt
rv32i (MkLC () ctx) = 
  let MkLC (opc, op1, op2, rs2, rd, imm, pc_, addr, mem_data, sign_) ctx' 
        = read_fn (MkLC () ctx)
      res : BitsVec 32 = case opc of
        (MERGED RR op) => arith op (op1, op2)
        (MERGED RI op) => arith op (op1, imm)
        (IJ op) => bv_cast_32 $ pc_ `bv_add` MkBitsVec 4
        (I2 op) => case op of
                     LB  => bv_cast_32 $ bv_sign_ext $ bv_get_range 0 8 mem_data
                     LH  => bv_cast_32 $ bv_sign_ext $ bv_get_range 0 16 mem_data
                     LW  => mem_data
                     LBU => bv_cast_32 $ bv_zero_ext $ bv_get_range 0 8 mem_data
                     LHU => bv_cast_32 $ bv_zero_ext $ bv_get_range 0 16 mem_data
        (U op) => case op of 
                    LUI => imm
                    AUIPC => bv_get_range 0 32 $ bv_add pc_ imm
        (J op) => bv_cast_32 $ pc_ `bv_add` MkBitsVec 4
        _ => MkBitsVec 0
      pc_' : BitsVec 32 = case opc of
        (IJ _) => bv_cast_32 $ bv_add op1 imm
        (B op) => case (b_fn1 op op1 op2) of
                    (MkBitsVec 1) => bv_cast_32 $ pc_ `bv_add` imm
                    _ => bv_cast_32 $ pc_ `bv_add` MkBitsVec 4
        (J _) => bv_cast_32 $ pc_ `bv_add` imm
        (I2 _) => if (sign_ == MkBitsVec 0) then pc_ else bv_cast_32 $ pc_ `bv_add` MkBitsVec 4
        (S2 _) => if (sign_ == MkBitsVec 0) then pc_ else bv_cast_32 $ pc_ `bv_add` MkBitsVec 4
        _ => bv_cast_32 $ pc_ `bv_add` MkBitsVec 4 
      r_addr : BitsVec 32 = case sign_ of
        (MkBitsVec 0) => case opc of                              
                           (I2 _) => bv_cast_32 $ op1 `bv_add` imm
                           (S2 _) => bv_cast_32 $ op1 `bv_add` imm
                           _ => MkBitsVec 0
        _ => MkBitsVec 0
      w_addr : BitsVec 32 = case opc of
        (S1 _) => bv_cast_32 $ op1 `bv_add` imm
        _ => addr
      w_dat : BitsVec 32 = case opc of
        (S2 op) => case op of
                     SB => bv_concatenate (bv_get_range 8 32 mem_data)  (bv_get_range 0 8 op2)
                     SH => bv_concatenate (bv_get_range 16 32 mem_data) (bv_get_range 0 16 op2)
        (S1 _) => op2
        _ => MkBitsVec 0
  in write_fn sign_ opc $ MkLC ((w_addr, w_dat), (rd, res), (pc_', r_addr), rs2) ctx'

eval: String -> Nat -> IO ()
eval i_file n = 
  let mem = mem_load i_file
      reg = mem_create (4*32)
      pc : PC    = reg_make (MkBitsVec 0)
      1 sign     = reg_make (MkBitsVec 0)
      1 op       = reg_make (I2 LB)
      1 reg_idx  = reg_make (MkBitsVec 5)
      1 saved_pc = reg_make (MkBitsVec 0)
      1 ctx = (mem # reg # pc)  # (sign # op # reg_idx # saved_pc)
      
      MkLC xs ((mem' # reg' # pc') # (sign' # op' # reg_idx' # saved_pc'))
        = seq_eval rv32i $ MkLC (iterateN n (\() => ()) ()) ctx
        
      (MkBitsVec v) # reg'' = regf_read (the (BitsVec 5) (MkBitsVec 3)) reg'
      mem_value # mem'' = mem_read {n=32} (MkBitsVec 0x1000) mem'
      next_pc   # pc''  = reg_read pc'
      next_inst # mem3  = mem_read next_pc mem''
      () = consume pc''
      () = consume sign'
      () = consume op'
      () = consume reg_idx'
      () = consume saved_pc'
      () = consume mem3
      () = consume reg''
  in do putStrLn "================================================================================"
        putStrLn i_file
        if mem_value == MkBitsVec 0x11111111 
          then putStrLn "pass!"
          else do _ <- fPutStrLn stderr "Next inst:"
                  _ <- fPutStrLn stderr (show $ decode next_inst)
                  _ <- fPutStrLn stderr ("Value in gp (x3, Count of tests): " ++ (show v))
                  _ <- fPutStrLn stderr ("Value in x6: " ++ (show v6))
                  _ <- fPutStrLn stderr ("Value in x7: " ++ (show v7))
                  _ <- fPutStrLn stderr ("Value in x8: " ++ (show v8))
                  _ <- fPutStrLn stderr "fail!"
                  pure ()
        pure ()

main : IO ()
main = do args <- getArgs
          case args of
            _ :: (y :: (z :: [])) => eval y $ stringToNatOrZ z
            _ => do printLn "Invalid Arguments!"
                    pure ()
