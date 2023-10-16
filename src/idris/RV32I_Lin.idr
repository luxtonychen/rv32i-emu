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

b_fn1: BOP -> BitsVec 32 -> BitsVec 32 -> BitsVec 1
b_fn1 BEQ  op1 op2 = bv_eq op1 op2
b_fn1 BNE  op1 op2 = bv_neg $ bv_eq op1 op2
b_fn1 BLT  op1 op2 = bv_lt op1 op2
b_fn1 BGE  op1 op2 = bv_neg $ bv_lt op1 op2
b_fn1 BLTU op1 op2 = bv_ltu op1 op2
b_fn1 BGEU op1 op2 = bv_neg $ bv_ltu op1 op2

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

res_fn : OP 
      -> (BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32)
      -> BitsVec 32
res_fn (MERGED RR op) (a_op1_op2, a_op1_imm, mem_data, pc_add_4, res_ui) = a_op1_op2
res_fn (MERGED RI op) (a_op1_op2, a_op1_imm, mem_data, pc_add_4, res_ui) = a_op1_imm
res_fn (IJ op) (a_op1_op2, a_op1_imm, mem_data, pc_add_4, res_ui) = pc_add_4
res_fn (I2 op) (a_op1_op2, a_op1_imm, mem_data, pc_add_4, res_ui) = 
  case op of
    LB  => bv_cast_32 $ bv_sign_ext $ bv_get_range 0 8 mem_data 
    LH  => bv_cast_32 $ bv_sign_ext $ bv_get_range 0 16 mem_data
    LW  => mem_data                                             
    LBU => bv_cast_32 $ bv_zero_ext $ bv_get_range 0 8 mem_data 
    LHU => bv_cast_32 $ bv_zero_ext $ bv_get_range 0 16 mem_data
res_fn (U op) (a_op1_op2, a_op1_imm, mem_data, pc_add_4, res_ui) = res_ui
res_fn (J op) (a_op1_op2, a_op1_imm, mem_data, pc_add_4, res_ui) = pc_add_4
res_fn _ _ = MkBitsVec 0

pc_fn: OP -> BitsVec 1 -> BitsVec 1
    -> (BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32)
    -> BitsVec 32
pc_fn (IJ _) _             _             (pc_, pc_add_4, pc_imm, op1_imm) = op1_imm
pc_fn (B op) _             (MkBitsVec 1) (pc_, pc_add_4, pc_imm, op1_imm) = pc_imm
pc_fn (B op) _             _             (pc_, pc_add_4, pc_imm, op1_imm) = pc_add_4
pc_fn (J  _) _             _             (pc_, pc_add_4, pc_imm, op1_imm) = pc_imm
pc_fn (I2 _) (MkBitsVec 0) _             (pc_, pc_add_4, pc_imm, op1_imm) = pc_
pc_fn (S2 _) (MkBitsVec 0) _             (pc_, pc_add_4, pc_imm, op1_imm) = pc_
pc_fn _ _ _                              (pc_, pc_add_4, pc_imm, op1_imm) = pc_add_4

r_addr_fn: OP 
        -> BitsVec 32
        -> BitsVec 32
r_addr_fn (I2 _) op1_imm = op1_imm
r_addr_fn (S2 _) op1_imm = op1_imm
r_addr_fn _ _ = MkBitsVec 0

w_addr_fn: OP 
        -> (BitsVec 32, BitsVec 32)
        -> BitsVec 32
w_addr_fn (S1 _) (op1_imm, addr) = op1_imm
w_addr_fn _      (op1_imm, addr) = addr

w_dat_fn: OP
       -> (BitsVec 32, BitsVec 32)
       -> BitsVec 32
w_dat_fn (S1 _)  (op2, mem_data) = op2
w_dat_fn (S2 op) (op2, mem_data) = 
  case op of
    SB => bv_concatenate (bv_get_range 8 32 mem_data)  (bv_get_range 0 8 op2)
    SH => bv_concatenate (bv_get_range 16 32 mem_data) (bv_get_range 0 16 op2)
w_dat_fn _ _ = MkBitsVec 0

pc_inc : BitsVec 32 -> BitsVec 32
pc_inc pc_ = bv_cast_32 $ bv_add pc_ (MkBitsVec 4)

bv_add_32: BitsVec 32 -> BitsVec 32 -> BitsVec 32
bv_add_32 x y = bv_cast_32 $ x `bv_add` y

rv32i : LinContext () ContextExt -@ LinContext () ContextExt
rv32i (MkLC () ctx) = 
  let MkLC (opc, op1, op2, rs2, rd, imm, pc_, addr, mem_data, sign_) ctx' 
        = read_fn (MkLC () ctx)
        
      pc_add_4 = pc_inc pc_
      pc_imm   = pc_ `bv_add_32` imm
      op1_imm  = op1 `bv_add_32` imm
        
      a_op1_op2 = case opc of
                    (MERGED RR op) => arith op (op1, op2)
                    _ => MkBitsVec 0
                    
      a_op1_imm = case opc of
                    (MERGED RI op) => arith op (op1, imm)
                    _ => MkBitsVec 0
                    
      res_ui = case opc of 
                 (U LUI) => imm
                 (U AUIPC) => pc_imm
                 _ => MkBitsVec 0
                    
      cmp = case opc of
              (B op) => b_fn1 op op1 op2
              _ => MkBitsVec 0
      
      res = res_fn opc (a_op1_op2, a_op1_imm, mem_data, pc_add_4, res_ui)
        
      pc_' = pc_fn opc sign_ cmp (pc_, pc_add_4, pc_imm, op1_imm)
        
      r_addr = r_addr_fn opc op1_imm

      w_addr = w_addr_fn opc (op1_imm, addr)
        
      w_dat  = w_dat_fn opc (op2, mem_data)
      
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
                  _ <- fPutStrLn stderr "fail!"
                  pure ()
        pure ()

main : IO ()
main = do args <- getArgs
          case args of
            _ :: (y :: (z :: [])) => eval y $ stringToNatOrZ z
            _ => do printLn "Invalid Arguments!"
                    pure ()
