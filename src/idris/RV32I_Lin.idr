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

ContextExt': Type
ContextExt' = LPair LinRegF
                    (LPair (LinReg $ BitsVec 1)       --sign
                   $ LPair (LinReg $ OP) -- op
                           (LPair (LinReg $ BitsVec 5) -- reg idx
                                  (LinReg $ BitsVec 32))) -- pc

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

cmp_fn: OP -> BitsVec 32 -> BitsVec 32 -> BitsVec 1
cmp_fn (B BNE)  op1 op2 = bv_neg $ bv_eq op1 op2
cmp_fn (B BLT)  op1 op2 = bv_lt op1 op2
cmp_fn (B BGE)  op1 op2 = bv_neg $ bv_lt op1 op2
cmp_fn (B BLTU) op1 op2 = bv_ltu op1 op2
cmp_fn (B BGEU) op1 op2 = bv_neg $ bv_ltu op1 op2
cmp_fn _  op1 op2 = bv_eq op1 op2

read_fn1: LinContext () (LPair LinMem PC)
          -@ LinContext (BitsVec 32, BitsVec 32) (LPair LinMem PC)
read_fn1 (MkLC () (mem # pc)) = 
  let addr     # pc'   = reg_read pc 
      mem_data # mem'  = mem_read addr mem
  in MkLC (addr, mem_data) (mem' # pc')

read_fn2: LinContext (BitsVec 32, BitsVec 32) ContextExt' 
       -@ LinContext 
            (OP, BitsVec 32, BitsVec 32, BitsVec 5, BitsVec 5, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 1) 
            ContextExt'
read_fn2 (MkLC (addr, mem_data) (regf # (sign # op # reg_idx # saved_pc))) = 
  let sign_    # sign' = reg_read sign
      pc_2     # saved_pc' = reg_read saved_pc
      pc_ = if (sign_ == (MkBitsVec 1)) then pc_2 else addr
      r'       # reg_idx' = reg_read reg_idx
      (MkInst opc1 rs1 rs2' rd imm) = decode mem_data
      rs2 = if (sign_ == (MkBitsVec 1)) then r' else rs2'
      opc2     # op'   = reg_read op
      op1      # regf' = regf_read rs1 regf
      op2      # regf'' = regf_read rs2 regf' 
      rd = if (sign_ == (MkBitsVec 1)) then r' else rd
      opc = if (sign_ == (MkBitsVec 1)) then opc2 else opc1
  in (MkLC (opc, op1, op2, rs2, rd, imm, pc_, addr, mem_data, sign_) 
           (regf'' # (sign' # op' # reg_idx' # saved_pc')))
                              
read_fn: LinContext () ContextExt
      -@ LinContext 
           (OP, BitsVec 32, BitsVec 32, BitsVec 5, BitsVec 5, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 1) 
           ContextExt
read_fn (MkLC () ((mem # regf # pc) # (sign # op # reg_idx # saved_pc))) = 
  let MkLC read_sig ((mem' # pc') # (regf' # (sign' # op' # reg_idx' # saved_pc'))) =
          (read_fn2 <<< read_fn1) 
        $ MkLC () $ (mem # pc) # (regf # (sign # op # reg_idx # saved_pc))
  in MkLC read_sig
          ((mem' # regf' # pc') # (sign' # op' # reg_idx' # saved_pc'))

mem_write_sig_gen: BitsVec 1 -> OP 
                -> (BitsVec 32, BitsVec 32) 
                -> (BitsVec 1, BitsVec 32, BitsVec 32)
mem_write_sig_gen (MkBitsVec 1) (S2 _) (addr, dat) = (MkBitsVec 1, addr, dat)
mem_write_sig_gen (MkBitsVec 0) (S1 _) (addr, dat) = (MkBitsVec 1, addr, dat)
mem_write_sig_gen _  _ (addr, dat) = (MkBitsVec 0, addr, dat)

write_mem_fn1: LinContext (BitsVec 1, BitsVec 32, BitsVec 32) LinMem
            -@ LinContext () LinMem
write_mem_fn1 (MkLC ((MkBitsVec 1), addr, dat) mem) = MkLC () $ mem_write addr dat mem
write_mem_fn1 (MkLC (_, addr, dat) mem) = MkLC () mem


write_mem_fn: BitsVec 1 -> OP 
           -> LinContext (BitsVec 32, BitsVec 32) LinMem
           -@ LinContext () LinMem
write_mem_fn sign_ opc = write_mem_fn1 . ((mem_write_sig_gen sign_ opc) >@ id)
           

write_regf_fn: BitsVec 1 -> OP 
           -> LinContext (BitsVec 5, BitsVec 32) LinRegF
           -@ LinContext () LinRegF
write_regf_fn (MkBitsVec 0) (I2 _) (MkLC (rd, dat) regf) = MkLC () $ regf
write_regf_fn _             (S2 _) (MkLC (rd, dat) regf) = MkLC () $ regf
write_regf_fn _             (B _)  (MkLC (rd, dat) regf) = MkLC () $ regf
write_regf_fn _             _      (MkLC (rd, dat) regf) = MkLC () $ regf_write rd dat regf

pc_sig_gen: BitsVec 1 -> OP 
         -> (BitsVec 32, BitsVec 32)
         -> BitsVec 32
pc_sig_gen (MkBitsVec 0) (S2 _) (pc_, r_addr) = r_addr
pc_sig_gen (MkBitsVec 0) (I2 _) (pc_, r_addr) = r_addr
pc_sig_gen _ _ (pc_, r_addr) = pc_

write_pc_fn1: LinContext (BitsVec 32) PC
           -@ LinContext () PC
write_pc_fn1 (MkLC pc_ pc) = MkLC () $ reg_write pc_ pc

write_pc_fn: BitsVec 1 -> OP 
          -> LinContext (BitsVec 32, BitsVec 32) PC
          -@ LinContext () PC
write_pc_fn sign_ opc = write_pc_fn1 . ((pc_sig_gen sign_ opc) >@ id)

-- (MkBitsVec 0) (S2 _) (MkLC (pc_, r_addr) pc) = MkLC () $ reg_write r_addr pc
-- write_pc_fn (MkBitsVec 0) (I2 _) (MkLC (pc_, r_addr) pc) = MkLC () $ reg_write r_addr pc
-- write_pc_fn _ _ (MkLC (pc_, r_addr) pc) = MkLC () $ reg_write pc_ pc

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

sel_reg_res : OP 
           -> (BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32)
           -> BitsVec 32
sel_reg_res (MERGED _ _)  (a_res, mem_data_r, pc_add_4, res_ui) = a_res
sel_reg_res (IJ _)        (a_res, mem_data_r, pc_add_4, res_ui) = pc_add_4
sel_reg_res (I2 _)        (a_res, mem_data_r, pc_add_4, res_ui) = mem_data_r
sel_reg_res (U _)         (a_res, mem_data_r, pc_add_4, res_ui) = res_ui
sel_reg_res (J _)         (a_res, mem_data_r, pc_add_4, res_ui) = pc_add_4
sel_reg_res _ _ = MkBitsVec 0

sel_pc: OP -> BitsVec 1 -> BitsVec 1
     -> (BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32)
     -> BitsVec 32
sel_pc (IJ _) _             _             (pc_, pc_add_4, pc_imm, op1_imm) = op1_imm
sel_pc (B op) _             (MkBitsVec 1) (pc_, pc_add_4, pc_imm, op1_imm) = pc_imm
sel_pc (B op) _             _             (pc_, pc_add_4, pc_imm, op1_imm) = pc_add_4
sel_pc (J  _) _             _             (pc_, pc_add_4, pc_imm, op1_imm) = pc_imm
sel_pc (I2 _) (MkBitsVec 0) _             (pc_, pc_add_4, pc_imm, op1_imm) = pc_
sel_pc (S2 _) (MkBitsVec 0) _             (pc_, pc_add_4, pc_imm, op1_imm) = pc_
sel_pc _ _ _                              (pc_, pc_add_4, pc_imm, op1_imm) = pc_add_4

sel_w_addr: OP 
         -> (BitsVec 32, BitsVec 32)
         -> BitsVec 32
sel_w_addr (S1 _) (op1_imm, addr) = op1_imm
sel_w_addr _      (op1_imm, addr) = addr

sel_w_dat: OP
        -> (BitsVec 32, BitsVec 32)
        -> BitsVec 32
sel_w_dat (S1 _)  (op2, mem_data_w) = op2
sel_w_dat (S2 _)  (op2, mem_data_w) = mem_data_w
sel_w_dat _ _ = MkBitsVec 0

sel_a_op2: OP -> (BitsVec 32 , BitsVec 32) -> BitsVec 32
sel_a_op2 (MERGED RR _) (op2, imm) = op2
sel_a_op2 _             (op2, imm) = imm

sel_a_opc: OP -> AOP
sel_a_opc (MERGED _ op) = op
sel_a_opc _ = ADD

sel_res_ui: OP -> (BitsVec 32, BitsVec 32) -> BitsVec 32
sel_res_ui (U LUI) (imm, pc_imm) = imm
sel_res_ui _       (imm, pc_imm) = pc_imm

sel_b_opc: OP -> BOP
sel_b_opc (B op) = op
sel_b_opc _ = BLT

sel_mem_data_w: OP -> (BitsVec 32, BitsVec 32) -> BitsVec 32
sel_mem_data_w (S2 SB) (b, h) = b
sel_mem_data_w _       (b, h) = h

get_mem_data_w: OP -> BitsVec 32 -> BitsVec 32 -> BitsVec 32
get_mem_data_w opc op2 mem_data = 
  let mem_data_w_b = bv_compose_b op2 mem_data                    
      mem_data_w_h = bv_compose_h op2 mem_data                    
  in sel_mem_data_w opc (mem_data_w_b, mem_data_w_h)
  
sel_mem_data_r: OP -> (BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32) -> BitsVec 32
sel_mem_data_r (I2 LB)  (mem_data, mem_data_r_sb, mem_data_r_sh, mem_data_r_ub, mem_data_r_uh) = mem_data_r_sb
sel_mem_data_r (I2 LH)  (mem_data, mem_data_r_sb, mem_data_r_sh, mem_data_r_ub, mem_data_r_uh) = mem_data_r_sh
sel_mem_data_r (I2 LBU) (mem_data, mem_data_r_sb, mem_data_r_sh, mem_data_r_ub, mem_data_r_uh) = mem_data_r_ub
sel_mem_data_r (I2 LHU) (mem_data, mem_data_r_sb, mem_data_r_sh, mem_data_r_ub, mem_data_r_uh) = mem_data_r_uh
sel_mem_data_r _        (mem_data, mem_data_r_sb, mem_data_r_sh, mem_data_r_ub, mem_data_r_uh) = mem_data

get_mem_data_r: OP -> BitsVec 32 -> BitsVec 32
get_mem_data_r opc mem_data = 
  let mem_data_r_sb = bv_get_lower_sb mem_data
      mem_data_r_sh = bv_get_lower_sh mem_data
      mem_data_r_ub = bv_get_lower_ub mem_data
      mem_data_r_uh = bv_get_lower_uh mem_data
  in sel_mem_data_r opc (mem_data, mem_data_r_sb, mem_data_r_sh, mem_data_r_ub, mem_data_r_uh)
  
arith_u: OP -> BitsVec 32 -> BitsVec 32 -> BitsVec 32 -> BitsVec 32
arith_u opc op1 op2 imm = 
  let a_op2      = sel_a_op2 opc (op2, imm)
      a_opc      = sel_a_opc opc
  in arith a_opc (op1, a_op2)

rv32i : LinContext () ContextExt -@ LinContext () ContextExt
rv32i (MkLC () ctx) = 
  let MkLC (opc, op1, op2, rs2, rd, imm, pc_, addr, mem_data, sign_) ctx' 
        = read_fn (MkLC () ctx)
        
      pc_add_4   = pc_ `bv_add_32` (MkBitsVec 4)
      pc_imm     = pc_ `bv_add_32` imm
      op1_imm    = op1 `bv_add_32` imm
      a_res      = arith_u opc op1 op2 imm
      res_ui     = sel_res_ui opc (imm, pc_imm)
      cmp        = cmp_fn opc op1 op2
      mem_data_w = get_mem_data_w opc op2 mem_data
      mem_data_r = get_mem_data_r opc mem_data
      
      res        = sel_reg_res opc (a_res, mem_data_r, pc_add_4, res_ui)
      pc_'       = sel_pc opc sign_ cmp (pc_, pc_add_4, pc_imm, op1_imm)
      w_addr     = sel_w_addr opc (op1_imm, addr)
      w_dat      = sel_w_dat opc (op2, mem_data_w)
      
  in write_fn sign_ opc $ MkLC ((w_addr, w_dat), (rd, res), (pc_', op1_imm), rs2) ctx'

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
