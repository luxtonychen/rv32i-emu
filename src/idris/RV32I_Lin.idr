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
   
r_fn: (ROP, BitsVec 32, BitsVec 32, BitsVec 5, BitsVec 32)
   -> (BitsVec 5, BitsVec 32, BitsVec 32)
r_fn (op, op1, op2, rd, pc_) = 
  let res = case op of
                 ADD  => bv_cast_32 . uncurry bv_add $ (op1, op2) 
                 SUB  => bv_cast_32 . uncurry bv_sub $ (op1, op2)
                 XOR  => uncurry bv_xor $ (op1, op2)
                 OR   => uncurry bv_or  $ (op1, op2)           
                 AND  => uncurry bv_and $ (op1, op2)            
                 SLL  => uncurry bv_sll $ (op1, op2)            
                 SRL  => uncurry bv_srl $ (op1, op2)            
                 SRA  => uncurry bv_sra $ (op1, op2)            
                 SLT  => bv_cast_32  . uncurry bv_lt  $ (op1, op2)
                 SLTU => bv_cast_32  . uncurry bv_ltu $ (op1, op2)
      pc_' = bv_cast_32 $ bv_add (MkBitsVec 4) pc_
  in (rd, res, pc_')
  
r_write_fn: LinContext (BitsVec 5, BitsVec 32, BitsVec 32) ContextExt
         -@ LinContext () ContextExt
r_write_fn (MkLC (rd, res, pc_) $ (mem # regf # pc) # rest) 
  = MkLC () $ (mem # regf_write rd res regf # reg_write pc_ pc) # rest


i1_fn: (IOP1, BitsVec 32, BitsVec 32, BitsVec 5, BitsVec 32)
    -> (BitsVec 5, BitsVec 32, BitsVec 32)
i1_fn (op, op1, imm, rd, pc_) = 
  let res = case op of
        ADDI  => bv_cast_32 $ bv_add op1 imm
        XORI  => bv_cast_32 $ bv_xor op1 imm
        ORI   => bv_cast_32 $ bv_or  op1 imm
        ANDI  => bv_cast_32 $ bv_and op1 imm
        SLLI  => bv_cast_32 $ bv_sll op1 $ bv_get_range 0 5 imm
        SRLI  => bv_cast_32 $ bv_srl op1 $ bv_get_range 0 5 imm
        SRAI  => bv_cast_32 $ bv_sra op1 $ bv_get_range 0 5 imm
        SLTI  => bv_cast_32 $ bv_lt  op1 imm
        SLTIU => bv_cast_32 $ bv_ltu op1 imm
        JALR  => bv_cast_32 $ pc_ `bv_add` MkBitsVec 4
      pc_' = case op of
        JALR => bv_cast_32 $ bv_add op1 imm
        _    => bv_cast_32 $ pc_ `bv_add` MkBitsVec 4
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
      
i_write_fn: LinContext (BitsVec 5, BitsVec 32, BitsVec 32) ContextExt
         -@ LinContext () ContextExt
i_write_fn (MkLC (rd, res, pc_) $ (mem # regf # pc) # (sign # rest))
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

-- s2_read_fn2: LinContext (SOP2, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32) ContextExt
--           -@ LinContext (SOP2, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32) ContextExt
-- s2_read_fn2 (MkLC (op, op2, pc_, addr, mem_data) ((mem # regf # pc) # (sign # saved_op # saved_reg_idx # saved_pc))) = MkLC (op, op2, pc_, addr, mem_data) 
--             $ (mem # regf # pc) # (sign # saved_op # saved_reg_idx # saved_pc)

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

      
b_fn : (BOP, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32)-> (BitsVec 32)
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

rv32i : LinContext () ContextExt -@ LinContext () ContextExt
rv32i (MkLC () ctx) = 
  let MkLC (opc, op1, op2, rs2, rd, imm, pc_, addr, mem_data, sign_) ctx' 
        = read_fn (MkLC () ctx)
  in if (sign_ == (MkBitsVec 1))
     then case opc of 
            (I2 op)  => i_write_fn 
                      . (i2_fn2 >@ id) 
                      $ MkLC (op, rd, pc_, mem_data) ctx'
                       
            (S2 op) => s_write_fn 
                     . (s2_fn2 >@ id) 
                     $ MkLC (op, op2, pc_, addr, mem_data) ctx' -- <- to break to two stage
                     
            _ => MkLC () ctx'
            
     else case (opc) of
            (R op) => r_write_fn 
                    . (r_fn >@ id) 
                    $ MkLC (op, op1, op2, rd, pc_)  ctx'
                  
            (I1 op) => i_write_fn 
                     . (i1_fn >@ id)  
                     $ MkLC (op, op1, imm, rd, pc_)  ctx'
                  
            (I2 op) => i2_write_fn1
                     . (i2_fn1 >@ id) 
                     $ MkLC (op, op1, imm, rd, pc_)  ctx'
                  
            (S1 op) => s_write_fn 
                     . (s1_fn >@ id)
                     $ MkLC (op, op1, op2, imm, pc_) ctx' 
            
            (S2 op) => s2_write_fn1 -- <-
                     . (s2_fn1 >@ id)
                     $ MkLC (op, op1, rs2, imm, pc_) ctx' 
                             
            (B op)  => b_write_fn 
                     . (b_fn >@ id) 
                     $ MkLC (op, op1, op2, imm, pc_) ctx'
                    
            (U op)  => u_write_fn 
                     . (u_fn >@ id) 
                     $ MkLC (op, imm, rd, pc_) ctx'
                  
            (J op)  => j_write_fn 
                     . (j_fn >@ id) 
                     $ MkLC (op, imm, rd, pc_) ctx'
                    
            _ => (MkLC () ctx')

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
      () = consume mem3
      () = consume reg''
      () = consume pc''
      () = consume sign'
      () = consume op'
      () = consume reg_idx'
      () = consume saved_pc'
  in do putStrLn "================================================================================"
        putStrLn i_file
        if mem_value == MkBitsVec 0x11111111 
          then putStrLn "pass!"
          else do
            _ <- fPutStrLn stderr "Next inst:"
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
