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
      
bv_cast_32 : {n: _} -> BitsVec n -> BitsVec 32
bv_cast_32 = bv_get_range 0 32  

r_read_fn: LinContext (ROP, BitsVec 5, BitsVec 5, BitsVec 5, BitsVec 32) Context
        -@ LinContext (ROP, BitsVec 32, BitsVec 32, BitsVec 5, BitsVec 32) Context
r_read_fn (MkLC (op, rs1, rs2, rd, pc_) (mem # regf # pc)) = 
  let op1 # regf' = regf_read rs1 regf
      op2 # regf'' = regf_read rs2 regf'
  in MkLC (op, op1, op2, rd, pc_) (mem # regf'' # pc)
   
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
  
r_write_fn: LinContext (BitsVec 5, BitsVec 32, BitsVec 32) Context 
         -@ LinContext () Context 
r_write_fn (MkLC (rd, res, pc_) (mem # regf # pc)) 
  = (MkLC () (mem # regf_write rd res regf # reg_write pc_ pc))

i1_read_fn1: LinContext (IOP1, BitsVec 5, BitsVec 12, BitsVec 5, BitsVec 32) Context 
          -@ LinContext (IOP1, BitsVec 32, BitsVec 32, BitsVec 5, BitsVec 32) Context
i1_read_fn1 (MkLC (op, rs1, imm, rd, pc_) (mem # regf # pc)) =  
  let op1 # regf'   = regf_read rs1 regf
      imm'          = (bv_cast_32 . bv_sign_ext) imm
  in MkLC (op, op1, imm', rd, pc_) (mem # regf' # pc)

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
  
i2_read_fn1: LinContext (IOP2, BitsVec 5, BitsVec 12, BitsVec 5, BitsVec 32) Context 
          -@ LinContext (IOP2, BitsVec 32, BitsVec 32, BitsVec 5, BitsVec 32) Context
i2_read_fn1 (MkLC (op, rs1, imm, rd, pc_) (mem # regf # pc)) =  
  let op1 # regf'   = regf_read rs1 regf
      imm'          = (bv_cast_32 . bv_sign_ext) imm
  in MkLC (op, op1, imm', rd, pc_) (mem # regf' # pc)
      
i2_fn1 : (IOP2, BitsVec 32, BitsVec 32, BitsVec 5, BitsVec 32)
      -> (IOP2, BitsVec 32, BitsVec 5, BitsVec 32)
i2_fn1 (op, op1, imm, rd, pc_) = 
  let imm' = (bv_cast_32 $ bv_add op1 imm)
  in (op, imm', rd, pc_)
      
i2_read_fn2: LinContext (IOP2, BitsVec 32, BitsVec 5, BitsVec 32) Context
         -@ LinContext (IOP2, BitsVec 5, BitsVec 32, BitsVec 32) Context
i2_read_fn2 (MkLC (op, addr, rd, pc_) (mem # regf # pc)) =  
  let mem_data # mem' = mem_read addr mem
  in MkLC (op, rd, pc_, mem_data) (mem' # regf # pc)

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
      
i_write_fn: LinContext (BitsVec 5, BitsVec 32, BitsVec 32) Context
         -@ LinContext () Context
i_write_fn (MkLC (rd, res, pc_) (mem # regf # pc)) 
  = (MkLC () (mem # regf_write rd res regf # reg_write pc_ pc))

s_read_fn1: LinContext (SOP, BitsVec 5, BitsVec 5, BitsVec 12, BitsVec 32) Context
        -@ LinContext (SOP, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32) Context
s_read_fn1 (MkLC (op, rs1, rs2, imm, pc_) (mem # regf # pc)) =
  let op1 # regf'  = regf_read rs1 regf 
      op2 # regf'' = regf_read rs2 regf'
      imm'         = (bv_cast_32 . bv_sign_ext) imm
  in MkLC (op, op1, op2, imm', pc_) (mem # regf'' # pc)

s_read_fn2: LinContext (SOP, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32) Context
         -@ LinContext (SOP, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32) Context
s_read_fn2 (MkLC (op, op1, op2, imm, pc_) (mem # regf # pc)) =
  let addr = (bv_cast_32 $ op1 `bv_add` imm)
      mem_data # mem' = mem_read addr mem
  in MkLC (op, op2, pc_, addr, mem_data) (mem' # regf # pc)
                  
s_fn: (SOP, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32)
   -> (BitsVec 32, BitsVec 32, BitsVec 32)
s_fn (op, op2, pc_, addr, mem_data) = 
  let res = case op of 
        SB => bv_concatenate (bv_get_range 8 32 mem_data)  (bv_get_range 0 8 op2)
        SH => bv_concatenate (bv_get_range 16 32 mem_data) (bv_get_range 0 16 op2)
        SW => op2
      pc_  = (bv_cast_32 $ pc_ `bv_add` MkBitsVec 4)
  in (pc_, addr, res)
  
s_write_fn: LinContext (BitsVec 32, BitsVec 32, BitsVec 32) Context
         -@ LinContext () Context
s_write_fn (MkLC (pc_, addr, res) (mem # regf # pc)) 
  = (MkLC () (mem_write addr res mem # regf # reg_write pc_ pc))

b_read_fn : LinContext (BOP, BitsVec 5, BitsVec 5, BitsVec 13, BitsVec 32) Context 
         -@ LinContext (BOP, BitsVec 32, BitsVec 32, BitsVec 32, BitsVec 32) Context
b_read_fn (MkLC (op, rs1, rs2, imm, pc_) (mem # regf # pc)) = 
  let op1 # regf'  = regf_read rs1 regf 
      op2 # regf'' = regf_read rs2 regf'
      imm' = (bv_get_range 0 32 $ bv_sign_ext imm)
  in (MkLC (op, op1, op2, imm', pc_) (mem # regf'' # pc))
      
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
  
b_write_fn : LinContext (BitsVec 32) Context -@ LinContext () Context
b_write_fn (MkLC pc_ (mem # regf # pc))
  = (MkLC () (mem # regf # reg_write pc_ pc))
         
u_read_fn: LinContext (UOP, BitsVec 20, BitsVec 5, BitsVec 32) Context
        -@ LinContext (UOP, BitsVec 32, BitsVec 5, BitsVec 32) Context
u_read_fn (MkLC (op, imm, rd, pc_) (mem # regf # pc)) = 
  let imm' = bv_cast_32 $ bv_sll {m = 8} (bv_zero_ext imm) $ MkBitsVec 12
  in (MkLC (op, imm', rd, pc_) (mem # regf # pc))

u_fn : (UOP, BitsVec 32, BitsVec 5, BitsVec 32)
    -> (BitsVec 5, BitsVec 32, BitsVec 32)
u_fn (op, imm', rd, pc_) = 
  let res = case op of 
        LUI => imm'
        AUIPC => bv_get_range 0 32 $ bv_add pc_ imm'
      pc_' = (bv_cast_32 $ pc_ `bv_add` MkBitsVec 4)
  in (rd, res, pc_')
  
u_write_fn : LinContext (BitsVec 5, BitsVec 32, BitsVec 32) Context 
          -@ LinContext () Context
u_write_fn (MkLC (rd, res, pc_) (mem # regf # pc))
  = (MkLC () (mem # regf_write rd res regf # reg_write pc_ pc))

j_read_fn: LinContext (JOP, BitsVec 21, BitsVec 5, BitsVec 32) Context
        -@ LinContext (JOP, BitsVec 32, BitsVec 5, BitsVec 32) Context
j_read_fn (MkLC (op, imm, rd, pc_) (mem # regf # pc)) = 
  let imm' = (bv_cast_32 $ bv_sign_ext imm)
  in (MkLC (op, imm', rd, pc_) (mem # regf # pc))
    
j_fn: (JOP, BitsVec 32, BitsVec 5, BitsVec 32)
   -> (BitsVec 5, BitsVec 32, BitsVec 32)
j_fn  (op, imm, rd, pc_) = 
  let 
      pc_' = bv_cast_32 $ pc_ `bv_add` imm
      res  = bv_cast_32 $ pc_ `bv_add` MkBitsVec 4
  in (rd, res, pc_')
  
j_write_fn: LinContext (BitsVec 5, BitsVec 32, BitsVec 32) Context
         -@ LinContext () Context
j_write_fn (MkLC (rd, res, pc_) (mem # regf # pc)) 
  = MkLC () (mem # regf_write rd res regf # reg_write pc_ pc)

rv32i : LinContext () Context -@ LinContext () Context
rv32i (MkLC () (mem # regf # pc)) = 
  let pc_ # pc' = reg_read pc
      inst' # mem' = mem_read pc_ mem
      inst = decode inst'
      1 ctx' = mem' # regf # pc'
  in case inst of
          (R  op rs1 rs2 rd)  => r_write_fn 
                               . (r_fn >@ id) 
                               . r_read_fn 
                               $ MkLC (op, rs1, rs2, rd, pc_)  ctx'
                               
          (I1 op rs1 imm rd)  => i_write_fn 
                               . (i1_fn >@ id) 
                               . i1_read_fn1 
                               $ MkLC (op, rs1, imm, rd, pc_)  ctx'
                               
          (I2 op rs1 imm rd)  => i_write_fn 
                               . (i2_fn2 >@ id) 
                               . i2_read_fn2 
                               . (i2_fn1 >@ id) 
                               . i2_read_fn1 
                               $ MkLC (op, rs1, imm, rd, pc_)  ctx'
                               
          (S  op rs1 rs2 imm) => s_write_fn 
                               . (s_fn >@ id) 
                               . s_read_fn2 
                               . s_read_fn1 
                               $ MkLC (op, rs1, rs2, imm, pc_) ctx' 
                               
          (B  op rs1 rs2 imm) => b_write_fn 
                               . (b_fn >@ id) 
                               . b_read_fn 
                               $ MkLC (op, rs1, rs2, imm, pc_) ctx'
                               
          (U  op imm rd)      => u_write_fn 
                               . (u_fn >@ id) 
                               . u_read_fn 
                               $ MkLC (op, imm, rd, pc_) ctx'
                               
          (J  op imm rd)      => j_write_fn 
                               . (j_fn >@ id) 
                               . j_read_fn 
                               $ MkLC (op, imm, rd, pc_) ctx'
          _ => (MkLC () ctx')

eval: String -> Nat -> IO ()
eval i_file n = 
  let mem = mem_load i_file
      reg = mem_create (4*32)
      pc : PC = reg_make $ MkBitsVec 0
      1 ctx = (mem # reg # pc)
      MkLC xs (mem' # reg' # pc') = seq_eval rv32i $ MkLC (iterateN n (\() => ()) ()) ctx
      (MkBitsVec v) # reg'' = regf_read (the (BitsVec 5) (MkBitsVec 3)) reg'
      mem_value # mem'' = mem_read {n=32} (MkBitsVec 0x1000) mem'
      next_pc   # pc''  = reg_read pc'
      next_inst # mem3  = mem_read next_pc mem''
      () = consume mem3
      () = consume reg''
      () = consume pc''
  in do putStrLn "================================================================================"
        putStrLn i_file
        if mem_value == MkBitsVec 0x11111111 
          then putStrLn "pass!"
          else do
            _ <- fPutStrLn stderr "Next inst:"
            _ <- fPutStrLn stderr (show $ decode $ next_inst)
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
