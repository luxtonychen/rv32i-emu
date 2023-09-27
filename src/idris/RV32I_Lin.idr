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

PC : Type
PC = LinReg (BitsVec 32)

record Context where
  constructor MkContext
  1 mem  : LinMem
  1 regf : LinRegF
  1 pc   : PC
  
bv_cast_32 : {n: _} -> BitsVec n -> BitsVec 32
bv_cast_32 = bv_get_range 0 32  

r_fn : LinContext (ROP, BitsVec 5, BitsVec 5, BitsVec 5) Context -@ LinContext () Context
r_fn (MkLC (op, rs1, rs2, rd) (MkContext mem regf pc)) = 
  let op1 # regf'  = regf_read rs1 regf 
      op2 # regf'' = regf_read rs2 regf'
      pc_ # pc' = reg_read pc 
      res = case op of
        ADD =>  bv_cast_32 $ op1 `bv_add` op2
        SUB =>  bv_cast_32 $ op1 `bv_sub` op2
        XOR =>  bv_cast_32 $ op1 `bv_xor` op2
        OR  =>  bv_cast_32 $ op1 `bv_or`  op2
        AND =>  bv_cast_32 $ op1 `bv_and` op2
        SLL =>  bv_cast_32 $ op1 `bv_sll` op2
        SRL =>  bv_cast_32 $ op1 `bv_srl` op2
        SRA =>  bv_cast_32 $ op1 `bv_sra` op2
        SLT =>  bv_cast_32 $ op1 `bv_lt`  op2
        SLTU => bv_cast_32 $ op1 `bv_ltu` op2
      regf''' = regf_write rd res regf''
      pc''   = reg_write (bv_cast_32 $ pc_ `bv_add` (MkBitsVec 4)) pc'
  in MkLC () (MkContext mem regf''' pc'')

i_fn : LinContext (IOP, BitsVec 5, BitsVec 12, BitsVec 5) Context -@ LinContext () Context
i_fn (MkLC (op, rs1, imm, rd) (MkContext mem regf pc)) = 
  let op1 # regf' = regf_read rs1 regf
      op2 = bv_get_range 0 32 $ bv_sign_ext imm
      pc_ # pc' = reg_read pc 
      mem_data # mem' = mem_read (bv_get_range 0 32 $ bv_add op1 op2) mem
      res = case op of
        ADDI  => bv_cast_32 $ bv_add op1 op2
        XORI  => bv_cast_32 $ bv_xor op1 op2
        ORI   => bv_cast_32 $ bv_or  op1 op2
        ANDI  => bv_cast_32 $ bv_and op1 op2
        SLLI  => bv_cast_32 $ bv_sll op1 $ bv_get_range 0 5 op2
        SRLI  => bv_cast_32 $ bv_srl op1 $ bv_get_range 0 5 op2
        SRAI  => bv_cast_32 $ bv_sra op1 $ bv_get_range 0 5 op2
        SLTI  => bv_cast_32 $ bv_lt  op1 op2
        SLTIU => bv_cast_32 $ bv_ltu op1 op2
        LB    => bv_cast_32 $ bv_sign_ext $ bv_get_range 0 8 mem_data
        LH    => bv_cast_32 $ bv_sign_ext $ bv_get_range 0 16 mem_data
        LW    => mem_data
        LBU   => bv_cast_32 $ bv_zero_ext $ bv_get_range 0 8 mem_data
        LHU   => bv_cast_32 $ bv_zero_ext $ bv_get_range 0 16 mem_data
        JALR  => bv_cast_32 $ pc_ `bv_add` MkBitsVec 4
      pc_' = case op of
        JALR => bv_cast_32 $ bv_add op1 op2
        _    => bv_cast_32 $ pc_ `bv_add` MkBitsVec 4
      regf'' = regf_write rd res regf'
      pc''   = reg_write pc_' pc'
  in MkLC () $ MkContext mem' regf'' pc''
  
s_fn : LinContext (SOP, BitsVec 5, BitsVec 5, BitsVec 12) Context -@ LinContext () Context
s_fn (MkLC (op, rs1, rs2, imm) (MkContext mem regf pc)) = 
  let op1 # regf'  = regf_read rs1 regf 
      op2 # regf'' = regf_read rs2 regf'
      pc_ # pc'    = reg_read pc
      addr = bv_get_range 0 32 $ op1 `bv_add` (bv_get_range 0 32 $ bv_sign_ext imm)
      mem_data # mem' = mem_read_word addr mem
      res = case op of 
        SB => bv_concatenate (bv_get_range 8 32 mem_data)  (bv_get_range 0 8 op2)
        SH => bv_concatenate (bv_get_range 16 32 mem_data) (bv_get_range 0 16 op2)
        SW => op2
      pc''  = reg_write (bv_cast_32 $ pc_ `bv_add` MkBitsVec 4) pc'
      mem'' = mem_write_word addr res mem'
  in MkLC () $ MkContext mem'' regf'' pc''
  
b_fn : LinContext (BOP, BitsVec 5, BitsVec 5, BitsVec 13) Context -@ LinContext () Context
b_fn (MkLC (op, rs1, rs2, imm) (MkContext mem regf pc)) = 
  let op1 # regf'  = regf_read rs1 regf
      op2 # regf'' = regf_read rs2 regf'
      pc_ # pc'    = reg_read pc
      b = case op of 
        BEQ  => (bv_lt op1 op2)  == (bv_lt op2 op1)
        BNE  => (bv_lt op1 op2)  /= (bv_lt op2 op1)
        BLT  => (bv_lt op1 op2)  == (MkBitsVec 1)
        BGE  => (bv_lt op1 op2)  /= (MkBitsVec 1)
        BLTU => (bv_ltu op1 op2) == (MkBitsVec 1)
        BGEU => (bv_ltu op1 op2) /= (MkBitsVec 1)
      pc_' = if b then bv_get_range 0 32 $ pc_ `bv_add` (bv_get_range 0 32 $ bv_sign_ext imm)
                  else bv_get_range 0 32 $ pc_ `bv_add` MkBitsVec 4
      pc'' = reg_write pc_' pc'
  in MkLC () $ MkContext mem regf'' pc''
  
u_fn : LinContext (UOP, BitsVec 20, BitsVec 5) Context -@ LinContext () Context
u_fn (MkLC (op, imm, rd) (MkContext mem regf pc)) = 
  let imm' = bv_get_range 0 32 $ bv_sll {m = 8} (bv_zero_ext imm) $ MkBitsVec 12
      pc_ # pc' = reg_read pc
      res = case op of 
        LUI => imm'
        AUIPC => bv_get_range 0 32 $ bv_add pc_ imm'
      regf' = regf_write rd res regf
      pc'' = reg_write (bv_get_range 0 32 $ pc_ `bv_add` MkBitsVec 4) pc'
  in MkLC () (MkContext mem regf' pc'')
  
j_fn : LinContext (JOP, BitsVec 21, BitsVec 5) Context -@ LinContext () Context
j_fn  (MkLC (op, imm, rd) (MkContext mem regf pc)) = 
  let pc_ # pc' = reg_read pc
      pc_' = bv_get_range 0 32 $ pc_ `bv_add` (bv_get_range 0 32 $ bv_sign_ext imm)
      pc'' = reg_write pc_' pc'
      regf' = regf_write rd (bv_get_range 0 32 $ pc_ `bv_add` MkBitsVec 4) regf
  in MkLC () (MkContext mem regf' pc'')

rv32i : LinContext () Context -@ LinContext () Context
rv32i (MkLC () (MkContext mem regf pc)) = 
  let pc_ # pc' = reg_read pc
      inst' # mem' = mem_read pc_ mem
      inst = decode inst'
      1 ctx' = MkContext mem' regf pc'
  in case inst of
          (R op rs1 rs2 rd)  => r_fn (MkLC (op, rs1, rs2, rd)  ctx')
          (I op rs1 imm rd)  => i_fn (MkLC (op, rs1, imm, rd)  ctx')
          (S op rs1 rs2 imm) => s_fn (MkLC (op, rs1, rs2, imm) ctx') 
          (B op rs1 rs2 imm) => b_fn (MkLC (op, rs1, rs2, imm) ctx') 
          (U op imm rd)      => u_fn (MkLC (op, imm, rd) ctx') 
          (J op imm rd)      => j_fn (MkLC (op, imm, rd) ctx')
          _ => (MkLC () ctx')

eval: String -> Nat -> IO ()
eval i_file n = 
  let mem = mem_load i_file
      reg = mem_create (4*32)
      pc : PC = reg_make $ MkBitsVec 0
      1 ctx = MkContext mem reg pc
      MkLC xs (MkContext mem' reg' pc') = seq_eval rv32i $ MkLC (iterateN n (\() => ()) ()) ctx
      count     # reg'' = regf_read (the (BitsVec 5) (MkBitsVec 3)) reg'
      mem_value # mem'' = mem_read {n=32} (MkBitsVec 0x1000) mem'
      next_pc   # pc''  = reg_read pc'
      next_inst # mem3  = mem_read next_pc mem''
      () = consume mem3
      () = consume reg''
      () = consume pc''
      (ofile, ostr, oval) : (_, _, Int) = if mem_value == MkBitsVec 0x11111111 
                                          then (stdout, "pass!", 0) 
                                          else (stderr, "fail!", 1)
  in do putStrLn i_file
        putStrLn "Next inst:"
        printLn $ decode $ next_inst
        case count of
          MkBitsVec v => putStrLn ("Value in gp (x3, Count of tests): " ++ (show v))
        _ <- fPutStrLn ofile ostr
        pure ()

main : IO ()
main = do args <- getArgs
          case args of
            _ :: (y :: (z :: [])) => eval y $ stringToNatOrZ z
            _ => do printLn "Invalid Arguments!"
                    pure ()
