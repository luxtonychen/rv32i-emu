import BitsVec
import Mem
import RegFile
import RV32I_Inst
import Data.Stream
import Data.List
import Data.List1
import Data.Nat

record Context where
  constructor MkContext
  mem  : MemTy
  regf : RegFile
  pc   : BitsVec

update_context : MemTy -> RegFile -> BitsVec -> IO Context 
update_context mem regf pc = pure $ MkContext mem regf pc

pc_inc : BitsVec -> BitsVec
pc_inc pc = bv_get_range 0 32 $ bv_add pc (MkBitsVec 32 4)

r_fn : ((ROP, BitsVec, BitsVec, BitsVec), Context) -> ((), IO Context)
r_fn ((op, rs1, rs2, rd), (MkContext mem regf pc)) = 
  let op1 = regf_read rs1 regf
      op2 = regf_read rs2 regf
      res = case op of
        ADD =>  bv_get_range 0 32 $ bv_add op1 op2
        SUB =>  bv_get_range 0 32 $ bv_sub op1 op2
        XOR =>  bv_get_range 0 32 $ bv_xor op1 op2
        OR  =>  bv_get_range 0 32 $ bv_or  op1 op2
        AND =>  bv_get_range 0 32 $ bv_and op1 op2
        SLL =>  bv_get_range 0 32 $ bv_sll op1 op2
        SRL =>  bv_get_range 0 32 $ bv_srl op1 op2
        SRA =>  bv_get_range 0 32 $ bv_sra op1 op2
        SLT =>  bv_get_range 0 32 $ bv_lt  op1 op2
        SLTU => bv_get_range 0 32 $ bv_ltu op1 op2
      regf' = regf_write' rd res regf
      pc'   = pc_inc pc
  in ((), regf' >>= (\x => update_context mem x pc'))

i_fn : ((IOP, BitsVec, BitsVec, BitsVec), Context) -> ((), IO Context)
i_fn ((op, rs1, imm, rd), (MkContext mem regf pc)) = 
  let op1 = regf_read rs1 regf
      op2 = imm
      mem_data = mem_read_word (bv_get_range 0 32 $ bv_add op1 op2) mem
      res = case op of
        ADDI  => bv_get_range 0 32 $ bv_add op1 op2
        XORI  => bv_get_range 0 32 $ bv_xor op1 op2
        ORI   => bv_get_range 0 32 $ bv_or  op1 op2
        ANDI  => bv_get_range 0 32 $ bv_and op1 op2
        SLLI  => bv_get_range 0 32 $ bv_sll op1 $ bv_get_range 0 5 op2
        SRLI  => bv_get_range 0 32 $ bv_srl op1 $ bv_get_range 0 5 op2
        SRAI  => bv_get_range 0 32 $ bv_sra op1 $ bv_get_range 0 5 op2
        SLTI  => bv_get_range 0 32 $ bv_lt  op1 op2
        SLTIU => bv_get_range 0 32 $ bv_ltu op1 op2
        LB    => bv_get_range 0 32 $ bv_sign_ext $ bv_get_range 0 8 mem_data
        LH    => bv_get_range 0 32 $ bv_sign_ext $ bv_get_range 0 16 mem_data
        LW    => mem_data
        LBU   => bv_get_range 0 32 $ bv_zero_ext $ bv_get_range 0 8 mem_data
        LHU   => bv_get_range 0 32 $ bv_zero_ext $ bv_get_range 0 16 mem_data
        JALR  => pc_inc pc
      pc' = case op of
        JALR => bv_add op1 $ bv_get_range 0 32 $ bv_sign_ext op2
        _    => pc_inc pc
      regf' = regf_write' rd res regf
  in ((), regf' >>= (\x => update_context mem x pc'))
  
s_fn : ((SOP, BitsVec, BitsVec, BitsVec), Context) -> ((), IO Context)
s_fn ((op, rs1, rs2, imm), (MkContext mem regf pc)) = 
  let op1 = regf_read rs1 regf
      op2 = regf_read rs2 regf
      addr = bv_get_range 0 32 $ bv_add op1 imm
      mem_data = mem_read_word addr mem
      res = case op of 
        SB => bv_concatenate (bv_get_range 8 32 mem_data)  (bv_get_range 0 8 op2)
        SH => bv_concatenate (bv_get_range 16 32 mem_data) (bv_get_range 0 16 op2)
        SW => op2
      pc' = pc_inc pc
      mem' = mem_write_word' addr res mem
  in ((), mem' >>= (\x => update_context x regf pc'))

b_fn : ((BOP, BitsVec, BitsVec, BitsVec), Context) -> ((), IO Context)
b_fn ((op, rs1, rs2, imm), (MkContext mem regf pc)) = 
  let op1 = regf_read rs1 regf
      op2 = regf_read rs2 regf
      b = case op of 
        BEQ => (bv_lt op1 op2) == (bv_lt op2 op1)
        BNE => (bv_lt op1 op2) /= (bv_lt op2 op1)
        BLT => (bv_lt op1 op2) == (MkBitsVec 1 1)
        BGE => (bv_lt op1 op2) /= (MkBitsVec 1 1)
        BLTU => (bv_ltu op1 op2) == (MkBitsVec 1 1)
        BGEU => (bv_ltu op1 op2) /= (MkBitsVec 1 1)
      pc' = if b then bv_get_range 0 32 $ bv_add pc imm
                 else pc_inc pc
  in ((), update_context mem regf pc')

u_fn : ((UOP, BitsVec, BitsVec), Context) -> ((), IO Context)
u_fn ((op, imm, rd), (MkContext mem regf pc)) = 
  let imm' = bv_get_range 0 32 $ bv_sll (bv_zero_ext imm) $ MkBitsVec 8 12
      res = case op of 
        LUI => imm'
        AUIPC => bv_get_range 0 32 $ bv_add pc imm'
      regf' = regf_write' rd res regf
      pc' = pc_inc pc
  in ((), regf' >>= (\x => update_context mem x pc'))

j_fn : ((JOP, BitsVec, BitsVec), Context) -> ((), IO Context)
j_fn  ((op, imm, rd), (MkContext mem regf pc)) = 
  let pc' = bv_get_range 0 32 $ bv_add pc $ bv_get_range 0 32 $ bv_sign_ext imm
      regf' = regf_write' rd (pc_inc pc) regf
  in ((), regf' >>= (\x => update_context mem x pc'))

rv32i_fwd : ((), Context) -> ((), IO Context)
rv32i_fwd ((), context) = 
  let (MkContext mem regf pc) = context
      inst = decode $ mem_read_word pc mem 
  in case inst of
          (R op rs1 rs2 rd)  => r_fn ((op, rs1, rs2, rd), context)
          (I op rs1 imm rd)  => i_fn ((op, rs1, imm, rd), context)
          (S op rs1 rs2 imm) => s_fn ((op, rs1, rs2, imm), context) 
          (B op rs1 rs2 imm) => b_fn ((op, rs1, rs2, imm), context) 
          (U op imm rd)      => u_fn ((op, imm, rd), context) 
          (J op imm rd)      => j_fn ((op, imm, rd), context)
          _ => ((), pure context)

run_n : (n : Nat) -> (ctx : Context) -> IO Context
run_n 0 ctx = pure ctx
run_n (S k) ctx = (snd . rv32i_fwd) ((), ctx) >>= (run_n k)

main : (n: Nat) -> String -> IO()
main n i_file = 
  let mem  = mem_load $ i_file
      regs = mem_create (4*32)
      pc = MkBitsVec 32 0
  in do 
        (MkContext mem' regs' pc') <- run_n n (MkContext mem regs pc)
        _ <- mem_save ((show n) ++ "_mem.bin") mem'
        _ <- mem_save ((show n) ++ "_regs.bin") regs'
        printLn pc'
        printLn $ decode $ mem_read_word pc' mem'
        if mem_read_word (MkBitsVec 32 0x1000) mem' == (MkBitsVec 32 0x11111111) 
          then printLn "pass!"
          else printLn (regf_read (MkBitsVec 5 3) regs')

  


