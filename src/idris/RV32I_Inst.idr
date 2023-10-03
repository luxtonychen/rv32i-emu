module RV32I_Inst

import BitsVec
import Data.Fin
import FinUtils

public export
data ROP = ADD | SUB | XOR | OR | AND | SLL | SRL | SRA | SLT | SLTU

Show ROP where
  show ADD  = "ADD  " 
  show SUB  = "SUB  " 
  show XOR  = "XOR  " 
  show OR   = "OR   " 
  show AND  = "AND  " 
  show SLL  = "SLL  " 
  show SRL  = "SRL  " 
  show SRA  = "SRA  " 
  show SLT  = "SLT  " 
  show SLTU = "SLTU " 

public export
data IOP1 = ADDI | XORI | ORI | ANDI | SLLI | SRLI | SRAI | SLTI | SLTIU | JALR

public export
data IOP2 =  LB | LH | LW | LBU | LHU 

Show IOP1 where 
  show ADDI  = "ADDI "
  show XORI  = "XORI "
  show ORI   = "ORI  "
  show ANDI  = "ANDI "
  show SLLI  = "SLLI "
  show SRLI  = "SRLI "
  show SRAI  = "SRAI "
  show SLTI  = "SLTI "
  show SLTIU = "SLTIU"
  show JALR  = "JALR "

Show IOP2 where 
  show LB    = "LB   "
  show LH    = "LH   "
  show LW    = "LW   "
  show LBU   = "LBU  "
  show LHU   = "LHU  "

public export
data SOP1 = SW

public export
data SOP2 = SB | SH

Show SOP2 where
  show SB = "SB   "
  show SH = "SH   "

Show SOP1 where
  show SW = "SW   "

public export
data BOP = BEQ | BNE | BLT | BGE | BLTU | BGEU

Show BOP where
  show BEQ  = "BEQ  "
  show BNE  = "BNE  "
  show BLT  = "BLT  "
  show BGE  = "BGE  "
  show BLTU = "BLTU "
  show BGEU = "BGEU "

public export
data UOP = LUI | AUIPC

Show UOP where
  show LUI = "LUI  "
  show AUIPC = "AUIPC"

public export
data JOP = JAL 

Show JOP where
  show JAL = "JAL  "

public export
data Inst : Type where
  R  : (op:ROP)  -> (rs1:BitsVec 5)  -> (rs2:BitsVec 5)  -> (rd:BitsVec 5)   -> Inst
  I1 : (op:IOP1) -> (rs1:BitsVec 5)  -> (imm:BitsVec 12) -> (rd:BitsVec 5)   -> Inst
  I2 : (op:IOP2) -> (rs1:BitsVec 5)  -> (imm:BitsVec 12) -> (rd:BitsVec 5)   -> Inst
  S1 : (op:SOP1)  -> (rs1:BitsVec 5)  -> (rs2:BitsVec 5)  -> (imm:BitsVec 12) -> Inst
  S2 : (op:SOP2)  -> (rs1:BitsVec 5)  -> (rs2:BitsVec 5)  -> (imm:BitsVec 12) -> Inst
  B  : (op:BOP)  -> (rs1:BitsVec 5)  -> (rs2:BitsVec 5)  -> (imm:BitsVec 13) -> Inst
  U  : (op:UOP)  -> (imm:BitsVec 20) -> (rd:BitsVec 5)   -> Inst
  J  : (op:JOP)  -> (imm:BitsVec 21) -> (rd:BitsVec 5)   -> Inst
  NA : Inst -- not valid

public export  
Show Inst where
  show (R op (MkBitsVec rs1) (MkBitsVec rs2) (MkBitsVec rd)) 
    = (show op) ++ " x" ++ (show rs1) ++ " x" ++ (show rs2) ++ " x" ++ (show rd)
  show (I1 op (MkBitsVec rs1) (MkBitsVec imm) (MkBitsVec rd)) 
    = (show op) ++ " x" ++ (show rs1) ++ " #" ++ (show imm) ++ " x" ++ (show rd)
  show (I2 op (MkBitsVec rs1) (MkBitsVec imm) (MkBitsVec rd)) 
    = (show op) ++ " x" ++ (show rs1) ++ " #" ++ (show imm) ++ " x" ++ (show rd)
  show (S1 op (MkBitsVec rs1) (MkBitsVec rs2) (MkBitsVec imm)) 
    = (show op) ++ " M[x" ++ (show rs1) ++ " + #" ++ (show imm) ++ "] x" ++ (show rs2)
  show (S2 op (MkBitsVec rs1) (MkBitsVec rs2) (MkBitsVec imm)) 
    = (show op) ++ " M[x" ++ (show rs1) ++ " + #" ++ (show imm) ++ "] x" ++ (show rs2)
  show (B op (MkBitsVec rs1) (MkBitsVec rs2) (MkBitsVec imm)) 
    = (show op) ++ " x" ++ (show rs1) ++ " x" ++ (show rs2) ++ " #" ++ (show imm)
  show (U op (MkBitsVec imm) (MkBitsVec rd)) 
    = (show op) ++ " x" ++ (show rd) ++ " #" ++ (show imm)
  show (J op (MkBitsVec imm) (MkBitsVec rd)) 
    = (show op) ++ " x" ++ (show rd) ++ " #" ++ (show imm)
  show NA = "NA"


data OpCode' = R' | I' | L' | S' | B' | U1 | U2 | J1 | J2 | NA'

get_op_code : BitsVec 7 -> OpCode'
get_op_code (MkBitsVec 0x33) = R' --Opcode 0110011
get_op_code (MkBitsVec 0x13) = I' --Opcode 0010011 
get_op_code (MkBitsVec 0x03) = L' --Opcode 0000011
get_op_code (MkBitsVec 0x23) = S' --Opcode 0100011
get_op_code (MkBitsVec 0x63) = B' --Opcode 1100011
get_op_code (MkBitsVec 0x6F) = J1 --Opcode 1101111
get_op_code (MkBitsVec 0x67) = J2 --Opcode 1100111
get_op_code (MkBitsVec 0x37) = U1 --Opcode 0110111
get_op_code (MkBitsVec 0x17) = U2 --Opcode 0010111
get_op_code _ = NA'


bv_compose_4 : {n: _} 
  -> (r1 : (LenTy, LenTy)) -> (r2 : (LenTy, LenTy)) 
  -> (r3 : (LenTy, LenTy)) -> (r4 : (LenTy, LenTy))
  -> BitsVec n 
  -> BitsVec (((snd r1) |-| (fst r1)) |+| ((snd r2) |-| (fst r2))
          |+| ((snd r3) |-| (fst r3)) |+| ((snd r4) |-| (fst r4)))
bv_compose_4 (l1, h1) (l2, h2) (l3, h3) (l4, h4) bv = 
  bv_concatenate (bv_get_range l1 h1 bv) 
 (bv_concatenate (bv_get_range l2 h2 bv) 
 (bv_concatenate (bv_get_range l3 h3 bv) 
                 (bv_get_range l4 h4 bv)))

public export
decode : BitsVec 32 -> Inst
decode bv = 
  let b_0_6   = bv_get_range 0  7  bv
      b_7_11  = bv_get_range 7  12 bv
      b_12_14 = bv_get_range 12 15 bv
      b_15_19 = bv_get_range 15 20 bv
      b_20_24 = bv_get_range 20 25 bv
      b_25_31 = bv_get_range 25 32 bv
      opcode  = get_op_code b_0_6
  in case opcode of
           R' => case b_12_14 of
                       (MkBitsVec 0x0) => case b_25_31 of
                                               (MkBitsVec 0x00) => R ADD b_15_19 b_20_24 b_7_11
                                               (MkBitsVec 0x20) => R SUB b_15_19 b_20_24 b_7_11
                                               _ => NA
                       (MkBitsVec 0x1) => R SLL  b_15_19 b_20_24 b_7_11
                       (MkBitsVec 0x2) => R SLT  b_15_19 b_20_24 b_7_11
                       (MkBitsVec 0x3) => R SLTU b_15_19 b_20_24 b_7_11
                       (MkBitsVec 0x4) => R XOR  b_15_19 b_20_24 b_7_11
                       (MkBitsVec 0x5) => case b_25_31 of 
                                               (MkBitsVec 0x00) => R SRL b_15_19 b_20_24 b_7_11
                                               (MkBitsVec 0x20) => R SRA b_15_19 b_20_24 b_7_11
                                               _ => NA
                       (MkBitsVec 0x6) => R OR  b_15_19 b_20_24 b_7_11
                       (MkBitsVec 0x7) => R AND b_15_19 b_20_24 b_7_11
                       _ => NA
           I' => let imm = bv_concatenate b_25_31 b_20_24
                 in case b_12_14 of
                        (MkBitsVec 0x0) => I1 ADDI b_15_19 imm b_7_11
                        (MkBitsVec 0x1) => I1 SLLI b_15_19 imm b_7_11
                        (MkBitsVec 0x2) => I1 SLTI b_15_19 imm b_7_11
                        (MkBitsVec 0x3) => I1 SLTIU b_15_19 imm b_7_11
                        (MkBitsVec 0x4) => I1 XORI b_15_19 imm b_7_11
                        (MkBitsVec 0x5) => case b_25_31 of 
                                                (MkBitsVec 0x00) => I1 SRLI b_15_19 imm b_7_11
                                                (MkBitsVec 0x20) => I1 SRAI b_15_19 imm b_7_11
                                                _ => NA
                        (MkBitsVec 0x6) => I1 ORI b_15_19 imm b_7_11
                        (MkBitsVec 0x7) => I1 ANDI b_15_19 imm b_7_11
                        _ => NA
           L' => let imm = bv_concatenate b_25_31 b_20_24
                 in case b_12_14 of
                        (MkBitsVec 0x0) => I2 LB  b_15_19 imm b_7_11
                        (MkBitsVec 0x1) => I2 LH  b_15_19 imm b_7_11
                        (MkBitsVec 0x2) => I2 LW  b_15_19 imm b_7_11
                        (MkBitsVec 0x4) => I2 LBU b_15_19 imm b_7_11
                        (MkBitsVec 0x5) => I2 LHU b_15_19 imm b_7_11
                        _ => NA
           S' => let imm = bv_concatenate b_25_31 b_7_11
                 in case b_12_14 of
                        (MkBitsVec 0x0) => S2 SB b_15_19 b_20_24 imm
                        (MkBitsVec 0x1) => S2 SH b_15_19 b_20_24 imm
                        (MkBitsVec 0x2) => S1 SW b_15_19 b_20_24 imm
                        _ => NA
           B' => let imm = (bv_concatenate 
                             (bv_compose_4 (31, 32) (7, 8) (25, 31) (8, 12) bv)
                             (the (BitsVec 1) (MkBitsVec 0)))
                in case b_12_14 of
                     (MkBitsVec 0x0) => B BEQ  b_15_19 b_20_24 imm
                     (MkBitsVec 0x1) => B BNE  b_15_19 b_20_24 imm
                     (MkBitsVec 0x4) => B BLT  b_15_19 b_20_24 imm
                     (MkBitsVec 0x5) => B BGE  b_15_19 b_20_24 imm
                     (MkBitsVec 0x6) => B BLTU b_15_19 b_20_24 imm
                     (MkBitsVec 0x7) => B BGEU b_15_19 b_20_24 imm
                     _ => NA
           J1 => let imm = (bv_concatenate 
                             (bv_compose_4 (31, 32) (12, 20) (20, 21) (21, 31) bv)
                             (the (BitsVec 1) (MkBitsVec 0))) 
                 in J JAL imm b_7_11
           J2 => I1 JALR b_15_19 (bv_get_range 20 32 bv) b_7_11
           U1 => U LUI (bv_get_range 12 32 bv) b_7_11
           U2 => U AUIPC (bv_get_range 12 32 bv) b_7_11
           _ => NA
