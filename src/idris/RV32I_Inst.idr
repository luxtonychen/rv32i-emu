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
data OP : Type where
  R : (op: ROP)  -> OP
  I1: (op: IOP1) -> OP
  I2: (op: IOP2) -> OP
  S1: (op: SOP1) -> OP
  S2: (op: SOP2) -> OP
  B : (op: BOP)  -> OP
  U : (op: UOP)  -> OP
  J : (op: JOP)  -> OP
  NA: OP
  
||| A union, instead of a disjoint union (coproduct $+$), of decoded fields.
||| For a coproduct A + B, we first derive the product varient $t \times A \times B$, 
||| then identify objects between them
public export
record Inst where
  constructor MkInst
  op  : OP
  rs1 : BitsVec 5
  rs2 : BitsVec 5
  rd  : BitsVec 5
  imm : BitsVec 32
  
bv_sign_ext_32: {m:_} -> BitsVec m -> BitsVec 32
bv_sign_ext_32 = (bv_get_range 0 32) .  bv_sign_ext
   
public export
Show Inst where
  show (MkInst (R op) rs1 rs2 rd imm)
    = (show op) ++ " x" ++ (show rs1) ++ " x" ++ (show rs2) ++ " x" ++ (show rd)
  show (MkInst (I1 op) rs1 rs2 rd imm) 
    = (show op) ++ " x" ++ (show rs1) ++ " #" ++ (show imm) ++ " x" ++ (show rd)
  show (MkInst (I2 op) rs1 rs2 rd imm)
    = (show op) ++ " x" ++ (show rs1) ++ " #" ++ (show imm) ++ " x" ++ (show rd)
  show (MkInst (S1 op) rs1 rs2 rd imm)
    = (show op) ++ " M[x" ++ (show rs1) ++ " + #" ++ (show imm) ++ "] x" ++ (show rs2)
  show (MkInst (S2 op) rs1 rs2 rd imm)
    = (show op) ++ " M[x" ++ (show rs1) ++ " + #" ++ (show imm) ++ "] x" ++ (show rs2)
  show (MkInst (B op) rs1 rs2 rd imm)
    = (show op) ++ " x" ++ (show rs1) ++ " x" ++ (show rs2) ++ " #" ++ (show imm)
  show (MkInst (U op) rs1 rs2 rd imm)
    = (show op) ++ " x" ++ (show rd) ++ " #" ++ (show imm)
  show (MkInst (J op) rs1 rs2 rd imm)
    = (show op) ++ " x" ++ (show rd) ++ " #" ++ (show imm)
  show (MkInst NA rs1 rs2 rd imm) = "NA"


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

export
decode: (dr: BitsVec 5) -> (di: BitsVec 32) -> BitsVec 32 -> Inst
decode dr di bv = 
  let b_0_6   = bv_get_range 0  7  bv
      b_7_11  = bv_get_range 7  12 bv
      b_12_14 = bv_get_range 12 15 bv
      b_15_19 = bv_get_range 15 20 bv
      b_20_24 = bv_get_range 20 25 bv
      b_25_31 = bv_get_range 25 32 bv
      opcode  = get_op_code b_0_6
  in case opcode of
           R' => let rop : Maybe ROP = case b_12_14 of
                                         (MkBitsVec 0x0) => case b_25_31 of
                                                              (MkBitsVec 0x00) => Just ADD
                                                              (MkBitsVec 0x20) => Just SUB 
                                                              _ => Nothing
                                         (MkBitsVec 0x1) => Just SLL  
                                         (MkBitsVec 0x2) => Just SLT  
                                         (MkBitsVec 0x3) => Just SLTU 
                                         (MkBitsVec 0x4) => Just XOR 
                                         (MkBitsVec 0x5) => case b_25_31 of 
                                                              (MkBitsVec 0x00) => Just SRL 
                                                              (MkBitsVec 0x20) => Just SRA
                                                              _ => Nothing
                                         (MkBitsVec 0x6) => Just OR 
                                         (MkBitsVec 0x7) => Just AND
                                         _ => Nothing
                 in case rop of 
                      (Just x) => MkInst (R x) b_15_19 b_20_24 b_7_11 di
                      Nothing  => MkInst NA dr dr dr di
                      
           I' => let imm = bv_sign_ext_32 $ bv_concatenate b_25_31 b_20_24
                     iop : Maybe IOP1 = case b_12_14 of
                                          (MkBitsVec 0x0) => Just ADDI 
                                          (MkBitsVec 0x1) => Just SLLI 
                                          (MkBitsVec 0x2) => Just SLTI 
                                          (MkBitsVec 0x3) => Just SLTIU
                                          (MkBitsVec 0x4) => Just XORI 
                                          (MkBitsVec 0x5) => case b_25_31 of 
                                                               (MkBitsVec 0x00) => Just SRLI
                                                               (MkBitsVec 0x20) => Just SRAI
                                                               _ => Nothing
                                          (MkBitsVec 0x6) => Just ORI 
                                          (MkBitsVec 0x7) => Just ANDI
                                          _ => Nothing
                 in case iop of
                      (Just x) => MkInst (I1 x) b_15_19 dr b_7_11 imm
                      Nothing  => MkInst NA dr dr dr di
                      
           L' => let imm = bv_sign_ext_32 $ bv_concatenate b_25_31 b_20_24
                     lop : Maybe IOP2 = case b_12_14 of
                                          (MkBitsVec 0x0) => Just LB 
                                          (MkBitsVec 0x1) => Just LH 
                                          (MkBitsVec 0x2) => Just LW 
                                          (MkBitsVec 0x4) => Just LBU
                                          (MkBitsVec 0x5) => Just LHU 
                                          _ => Nothing
                 in case lop of
                      (Just x) => MkInst (I2 x) b_15_19 dr b_7_11 imm
                      Nothing  => MkInst NA dr dr dr di
                      
           S' => let imm = bv_sign_ext_32 $ bv_concatenate b_25_31 b_7_11
                 in case b_12_14 of
                      (MkBitsVec 0x0) => MkInst (S2 SB) b_15_19 b_20_24 dr imm
                      (MkBitsVec 0x1) => MkInst (S2 SH) b_15_19 b_20_24 dr imm
                      (MkBitsVec 0x2) => MkInst (S1 SW) b_15_19 b_20_24 dr imm
                      _ => MkInst NA dr dr dr di
                   
           B' => let imm = bv_sign_ext_32 $ (bv_concatenate 
                                              (bv_compose_4 (31, 32) (7, 8) (25, 31) (8, 12) bv)
                                              (the (BitsVec 1) (MkBitsVec 0)))
                     bop : Maybe BOP = case b_12_14 of
                                         (MkBitsVec 0x0) => Just BEQ  
                                         (MkBitsVec 0x1) => Just BNE 
                                         (MkBitsVec 0x4) => Just BLT 
                                         (MkBitsVec 0x5) => Just BGE 
                                         (MkBitsVec 0x6) => Just BLTU
                                         (MkBitsVec 0x7) => Just BGEU 
                                         _ => Nothing
                 in case bop of
                      (Just x) => MkInst (B x) b_15_19 b_20_24 dr imm
                      Nothing => MkInst NA dr dr dr di
                     
           J1 => let imm = bv_sign_ext_32 
                         $ (bv_concatenate 
                             (bv_compose_4 (31, 32) (12, 20) (20, 21) (21, 31) bv)
                             (the (BitsVec 1) (MkBitsVec 0))) 
                 in MkInst (J JAL) dr dr b_7_11 imm
                 
           J2 => MkInst (I1 JALR) b_15_19 dr b_7_11 (bv_sign_ext_32 $ bv_get_range 20 32 bv)
           
           U1 => let imm = (bv_get_range 0 32 
                          $ bv_sll {m = 8} (bv_zero_ext (bv_get_range 12 32 bv)) 
                          $ MkBitsVec 12)
                 in MkInst (U LUI) dr dr b_7_11 imm
                 
           U2 => let imm = (bv_get_range 0 32 
                          $ bv_sll {m = 8} (bv_zero_ext (bv_get_range 12 32 bv)) 
                          $ MkBitsVec 12)
                 in MkInst (U AUIPC) dr dr b_7_11 imm
                 
           _ => MkInst NA dr dr dr di
