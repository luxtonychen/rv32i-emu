module FinUtils

import Data.Fin

infixr 9 |-|
infixr 9 |+|
infixr 9 |*|

public export
(|-|) : Fin n -> Fin n -> Fin n
(|-|) FZ y = FZ
(|-|) (FS x) FZ = FS x
(|-|) (FS x) (FS y) = weaken $ x |-| y

public export
lemma2 : {x: _} -> {y: _} -> (compareNat x y == LT = True) -> LT x y
lemma2 {x = 0} {y = 0} prf impossible
lemma2 {x = 0} {y = (S k)} prf = LTESucc LTEZero
lemma2 {x = (S k)} {y = 0} prf impossible
lemma2 {x = (S k)} {y = (S j)} prf = LTESucc $ lemma2 prf

public export
lemma3 : {x: _} -> {y: _} -> LT x y -> LT x (S y)
lemma3 {x = 0} {y = y} p = LTESucc LTEZero
lemma3 {x = (S k)} {y = (S right)} (LTESucc x) = LTESucc (lemma3 x)

public export
natToFinSaturated : {n: _} -> Nat -> Fin (S n)
natToFinSaturated {n = 0} k = FZ
natToFinSaturated {n = (S j)} k with (k < S j) proof p
  natToFinSaturated {n = (S j)} k | False = last
  natToFinSaturated {n = (S j)} k | True = let 0 prf' = lemma3 {x=k} {y=S j} $ lemma2 p 
                                          in natToFinLT k {prf = prf'}

public export
(|+|) : {n: _} -> Fin n -> Fin n -> Fin n
(|+|) {n = 0} x y = x
(|+|) {n = (S k)} x y = let x' = finToNat x 
                            y' = finToNat y
                            r' = x' + y'
                        in natToFinSaturated r'


data FinLTE : Fin (S n) -> Fin (S n) -> Type where
  FLTEZero : FinLTE FZ _
  FLTESucc : FinLTE x y -> FinLTE (FS x) (FS y)

data FinOrd = LT | EQ | GT

Eq FinOrd where
  (==) LT LT = True
  (==) EQ EQ = True
  (==) GT GT = True
  (==) _ _ = False

compareFin : Fin (S n) -> Fin (S n) -> FinOrd
compareFin FZ FZ = EQ
compareFin FZ (FS x) = LT
compareFin (FS x) FZ = GT
compareFin (FS FZ) (FS FZ) = EQ
compareFin (FS FZ) (FS (FS x)) = LT
compareFin (FS (FS x)) (FS y) = compareFin (FS x) y

tight : {n: _} -> (x : Fin (2 + n)) 
      -> {auto 0 prf : FinLTE x (weaken $ the (Fin (S n)) Data.Fin.last)}
      -> Fin (S n)
tight {n = 0} FZ {prf} = FZ
tight {n = 0} (FS _) {prf = FLTEZero} impossible
tight {n = 0} (FS _) {prf = FLTESucc y} impossible
tight {n = (S k)} FZ {prf = FLTEZero} = FZ
tight {n = (S k)} (FS x) {prf = FLTESucc prf'} = FS $ tight {n=k} x {prf=prf'}

lemma : (x: Fin (S n)) -> (y: Fin (S n)) -> {prf: compareFin x y = LT} -> FinLTE x y
lemma FZ FZ {prf = Refl} impossible
lemma FZ (FS x) {prf = Refl} = FLTEZero
lemma (FS _) FZ {prf = Refl} impossible
lemma (FS FZ) (FS y) {prf = prf} = FLTESucc FLTEZero
lemma (FS (FS x)) (FS y) {prf} = FLTESucc (lemma (FS x) y {prf = prf})

(|*|) : {n:_} -> Fin n -> Fin n -> Fin n
(|*|) {n = 0} x y = x
(|*|) {n = (S k)} FZ y = y
(|*|) {n = (S k)} x FZ = x
(|*|) {n = (S k)} (FS x) (FS y) with (FS $ FS $ x |*| y)
  (|*|) {n = (S k)} (FS x) (FS y) | res' with (compareFin res' (weaken $ the (Fin (S k)) last)) proof p
    (|*|) {n = (S k)} (FS x) (FS y) | res' | LT = let 0 p' = lemma res' (weaken (the (Fin (S k)) last)) {prf = p} 
                                                  in tight res' {prf = p'}
    (|*|) {n = (S k)} (FS x) (FS y) | res' | _ = last

-- l5 : (the LenTy 32) = (16 |+| 16)
-- l5 = ?rhs
