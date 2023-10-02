module Linear

import public Data.Vect

infixr 0 -@
||| Infix notation for linear implication
public export
(-@) : Type -> Type -> Type
a -@ b = (1 _ : a) -> b

||| Linear identity function
public export
id : a -@ a
id x = x

||| Linear function composition
public export
(.) : (b -@ c) -@ (a -@ b) -@ (a -@ c)
(.) f g v = f (g v)

prefix 5 !*
||| Prefix notation for the linear unrestricted modality
public export
record (!*) (a : Type) where
  constructor MkBang
  unrestricted : a

public export
data LinVect : Nat -> Type -> Type where
  Nil : LinVect 0 _
  (::) : a -@ LinVect n a -@ LinVect (S n) a

public export
interface Consumable a where
  consume : a -@ ()
  
public export 
interface LinFunctor f where
  lin_map : (a -@ b) -> f a -@ f b

infixr 3 <<*>>
public export 
interface LinFunctor f => LinApplicative f where
  pure : a -> f a
  (<<*>>) : (f (a -@ b)) -> f a -@ f b
  
      
public export            
LinFunctor (LinVect n) where
  lin_map f [] = []
  lin_map f (x :: xs) = (f x) :: (lin_map f xs)  

public export
unzip : LinVect n (Res a (const $ b)) -@ Res (Vect n a) (const $ (LinVect n b))
unzip [] = [] # []
unzip ((val # r) :: xs) = let vs # rs : (Res _ _) = unzip xs in (val :: vs) # (r :: rs)

public export
val_app : (a -> b) -> (Res a (const c)) -@ (Res b (const c))
val_app f (val # r) = f val # r

export
Consumable (!* a) where
  consume (MkBang v) = ()

public export
proj1 : (Consumable b) => (Res a (\v => b)) -@ a
proj1 (val # r) = let () = consume r in val

public export
proj2 : (Res a (\v => b)) -@ b
proj2 (val # r) = r

lin : (a -> b) -> (a -@ b)
lin f = believe_me f
