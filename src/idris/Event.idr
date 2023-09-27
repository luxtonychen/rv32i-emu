module Event

import Linear

public export
data Event: Type -> Type where
  V : (a : ty) -> Event ty
  Abst : Event _
  
export
Functor Event where
  map f (V a) = V $ f a
  map f Abst = Abst
  
export
Applicative Event where
  pure a = V a
  (<*>) (V f) a = map f a
  (<*>) Abst a = Abst

export
Monad Event where
  (>>=) (V x) f = f x
  (>>=) Abst f = Abst

export
LinFunctor Event where
  lin_map f (V x) = V (f x)
  lin_map f Abst = Abst
  
export
LinApplicative Event where
  pure x = V x
  (<<*>>) (V f) x = lin_map f x
  (<<*>>) Abst (V x) = Abst
  (<<*>>) Abst Abst = Abst
  
