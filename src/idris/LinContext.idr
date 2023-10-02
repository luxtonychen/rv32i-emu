module LinContext

import public Linear
  
public export
record LinContext (a, b: Type) where
  constructor MkLC
  val : a
  1 ctx : b
  
public export
fromLDPair: (Res a (const b)) -@ LinContext a b
fromLDPair (val # r) = MkLC val r

Functor (\ty => LinContext ty c) where
  map f (MkLC val ctx) = MkLC (f val) ctx

LinFunctor (LinContext v) where
  lin_map f (MkLC val c) = MkLC val (f c)
  
bimap : (a -> b) -> (c -@ d) -> LinContext a c -@ LinContext b d
bimap f g (MkLC val ctx) = MkLC (f val) (g ctx)

public export
apply_on_val : (a -> b) -> (LinContext a c) -@ (LinContext b c)
apply_on_val f = bimap f id

infixr 9 <**>
infixr 9 <<<
infixr 9 <->
infixr 9 |>
infixr 9 <|
infixr 9 <||>
infixr 9 >@

export
(>@) : (a -> b) -> (c -@ d) -> LinContext a c -@ LinContext b d
(>@) = bimap

export
proj_val : (Consumable b) => LinContext a b -@ a
proj_val (MkLC val ctx) = let () = consume ctx in val

export
proj_ctx : LinContext a b -@ b
proj_ctx (MkLC val ctx) = ctx

export
(<**>) : (1 _: LinContext a b) -> (1 _: LinContext c d) -> LinContext (a, c) (LPair b d)
(<**>) (MkLC val1 ctx1) (MkLC val2 ctx2) = MkLC (val1, val2) (ctx1 # ctx2)

export
(<<<) : (LinContext b c2 -@ LinContext c c2) 
     -> (LinContext a c1 -@ LinContext b c1) 
     -> (LinContext a (LPair c1 c2) -@ LinContext c (LPair c1 c2))
(<<<) f g (MkLC val (ctx1 # ctx2)) = let (MkLC val' ctx1') = g $ MkLC val ctx1 
                                         (MkLC res ctx2') = f $ MkLC val' ctx2 
                                     in MkLC res (ctx1' # ctx2')

export
(<->) : (LinContext a c1 -@ LinContext b c1) 
     -> (LinContext c c1 -@ LinContext d c1) 
     -> (LinContext (a, c) c1 -@ LinContext (b, d) c1)
(<->) f g (MkLC (x, y) ctx) = let MkLC x' ctx'  = f $ MkLC x ctx 
                                  MkLC y' ctx'' = g $ MkLC y ctx' 
                              in MkLC (x', y') ctx''


export
(|>) : (a -> b) -> (LinContext c c1 -@ LinContext d c1)
    -> LinContext (a, c) c1 -@ LinContext (b, d) c1
(|>) f g = (bimap f id) <-> g

export
(<|) : (LinContext c c1 -@ LinContext d c1) -> (a -> b) 
    -> LinContext (c, a) c1 -@ LinContext (d, b) c1
(<|) f g = (bimap swap id) . (g |> f) . (bimap swap id)

export
(<||>) : (LinContext a c1 -@ LinContext b c1) 
      -> (LinContext c c2 -@ LinContext d c2) 
      -> (LinContext (a, c) (LPair c1 c2) -@ LinContext (b, d) (LPair c1 c2))
(<||>) f g (MkLC (v1, v2) (ctx1 # ctx2)) = let r1 = f (MkLC v1 ctx1)
                                               r2 = g (MkLC v2 ctx2)
                                           in r1 <**> r2
                                          
-- TODO: Implement elimination by meta programming
export
elim_vl : LinContext ((), c) b -@ LinContext c b
elim_vl (MkLC ((), val) ctx) = MkLC val ctx

export 
elim_vr : LinContext (a, ()) (LPair b d) -@ LinContext a (LPair b d)
elim_vr (MkLC (val, ()) ctx) = MkLC val ctx

export
elim_cl : LinContext (a, c) (LPair () d) -@ LinContext (a, c) d
elim_cl (MkLC val (() # ctx)) = MkLC val ctx

export
elim_cr : LinContext (a, c) (LPair b ()) -@ LinContext (a, c) b
elim_cr (MkLC val (ctx # ())) = MkLC val ctx

-- not a map
export
seq_eval : (f: LinContext a c -@ LinContext b c) -> LinContext (List a) c -@ LinContext (List b) c
seq_eval f (MkLC [] ctx) = MkLC [] ctx
seq_eval f (MkLC (x :: xs) ctx) = let MkLC y ctx'   = f $ MkLC x ctx 
                                      MkLC ys ctx'' = seq_eval f $ MkLC xs ctx'
                                  in MkLC (y::ys) ctx''

