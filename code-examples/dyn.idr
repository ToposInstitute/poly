module dyn

import Data.Vect
import Data.List

--- Code by David I. Spivak and David Jaz Myers and David Orion Girardo
--- © 2020  


------ The category of arenas ------

--Also called Cont, the category of containers.
--Equivalent to Poly, the category of polynomial functors in one variable.


--- Objects ---
record Arena where
       constructor MkArena
       pos : Type
       dis : pos -> Type

--- Morphisms---

record Lens (dom : Arena) (cod : Arena) where
       constructor MkLens
       observe   : pos dom -> pos cod
       interpret : (p : pos dom) -> dis cod (observe p) -> dis dom p

--- Identity ---

idLens : (a : Arena) -> Lens a a
idLens a = MkLens id (\_ => id)


--- Composition ---

infixr 4 <.>
(<.>) : Lens a2 a3 -> Lens a1 a2 -> Lens a1 a3
(<.>) lens23 lens12 = MkLens obs int
      where
        obs : pos a1 -> pos a3
        obs = (observe lens23) . (observe lens12)

        int : (p : pos a1) -> (dis a3 (obs p)) -> dis a1 p
        int p = (interpret lens12 p) . (interpret lens23 (observe lens12 p))

--- Manipulations on Arenas ---

Display : Arena -> Type  
Display a = (p : pos a ** dis a p)

AsFunctor : Arena -> Type -> Type
AsFunctor a y = (p : pos a ** dis a p -> y)



--- Special Arenas ---

ArenaIO : (i : Type) -> (o : Type) -> Arena --positions as output and
ArenaIO i o = MkArena o (\_ => i)           --distinctions as input

Self : Type -> Arena
Self s = ArenaIO s s

Closed : Arena
Closed = ArenaIO () ()


--- Factorization of lenses ---

Factor :  {a, c : Arena} -> Lens a c -> (b : Arena ** (Lens b c, Lens a b))
Factor f
  = let vertf = MkLens id (interpret f)
        cartf = MkLens (observe f) (\_ => id)
    in  ((MkArena (pos a) $ dis c . observe f) ** (cartf, vertf))

--- Reflections to Type ---

Exception : Type -> Arena
Exception t = ArenaIO Void t

Emitter : Type -> Arena
Emitter t = ArenaIO () t

Sensor : Type -> Arena
Sensor t = ArenaIO t ()

ev0 : Arena -> Arena
ev0 a = Exception $ AsFunctor a Void

fromEv0 : (a : Arena) -> Lens (ev0 a) a
fromEv0 a = MkLens o i
          where
            o : (p : pos a ** dis a p -> Void) -> pos a
            o = fst
--          i : (x : pos (ev0 a)) -> dis a (o x) -> dis (ev0 a) x
--          i : (x : AsFunctor a Void) -> dis a (o x) -> dis (ev0 a) x
            i : (x : (p : pos a ** dis a p -> Void)) -> dis a (fst x) -> dis (ev0 a) x
            i (p ** f) = f

ev1 : Arena -> Arena
ev1 a = Exception $ pos a -- = Exception $ AsFunctor a ()

toEv1 : (a : Arena) -> Lens a (ev1 a)
toEv1 a = MkLens id (\_ => absurd)

ev1y : Arena -> Arena
ev1y a = Emitter $ pos a

fromEv1y : (a : Arena) -> Lens (ev1y a) a
fromEv1y a = MkLens id (\_, _ => ()) 

constantFunction : {t, u : Type} -> (t -> u) -> Lens (Exception t) (Exception u)
constantFunction {t} {u} f = MkLens f (\_ => id)

EmitterFunction : {t, u : Type} -> (t -> u) -> Lens (Emitter t) (Emitter u)
EmitterFunction {t} {u} f = MkLens f (\_ => id) 

SensorFunction : {t, u: Type} -> (t -> u) -> Lens (Sensor u) (Sensor t)
SensorFunction {t} {u} f = MkLens id (\_ => f)

enclose : Arena -> Type
enclose a = Lens a Closed

encloseFunction : {t, u : Type} -> (t -> u) -> Lens (ArenaIO u t) Closed
encloseFunction {t} {u} f = MkLens (\_ => ()) (\d => \_ => f d)

enclosed : {m : Type} -> enclose (Emitter m)
enclosed {m} = encloseFunction $ \_ => ()

--- functors and monads ---

lift : (f : Type -> Type) -> Functor f => Arena -> Arena
lift f ar = MkArena (pos ar) fdis
          where
            fdis : (p : pos ar) -> Type
            fdis p = f $ dis ar p

LiftLens : {a, b : Arena} -> (f : Type -> Type) -> Functor f => 
           Lens a b -> Lens (lift f a) (lift f b) 
LiftLens {a} {b} f lens = MkLens (observe lens) int
          where
            int : (p : pos a) -> f $ dis b (observe lens p) -> f $ dis a p 
            int p = map $ interpret lens p

extract : {a : Arena} -> (f : Type -> Type) -> Monad f =>
            Lens (lift f a) a
extract {a} f = MkLens id pur 
          where
            pur : (p : pos a) -> dis a p -> dis (lift f a) p
            pur p = pure

extend : {a : Arena} -> (f : Type -> Type) -> Monad f =>
            Lens (lift f a) (lift f (lift f a))
extend {a} f = MkLens id joi
          where
            joi : (p : pos a) -> dis (lift f (lift f a)) p -> dis (lift f a) p
            joi p = join  

--- sum ---

zero : Arena
zero = ArenaIO Void Void

infixr 4 <++>

(<++>) : Arena -> Arena -> Arena
(<++>) a b = MkArena (Either (pos a) (pos b)) (\x => case x of {(Left p) => dis a p; (Right p) => dis b p})

sum : (ind : Type ** ind -> Arena) -> Arena
sum (ind ** arena) = MkArena (i : ind ** pos (arena i)) (\ (i ** p) => dis (arena i) p)




sumLens : Lens a1 b1 -> Lens a2 b2 -> Lens (a1 <++> a2) (b1 <++> b2)
sumLens {a1} {b1} {a2} {b2} l1 l2 = MkLens o i
          where
            o : pos (a1 <++> a2) -> pos (b1 <++> b2)
            o (Left p1)   = Left (observe l1 p1)
            o (Right p2) = Right (observe l2 p2)
            i : (p : pos (a1 <++> a2)) -> dis (b1 <++> b2) (o p) -> dis (a1 <++> a2) p
            i (Left p1) d1  = interpret l1 p1 d1
            i (Right p2) d2 = interpret l2 p2 d2

copair : {a1 : Arena} -> {a2 : Arena} -> {b : Arena} -> 
          Lens a1 b -> Lens a2 b -> Lens (a1 <++> a2) b
copair {a1} {a2} {b} l1 l2 = MkLens obs int
          where
            obs : pos (a1 <++> a2) -> pos b
            int : (p : pos (a1 <++> a2)) -> dis b (obs p) -> dis (a1 <++> a2) p          
            obs (Left  p1) = observe l1 p1
            obs (Right p2) = observe l2 p2
            int (Left  p1) d1 = interpret l1 p1 d1
            int (Right p2) d2 = interpret l2 p2 d2

--- product ---

one : Arena
one = ArenaIO Void ()

infixr 4 <**>

(<**>) : Arena -> Arena -> Arena
(<**>) a b = MkArena (pos a, pos b) (\ (pa,pb) => Either (dis a pa) (dis b pb))

prodList : List Arena -> Arena
prodList [] = one
prodList [a] = a
prodList (a :: as) = a <**> (prodList as)

-- functoriality of prod
prodLens : Lens a1 b1 -> Lens a2 b2 -> Lens (a1 <**> a2) (b1 <**> b2)
prodLens {a1} {b1} {a2} {b2} l1 l2 = MkLens o i 
          where
            o : pos (a1 <**> a2) -> pos (b1 <**> b2)
            o (p1, p2) = (observe l1 p1, observe l2 p2)
            i : (p : pos (a1 <**> a2)) -> dis (b1 <**> b2) (o p) -> dis (a1 <**> a2) p
            i (p1, p2) (Left d1)  = Left (interpret l1 p1 d1)
            i (p1, p2) (Right d2) = Right (interpret l2 p2 d2)

-- prod is the dependent product of polynomials; used in both inner homs
prod : (ind : Type ** ind -> Arena) -> Arena
prod (ind ** arena) = MkArena ((i : ind) -> pos (arena i)) (\p => (i : ind **
                      dis (arena i) (p i)))

pair : {a : Arena} -> {b1 : Arena} -> {b2 : Arena} -> 
        Lens a b1 -> Lens a b2 -> Lens a (b1 <**> b2)
pair {a} {b1} {b2} l1 l2 = MkLens obs int
          where
            obs : pos a -> (pos b1, pos b2)
            obs p = (observe l1 p, observe l2 p)
            int : (p : pos a) -> dis (b1 <**> b2) (obs p) -> dis a p
            int p (Left d1)  = interpret l1 p d1
            int p (Right d2) = interpret l2 p d2

--- Juxtaposition ---

(*) : Arena -> Arena -> Arena
(*) a b = MkArena (pos a, pos b) \ (pa, pb) => (dis a pa, dis b pb)

juxtList : List Arena -> Arena
juxtList [] = Closed
juxtList [a] = a
juxtList (a :: as) = a * (juxtList as)

juxt : (ind : Type) -> (ind -> Arena) -> Arena
juxt ind arena = MkArena ((i : ind) -> pos (arena i))
                         (\p => (i : ind) -> dis (arena i) (p i))

juxtLens : Lens a1 b1 -> Lens a2 b2 -> Lens (a1 * a2) (b1 * b2)
juxtLens {a1} {b1} {a2} {b2} l1 l2 = MkLens o i
          where 
            o : pos (a1 * a2) -> pos (b1 * b2)
            o (p1, p2) = (observe l1 p1, observe l2 p2)
            i : (p : pos (a1 * a2)) -> dis (b1 * b2) (o p) -> dis (a1 * a2) p
            i (p1, p2) (d1, d2) = (interpret l1 p1 d1, interpret l2 p2 d2)




--- Composition product ---

infixr 4 @@
(@@) : Arena -> Arena -> Arena
(@@) a b = MkArena (p : pos a ** dis a p -> pos b) \ (p ** f) => (d : dis a p ** dis b (f d))



circLens : {a1 : Arena} -> {b1 : Arena} -> {a2 : Arena} -> {b2 : Arena} -> 
           Lens a1 b1 -> Lens a2 b2 -> Lens (a1 @@ a2) (b1 @@ b2)
circLens {a1} {b1} {a2} {b2} l1 l2 = MkLens o i
          where
            o : pos (a1 @@ a2) -> pos (b1 @@ b2)
            o (p ** f) = (observe l1 p ** (observe l2) . f . (interpret l1 p))
            i : (p : pos (a1 @@ a2)) -> dis (b1 @@ b2) (o p) -> dis (a1 @@ a2) p
            i (p ** f) (d1 ** d2) = (e1 ** interpret l2 (f e1) d2)
            where
              e1 : dis a1 p 
              e1 = interpret l1 p d1

CircPow : Arena -> Nat -> Arena
CircPow _  Z     = Closed
CircPow a (S n) = a @@ CircPow a n 

CircPowLens : {a : Arena} -> {b : Arena} -> 
              Lens a b -> (n : Nat) -> Lens (CircPow a n) (CircPow b n)
CircPowLens {a} {b} _     Z    = idLens Closed 
CircPowLens {a} {b} lens (S n) = circLens lens (CircPowLens lens n)

EmitterPow : (t : Type) -> (n : Nat) -> Lens (CircPow (Emitter t) n) (Emitter (Vect n t))
EmitterPow t Z = MkLens (\_ => Nil) (\_, _ => ())
EmitterPow t (S n) = ?pown



--- Comonoids ---

record Comonoid where
       constructor MkComonoid
       domains    : Arena
       identities : Lens domains Closed
       codsComps  : Lens domains (domains @@ domains)

data Behavior : (ar : Arena) -> Type where
          (::) : (p : pos ar) -> (dis ar p -> Behavior ar) -> Behavior ar

head : {ar : Arena} -> Behavior ar -> pos ar
head {ar} (h :: _) = h

tail : {ar : Arena} -> (b : Behavior ar) -> dis ar (head b) -> Behavior ar
tail {ar} (_ :: t) = t




MonSensor : (t : Type) -> t -> (t -> t -> t) -> Comonoid
MonSensor t neut plus
  = let 
        sens : Arena
        idy  : Lens sens Closed
        cc   : Lens sens (sens @@ sens)
        sens = (Sensor t)
        idy  = SensorFunction $ \_ => neut
        cc   = MkLens obs int
          where
            obs : pos sens -> (p : pos sens ** dis sens p -> pos sens)
            obs _ = (() ** \_ => ())
            int : (p : pos sens) -> dis (sens @@ sens) (obs p) -> dis sens p
            int _ (d ** e) = d `plus` e
    in MkComonoid sens idy cc

TrajComon : Comonoid
TrajComon = MonSensor Nat Z (+)



--- Selves are comonoids ---



counit : (s : Type) -> Lens (Self s) Closed
counit s = MkLens o i
          where
            o : s -> ()
            o _ = ()
            i : s -> () -> s
            i s _ = s

comult : (s : Type) -> Lens (Self s) ((Self s) @@ (Self s))
comult s = MkLens o i
          where
            o : s -> pos ((Self s) @@ (Self s))
            o x = (x ** id)
            i : (x : s) -> (dis ((Self s) @@ (Self s)) (o x)) -> s
            i x (d1 ** d2) = d2

ContrGrpd : Type -> Comonoid
ContrGrpd t = MkComonoid (Self t) (counit t) (comult t)

comultPow : (s : Type) -> (n : Nat) -> Lens (Self s) (CircPow (Self s) n)
comultPow s  Z    = counit s
comultPow s (S n) = (circLens (idLens (Self s)) (comultPow s n)) <.> (comult s)




--- Duoidal ---

duoidal : {a1, a2, b1, b2 : Arena} -> Lens ((a1 @@ a2) * (b1 @@ b2))
                                           ((a1 * b1) @@ (a2 * b2))
duoidal {a1} {a2} {b1} {b2} =
          let
            x : Arena
            x = (a1 @@ a2) * (b1 @@ b2)
            y : Arena
            y = (a1 * b1) @@ (a2 * b2)
            o : pos x -> pos y
            o ((p1 ** p2), (q1 ** q2)) = pp
              where
                pp : (p : (pos a1, pos b1) ** dis (a1 * b1) p -> pos (a2 * b2))
                pp = ((p1, q1) ** (\d : dis (a1 * b1) (p1, q1) => (p2 (fst d), q2 (snd d))))
            i : (p : pos x) -> dis y (o p) -> dis x p
            i ((p1 ** p2), (q1 ** q2)) = ii
              where
--              ii : dis y ((p1, q1) ** (\d : dis (a1 * b1) (p1, q1) => (p2 (fst d), q2 (snd d)))) 
--                      -> dis x ((p1 ** p2), (q1 ** q2))
                ii : (de1 : dis (a1 * b1) (p1, q1) ** dis (a2 * b2) (p2 (fst de1), q2 (snd de1)))
                        -> dis x ((p1 ** p2), (q1 ** q2))
                ii (de1 ** de2) = ((fst de1 ** fst de2), (snd de1 ** snd de2))
          in MkLens o i

--- Exponentiation ---

infixr 4 ^

--prod : (ind : Type ** ind -> Arena) -> Arena
(^) : Arena -> Arena -> Arena
(^) a b = prod (pos a ** arena)
          where
            arena : pos a -> Arena
            arena p = b @@ ((Exception $ dis a p) <++> Closed)

--- Internal Hom ---

infixr 4 ^^
(^^) : Arena -> Arena -> Arena
(^^) b a = prod (pos a ** arena)
          where 
            arena : pos a -> Arena
            arena p = b @@ (Emitter $ dis a p)

--eval : {a : Arena} -> {b : Arena} -> Lens (a * (b ^^ a)) b
--eval {a} {b} = MkLens (\(pa,pab) => let (pb ** _) = pab pa in pb)  (\(pa, pab) ,
--db => let (paa ** da) = (pab pa) in (da db , (pa ** ?xx)))

--- Dynamical systems ---


record DynSystem where
       constructor MkDynSystem
       state : Type
       body  : Arena
       pheno : Lens (Self state) body

static : DynSystem
static = MkDynSystem () Closed (EmitterFunction id)

infixr 4 ***
(***) : DynSystem -> DynSystem -> DynSystem
(***) dyn1 dyn2 = 
          let
            state12 : Type
            body12  : Arena
            pheno12 : Lens (Self state12) body12
            state12 = (state dyn1, state dyn2)
            body12  = (body dyn1) * (body dyn2)
            pheno12
              = MkLens (\(s1, s2) => (observe (pheno dyn1) s1, observe (pheno dyn2) s2))
                       (\(s1, s2),(d1, d2) => (interpret (pheno dyn1) s1 d1, interpret (pheno dyn2) s2 d2))
          in MkDynSystem state12 body12 pheno12

--juxtapose : List DynSystem -> DynSystem
--juxtapose []        = static
--juxtapose [d]       = d
--juxtapose (d :: ds) = d *** (juxtapose ds)

install : (d : DynSystem) -> (a : Arena) -> Lens (body d) a -> DynSystem
install d a l = MkDynSystem (state d) a (l <.> (pheno d))

speedUp : DynSystem -> Nat -> DynSystem
speedUp dyn n = let
              fastBody   : Arena
              fastWork   : Lens (Self $ state dyn) fastBody
              fastBody   = CircPow (body dyn) n
              fastWork   = CircPowLens (pheno dyn) n <.> comultPow (state dyn) n
            in MkDynSystem (state dyn) fastBody fastWork


run : (d : DynSystem) -> enclose (body d) -> (state d) -> Stream (pos $ body d)
run d e s = outp :: (run d e next)
            where
              outp : pos $ body d
              next : state d
              outp = observe (pheno d) s
              next = interpret (pheno d) s $ interpret e outp ()



toStreamBehavior : {a : Arena} -> (b : Behavior a) -> (phys : enclose a) -> Stream (pos a)
toStreamBehavior {a} b phys = currpos :: toStreamBehavior rest phys
  where
    currpos : pos a
    currpos = head b

    rest : Behavior a
    rest = tail b $ interpret phys currpos ()

dynBehavior : (d : DynSystem) -> (state d) -> Behavior (body d)
dynBehavior dyn st = let
              current : pos $ body dyn
              choice  : dis (body dyn) current -> Behavior (body dyn)
              current  = observe (pheno dyn) st 
              choice d = dynBehavior dyn (interpret (pheno dyn) st d)
           in current :: choice

runBehav : (d : DynSystem) -> enclose (body d) -> (state d) -> Stream (pos $ body d)
runBehav dyn phys st = toStreamBehavior (dynBehavior dyn st) phys

--- IO ---

-- EmitterM : (m : Type -> Type) -> Monad m => (a : Type) -> DynSystem
-- EmitterM m a = MkDynSystem (m a) (Emitter (m a)) passInput
--           where
--             passInput : Lens (Self (m a)) (Emitter (m a))
--             passInput = MkLens id 

IOEmitter : (a : Type) -> (String -> a) -> DynSystem
IOEmitter a cast = let 
            passUserInput : Lens (Self $ IO a) (Emitter $ IO a)
            passUserInput = MkLens id listen
            where
              listen : (old : IO a) -> () -> IO a
              listen _ _ = map cast getLine
         in MkDynSystem (IO a) (Emitter $ IO a) passUserInput


--- Debugging ---

-- current : (d : DynSystem) -> state d -> pos (body d)
-- current d s = observe (pheno d) s

-- feed : (dyn : DynSystem) -> (s : state dyn) -> dis (body dyn) (observe (pheno dyn) s) -> state dyn
-- feed dyn s d = interpret play s d
--           where 
--             play : Lens (Self (state dyn)) (body dyn)
--             play = pheno dyn

--- Examples ---


funcToDynSystem : {s : Type} -> {t : Type} -> (s -> t) -> DynSystem
funcToDynSystem {s} {t} f = let
              bodyf : Arena
              phenof : Lens (Self t) bodyf
              bodyf = ArenaIO s t
              phenof = MkLens id (\_ => f)
           in MkDynSystem t bodyf phenof

delay : (s : Type) -> DynSystem
delay s = funcToDynSystem (the (s -> s) id)

plus : DynSystem
plus = funcToDynSystem (uncurry (+))

inv : {a,b : Type} -> (f : a -> b) -> b -> Type
inv f y = DPair a (\ x => (f x = y))

record Graph (Node : Type) (Edge : Type) where
  constructor MkGraph
  source, target : Edge -> Node

namespace graph_examples
  grph1 : Graph (Nat , Nat) (Nat, Nat, Nat, Nat)
  grph1 = MkGraph (\(i,j,m,n) => (m,n))  (\(i,j,m,n) => (m + i,n + j))

-- Exmaple 1.122
--emanation : {n, e : Type} -> Graph n e -> Arena
--emanation g = MkArena n $ inv (source g)

--graphDyn : {node, edge : Type} -> Graph node edge -> DynSystem
--graphDyn g = MkDynSystem node (emanation g) (MkLens id \ _ , (e ** p) => target g e)
---


-- Exmaple 1.137
emanation : {node,edge : Type} -> (g : Graph node edge) -> (t : node -> Type) -> node -> Arena
emanation g t v = let dis = ((a : inv (source g) v) -> t (target g (fst a)))
            in ArenaIO dis (t v)

--juxt : (ind : Type) -> (ind -> Arena) -> Arena
--juxt ind arena = MkArena ((i : ind) -> pos (arena i))
                         --(\p => (i : ind) -> dis (arena i) (p i))

data Direction = N | NE | E | SE | S | SW | W | NW
tgt_gol : ((Integer, Integer), Direction) -> (Integer, Integer)
tgt_gol ((i,j),d) = case d of
                         N => (i,j+1)
                         S => (i,j-1)
                         E => (i+1,j)
                         W => (i-1,j)
                         NE => (i+1,j+1)
                         NW => (i-1,j+1)
                         SE => (i+1,j-1)
                         SW => (i-1,j-1)


juxtLenses : (ind : Type) -> (as,bs : ind -> Arena)
       -> ((i : ind) -> Lens (as i) (bs i))
       -> Lens (juxt ind as) (juxt ind bs)
juxtLenses i as bs ls =
  MkLens (\pas, i => observe (ls i) (pas i))
         (\pas, dbs, i => interpret (ls i) (pas i) (dbs i))

juxtapose : {ind : Type} -> (ind -> DynSystem) -> DynSystem
juxtapose ds =
      MkDynSystem ((v : ind) -> state (ds v))
                  (juxt ind $ \v => body (ds v))
                  (juxtLenses ind (\i => Self (state (ds i)))
                                  (\i => body (ds i))
                                  (\i => pheno (ds i)))

cellArena : Arena
cellArena = MkArena Bool (\_ => Direction -> Bool)

bool2Nat : Bool -> Nat
bool2Nat True = 1
bool2Nat False = 0

countNear : (Direction -> Bool) -> Nat
countNear f = let f' = bool2Nat . f in f' N + f' S + f' E + f' W + f' NE + f' NW + f' SE + f' SW

cellUpdt : (p : Bool) -> (Direction -> Bool) -> Bool
cellUpdt True f = countNear f == 2 || countNear f == 3
cellUpdt False f = countNear f == 3

--install : (d : DynSystem) -> (a : Arena) -> Lens (body d) a -> DynSystem
--install d a l = MkDynSystem (state d) a (l <.> (pheno d))

graphWD : {node, edge : Type} -> (g : Graph node edge)
       -> (t : node -> Type) -> Lens (juxt node $ emanation g t)
                                     (Emitter ((v : node) -> t v))
graphWD g  t = MkLens id ?st -- (\f, (), _, a => f (target g (fst a)))


cellDyn : DynSystem
cellDyn = MkDynSystem Bool cellArena $ MkLens id (\p, updt => cellUpdt p updt)

golGraph : Graph (Integer, Integer) ((Integer, Integer), Direction)
golGraph = MkGraph (\(ij,_) => ij) tgt_gol

golDyn : DynSystem
golDyn = let cellDyns : (Integer,Integer) -> DynSystem
             cellDyns _ = cellDyn
         in juxtapose cellDyns


GoL : DynSystem
GoL = let ll = graphWD golGraph (\_ => Bool)
      in install golDyn (Emitter ((Integer,Integer) -> Bool)) ?lll
  {-


initGol : (Integer,Integer) -> Bool
initGol (i,j) = j == 0 && i >= (-1) && i <= 1

runGol : Stream ((Integer,Integer) -> Bool)
runGol = run GoL enclosed initGol

viewGol : Stream (Bool,Bool,Bool)
viewGol = map (\f => (f (-1,0), f (0,0), f (1,0))) runGol
-}

-- (graphWD golGraph ?ss)


Prefib : DynSystem
Prefib = plus *** (delay Integer)

fibwd : Lens (body Prefib) (Emitter Integer)
fibwd = MkLens observe interpret 
          where
            observe : (Integer, Integer) -> Integer
            interpret : (p : (Integer, Integer)) -> () -> dis (body Prefib) p
            observe (pl, de) = de
            interpret (pl, de) = \_ => ((de, pl), pl)

Fibonacci : DynSystem
Fibonacci = install Prefib (Emitter Integer) fibwd


FibSeq : Stream Integer
FibSeq = run Fibonacci enclosed (1, 1)

FibSeq5 : Lens (MkArena (p : Integer ** () -> (p : Integer ** () -> ())) ?t) Closed
      -> Stream (pos (body (speedUp Fibonacci 2)))
FibSeq5 = \x => run (speedUp Fibonacci 2) x (1,1)

--------  Fibonacci in REPL --------
main : IO ()
main = print $ take 10000 FibSeq

-- Run this in the REPL:
-- take 10 FibSeq





-- ==========================























--- Distributivity ---

prodSum : {a, b, c : Arena} -> Lens (a <**> (b <++> c)) ((a <**> b) <++> (a <**> c))
prodSum {a} {b} {c} = let
              a1 : Arena
              a1 = a <**> (b <++> c)
              a2 : Arena
              a2 = (a <**> b) <++> (a <**> c)
              o : pos a1 -> pos a2
              o (p, Left q)  = Left (p, q)
              o (p, Right r) = Right (p, r)
              i : (p : pos a1) -> dis a2 (o p) -> dis a1 p
              i (pa, Left pb) (Left da) = Left da
              i (pa, Left pb) (Right db) = Right db
              i (pa, Right pc) (Left da) = Left da
              i (pa, Right pc) (Right dc) = Right dc
           in MkLens o i
sumProd : {a, b, c : Arena} -> Lens ((a <**> b) <++> (a <**> c)) (a <**> (b <++> c))
sumProd {a} {b} {c} = let
              a1 : Arena
              a1 = (a <**> b) <++> (a <**> c)
              a2 : Arena
              a2 = a <**> (b <++> c)
              o : pos a1 -> pos a2
              o (Left (pa, pb)) = (pa, Left pb)
              o (Right (pa, pc)) = (pa, Right pc)
              i : (p : pos a1) -> dis a2 (o p) -> dis a1 p
              i (Left (pa, pb)) (Left da) = Left da
              i (Left (pa, pb)) (Right db) = Right db
              i (Right (pa, pc)) (Left da) = Left da
              i (Right (pa, pc)) (Right dc) = Right dc
           in MkLens o i

juxtSum : {a, b, c : Arena} -> Lens (a * (b <++> c)) ((a * b) <++> (a * c))
juxtSum {a} {b} {c} = let
              a1 : Arena
              a1 = a * (b <++> c)
              a2 : Arena
              a2 = (a * b) <++> (a * c)
              o : pos a1 -> pos a2
              o (pa, Left pb) = Left (pa, pb)
              o (pa, Right pc) = Right (pa, pc)
              i : (p : pos a1) -> dis a2 (o p) -> dis a1 p
              i (pa, Left pb) (da, db) = (da, db)
              i (pa, Right pc) (da, dc) = (da, dc)
           in MkLens o i

sumJuxt : {a, b, c : Arena} -> Lens ((a * b) <++> (a * c)) (a * (b <++> c))
sumJuxt {a} {b} {c} = let
              a1 : Arena
              a1 = (a * b) <++> (a * c)
              a2 : Arena
              a2 = a * (b <++> c)
              o : pos a1 -> pos a2
              o (Left (pa, pb)) = (pa, Left pb)
              o (Right (pa, pc)) = (pa, Right pc)
              i : (p : pos a1) -> dis a2 (o p) -> dis a1 p
              i (Left (pa, pb)) (da, db) = (da, db)
              i (Right (pa, pc)) (da, dc) = (da, dc)
          in MkLens o i
