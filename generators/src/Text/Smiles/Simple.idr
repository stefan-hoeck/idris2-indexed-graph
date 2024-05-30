module Text.Smiles.Simple

import Data.Graph.Indexed
import Derive.Prelude
import Text.Parse.Manual

%default total
%language ElabReflection

public export
data Bond = Sngl | Dbl | Trpl

%runElab derive "Bond" [Show,Eq,Ord]

export
Interpolation Bond where
  interpolate Sngl = "-"
  interpolate Dbl  = "="
  interpolate Trpl = "#"

public export
data Elem = B | C | N | O | F | P | S

%runElab derive "Elem" [Show,Eq,Ord]

export
Interpolation Elem where interpolate = show

public export
record Ring where
  constructor R
  ring   : Nat
  bond   : Maybe Bond

%runElab derive "Ring" [Show,Eq]

export
Interpolation Ring where
  interpolate (R r (Just b)) = "\{b}\{show r}"
  interpolate (R r Nothing)  = "\{show r}"

public export
data SmilesToken : Type where
  PO  : SmilesToken -- '('
  PC  : SmilesToken -- ')'
  Dot : SmilesToken
  TB  : Bond -> SmilesToken
  TA  : Elem -> SnocList Ring -> SmilesToken

%runElab derive "SmilesToken" [Show,Eq]

export
Interpolation SmilesToken where
  interpolate PO        = "("
  interpolate PC        = ")"
  interpolate Dot       = "."
  interpolate (TB x)    = "\{x}"
  interpolate (TA x rs) = "\{x}\{fastConcat $ map interpolate (rs <>> [])}"

--------------------------------------------------------------------------------
--          Lexer
--------------------------------------------------------------------------------

rng :
     SnocList (SmilesToken,Nat)
  -> (column : Nat)
  -> (ringNr : Nat)
  -> (cs : List Char)
  -> (0 acc : SuffixAcc cs)
  -> Maybe (List (SmilesToken,Nat))

tok :
     SnocList (SmilesToken,Nat)
  -> (column : Nat)
  -> (cs : List Char)
  -> (0 acc : SuffixAcc cs)
  -> Maybe (List (SmilesToken,Nat))
tok st c ('C'::t) (SA r) = tok (st :< (TA C [<],c)) (c+1) t r
tok st c ('N'::t) (SA r) = tok (st :< (TA N [<],c)) (c+1) t r
tok st c ('O'::t) (SA r) = tok (st :< (TA O [<],c)) (c+1) t r
tok st c ('F'::t) (SA r) = tok (st :< (TA F [<],c)) (c+1) t r
tok st c ('S'::t) (SA r) = tok (st :< (TA S [<],c)) (c+1) t r
tok st c ('P'::t) (SA r) = tok (st :< (TA P [<],c)) (c+1) t r
tok st c ('B'::t) (SA r) = tok (st :< (TA B [<],c)) (c+1) t r
tok st c ('('::t) (SA r) = tok (st :< (PO,c)) (c+1) t r
tok st c (')'::t) (SA r) = tok (st :< (PC,c)) (c+1) t r
tok st c ('='::t) (SA r) = tok (st :< (TB Dbl,c)) (c+1) t r
tok st c ('#'::t) (SA r) = tok (st :< (TB Trpl,c)) (c+1) t r
tok st c ('-'::t) (SA r) = tok (st :< (TB Sngl,c)) (c+1) t r
tok st c ('.'::t) (SA r) = tok (st :< (Dot,c)) (c+1) t r
tok st c ('0'::t) (SA r) = rng st (c+1) 0 t r
tok st c ('1'::t) (SA r) = rng st (c+1) 1 t r
tok st c ('2'::t) (SA r) = rng st (c+1) 2 t r
tok st c ('3'::t) (SA r) = rng st (c+1) 3 t r
tok st c ('4'::t) (SA r) = rng st (c+1) 4 t r
tok st c ('5'::t) (SA r) = rng st (c+1) 5 t r
tok st c ('6'::t) (SA r) = rng st (c+1) 6 t r
tok st c ('7'::t) (SA r) = rng st (c+1) 7 t r
tok st c ('8'::t) (SA r) = rng st (c+1) 8 t r
tok st c ('9'::t) (SA r) = rng st (c+1) 9 t r
tok st c ('%'::x::y::t) (SA r) =
  if isDigit x && isDigit y
     then rng st (c+2) (cast $ digit x * 10 + digit y) t r
     else Nothing
tok st c (x  ::t) (SA r) = Nothing
tok st c []       _      = Just (st <>> [])

rng (st :< (TA a rs,x)) c rn cs acc =
  tok (st :< (TA a (rs :< R rn Nothing),x)) c cs acc
rng (st :< (TA a rs,x):< (TB b, y)) c rn cs acc =
  tok (st :< (TA a (rs :< R rn (Just b)),x)) c cs acc
rng st c rn cs acc = Nothing

export
lexSmiles : String -> Maybe (List (SmilesToken,Nat))
lexSmiles s = tok [<] 0 (unpack s) suffixAcc

--------------------------------------------------------------------------------
--          Parser
--------------------------------------------------------------------------------

record RingInfo (k : Nat) where
  constructor RI
  orig   : Fin k
  atom   : Elem
  bond   : Maybe Bond
  column : Nat

record AtomInfo (k : Nat) where
  constructor A
  orig   : Fin k
  atom   : Elem
  column : Nat

0 Atoms : Nat -> Type
Atoms k = Vect k Elem

0 Rings : Nat -> Type
Rings k = List (Nat, RingInfo k)

0 Bonds : Nat -> Type
Bonds k = List (Edge k Bond)

0 Stack : Nat -> Type
Stack = List . AtomInfo

lookupRing : Nat -> Rings k -> Maybe (RingInfo k)
lookupRing r []        = Nothing
lookupRing r (x :: xs) = case compare r (fst x) of
  LT => Nothing
  EQ => Just (snd x)
  GT => lookupRing r xs

insert : Nat -> RingInfo k -> Rings k -> Rings k
insert r i []        = [(r,i)]
insert r i (x :: xs) = case compare r (fst x) of
  LT => (r,i) :: x :: xs
  _  => x :: insert r i xs

delete : Nat -> Rings k -> Rings k
delete r []        = []
delete r (x :: xs) = case compare r (fst x) of
  LT => x :: delete r xs
  EQ => xs
  GT => x :: delete r xs

--------------------------------------------------------------------------------
--          Weakenings
--------------------------------------------------------------------------------

-- All weakening functions should be optimized away by the
-- Idris compiler. It is paramount to test this by parsing a
-- huge SMILES string, to make sure the SMILES parser runs in
-- linear time.

wring : RingInfo k -> RingInfo (S k)
wring (RI o a b c) = RI (weaken o) a b c

watom : AtomInfo k -> AtomInfo (S k)
watom (A o a b) = A (weaken o) a b

wrings : Rings k -> Rings (S k)
wrings []     = []
wrings ((n,h)::t) = (n, wring h) :: wrings t

wbonds : Bonds k -> Bonds (S k)
wbonds []         = []
wbonds (h::t) = weakenEdge h :: wbonds t

wstack : Stack k -> Stack (S k)
wstack []     = []
wstack (h::t) = watom h :: wstack t

--------------------------------------------------------------------------------
--          Parser
--------------------------------------------------------------------------------

addBond : {k : _} -> Fin k -> Bond -> Bonds (S k) -> Bonds (S k)
addBond n1 b es = edge n1 b :: es

waddBond : {k : _} -> Fin k -> Bond -> Bonds k -> Bonds (S k)
waddBond n1 b es = addBond n1 b (wbonds es)

ringBond : (b,c : Maybe Bond) -> (x,y : Elem) -> Maybe Bond
ringBond Nothing Nothing   x y = Just Sngl
ringBond Nothing (Just x)  _ _ = Just x
ringBond (Just x) Nothing  _ _ = Just x
ringBond (Just x) (Just y) _ _ = if x == y then Just x else Nothing

rings :
     {k : _}
  -> (column : Nat)
  -> Elem
  -> SnocList Ring
  -> Stack k
  -> Rings k
  -> Rings (S k)
  -> Atoms k
  -> Bonds (S k)
  -> (ts   : List (SmilesToken,Nat))
  -> Maybe (Graph Bond Elem)

finalize :
     {k : _}
  -> Stack k
  -> Rings k
  -> Atoms k
  -> Bonds k
  -> Maybe (Graph Bond Elem)
finalize (A _ _ c :: xs) _        _  _ = Nothing
finalize [] ((r,RI _ _ _ c) :: _) _  _ = Nothing
finalize [] []                   as bs = Just $ G k (mkGraphRev as bs)

-- We just got a fresh atom. Now come the optional ring bonds and branches.
-- branched_atom ::= atom ringbond* branch*
chain :
     {k    : Nat}
  -> (orig : Fin k)         -- the node we bind to
  -> (a    : Elem)    -- the atom we bind to
  -> (s    : Stack k)       -- stack of open branches
  -> (r    : Rings k)       -- list of opened ring bonds
  -> (as   : Atoms k)       -- accumulated atoms
  -> (bs   : Bonds k)       -- accumulated bonds
  -> (ts   : List (SmilesToken,Nat))
  -> Maybe (Graph Bond Elem)
chain o a s r as bs [] = finalize s r as bs
chain o a s r as bs ((x,c)::xs) = case x of
  TA a2 rs => rings c a2 rs s r (wrings r) as (waddBond o Sngl bs) xs

  PC => case s of
    A o2 a2 _ :: t => chain o2 a2 t r as bs xs
    []             => Nothing

  PO => case xs of
    (TB b, _) :: (TA a2 rs,d) :: t =>
      rings d a2 rs (A o a c :: s) r (wrings r) as (waddBond o b bs) t
    (TA a2 rs,d) :: t =>
      rings d a2 rs (A o a c :: s) r (wrings r) as (waddBond o Sngl bs) t
    _ => Nothing

  TB b  => case xs of
    (TA a2 rs,d) :: t => rings d a2 rs s r (wrings r) as (waddBond o b bs) t
    _ => Nothing

  Dot => case xs of
    (TA a2 rs,d) :: t => rings d a2 rs s r (wrings r) as (wbonds bs) t
    _             => Nothing

rings c a [<]             s wr r as bs ts = chain last a (wstack s) r (a::as) bs ts
rings c a (xs :< R rn mb) s wr r as bs ts =
  case lookupRing rn wr of
    Nothing => rings c a xs s wr (insert rn (RI last a mb c) r) as bs ts
    Just (RI n a2 mb2 c2) =>
      let Just b := ringBond mb mb2 a a2 | Nothing => Nothing
          r2     := delete rn r
       in rings c a xs s wr r2 as (addBond n b bs) ts

start : List (SmilesToken,Nat) -> Maybe (Graph Bond Elem)
start ((TA a rs,c) :: xs) = rings c a rs [] [] [] [] [] xs
start []                  = Just (G 0 empty)
start ((t,c) :: _)        = Nothing

export
readSmiles : String -> Maybe (Graph Bond Elem)
readSmiles s = lexSmiles s >>= start
