module Text.Smiles.Simple

import Data.Either
import Data.Finite
import Data.Graph.Indexed
import Data.Maybe
import Data.Refined.Bits8
import Data.SnocVect
import Derive.Finite
import Derive.Prelude
import Derive.Refined
import Syntax.T1
import Text.ILex
import Text.ILex.Derive

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

public export
record RingNr where
  constructor MkRingNr
  value : Bits8
  0 prf : value <= 99

export %inline
Interpolation RingNr where
  interpolate n = if n.value >= 10 then "%\{show n.value}" else show n.value

namespace RingNr
  %runElab derive "RingNr" [Show,Eq,Ord,RefinedInteger]

export
Finite RingNr where
  values = mapMaybe refineRingNr [0..99]

public export
data Bond = Sngl | Dbl | Trpl

%runElab derive "Bond" [Show,Eq,Ord,Finite]

export %inline
Interpolation Bond where
  interpolate Sngl = "-"
  interpolate Dbl  = "="
  interpolate Trpl = "#"

public export
record Ring where
  constructor R
  ring   : RingNr
  bond   : Maybe Bond

%runElab derive "Ring" [Show,Eq,Finite]

export
Interpolation Ring where
  interpolate (R r (Just b)) = "\{b}\{r}"
  interpolate (R r Nothing)  = "\{r}"

public export
data Elem = B | C | N | O | F | P

%runElab derive "Elem" [Show,Eq,Ord,Finite]

export
Interpolation Elem where interpolate = show

public export
data SmilesErr : Type where
  RingBondMismatch   : SmilesErr
  UnclosedRing       : SmilesErr
  ManyEntries        : SmilesErr

export
Interpolation SmilesErr where
  interpolate RingBondMismatch = "Ring bonds do not match"
  interpolate UnclosedRing     = "Unclosed ring"
  interpolate ManyEntries      = "More than one molecule"

%runElab derive "SmilesErr" [Eq,Show]

public export
0 SmilesParseErr : Type
SmilesParseErr = ParseError SmilesErr

data DOB : Type where
  No  : DOB
  Dot : DOB
  Bnd : Bond -> DOB

record RingInfo n where
  constructor RI
  start : Fin n
  nr    : RingNr
  atom  : Elem
  bond  : Maybe Bond
  pos   : Position

record AtomInfo n where
  constructor A
  node  : Fin n
  atom  : Elem

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

%inline
drop : List a -> List a
drop (_::t) = t
drop []     = []

%inline
doubleHead : List a -> List a
doubleHead l@(h::_) = h::l
doubleHead []       = []

ringBond : (b,c : Maybe Bond) -> (x,y : Elem) -> Maybe Bond
ringBond Nothing Nothing   x y = Just Sngl
ringBond Nothing (Just x)  _ _ = Just x
ringBond (Just x) Nothing  _ _ = Just x
ringBond (Just x) (Just y) _ _ = if x == y then Just x else Nothing

lookupRing : RingNr -> List (RingInfo n) -> Maybe (RingInfo n)
lookupRing r []      = Nothing
lookupRing r (x::xs) = case compare r (nr x) of
  LT => Nothing
  EQ => Just x
  GT => lookupRing r xs

insert : RingInfo n -> List (RingInfo n) -> List (RingInfo n)
insert r []      = [r]
insert r (x::xs) = if r.nr < x.nr then r::x::xs else x::insert r xs

delete : RingNr -> List (RingInfo n) -> List (RingInfo n)
delete r []      = []
delete r (x::xs) = if r == x.nr then xs else x::delete r xs

ringBondMismatch : Ring -> Position -> BoundedErr SmilesErr
ringBondMismatch r p =
 let bs := BS p $ addCol (length "\{r}") p
  in B (Custom RingBondMismatch) bs

record ST where
  constructor S
  cnt   : Nat
  stck  : List (AtomInfo cnt)
  atoms : SnocVect cnt Elem
  bonds : List (Edge cnt Bond)
  rings : List (RingInfo cnt)

public export
0 SmilesGraph : Type
SmilesGraph = Graph Bond Elem

empty : ST
empty = S 0 [] [<] [] []

toGraph : ST -> Either (BoundedErr SmilesErr) SmilesGraph
toGraph (S n _ a b [])                 = Right $ G n (mkGraph (cast a) b)
toGraph (S _ _ _ _ (RI _ r _ b p ::_)) =
 let bs := BS p $ addCol (length "\{R r b}") p
  in Left $ B (Custom UnclosedRing) bs

weakenST : List (AtomInfo n) -> List (AtomInfo $ S n)
weakenST x = believe_me x

weakenBS : List (Edge n e) -> List (Edge (S n) e)
weakenBS x = believe_me x

weakenRS : List (RingInfo n) -> List (RingInfo (S n))
weakenRS x = believe_me x

plainAtom : Elem -> ST -> ST
plainAtom a1 (S c (A n a::ss) sa bs rs) =
  let bs2 := edge n Sngl :: weakenBS bs
      st2 := A last a1 :: weakenST ss
   in S (S c) st2 (sa:<a1) bs2 (weakenRS rs)
plainAtom a1 st = st

atomWithBond : Bond -> Elem -> ST -> ST
atomWithBond b a1 (S c (A n _::ss) sa bs rs) =
  let bs2 := edge n b :: weakenBS bs
      st2 := A last a1 :: weakenST ss
   in S (S c) st2 (sa:<a1) bs2 (weakenRS rs)
atomWithBond b a1 st = st

dottedAtom : Elem -> ST -> ST
dottedAtom a1 (S c st sa bs rs) =
  S (S c) (A last a1 :: weakenST st) (sa:<a1) (weakenBS bs) (weakenRS rs)

addRing : Position -> Ring -> ST -> Either (BoundedErr SmilesErr) ST
addRing p (R r mb1) st =
  case st.stck of
    A n1 a1::_ => case lookupRing r st.rings of
      Just (RI n2 nr a2 mb2 p) => case ringBond mb1 mb2 a1 a2 of
        Just b  => case mkEdge n1 n2 b of
          Just e  => Right $ {bonds $= (e::), rings $= delete r} st
          Nothing => Right st -- impossible
        Nothing => Left (ringBondMismatch (R r mb1) p)
      Nothing => Right $ {rings $= insert (RI n1 r a1 mb1 p)} st
    [] => Right st -- impossible

--------------------------------------------------------------------------------
--          Parser
--------------------------------------------------------------------------------

export
record SSTCK (q : Type) where
  constructor SS
  line_      : Ref q Nat
  col_       : Ref q Nat
  positions_ : Ref q (SnocList Position)
  st         : Ref q ST
  dob        : Ref q DOB
  bytes_     : Ref q ByteString
  error_     : Ref q (Maybe $ BoundedErr SmilesErr)
  stack_     : Ref q (SnocList SmilesGraph)

%runElab derive "SSTCK" [HasPosition, HasBytes, HasError, HasStack]

init : F1 q (SSTCK q)
init = T1.do
  l   <- ref1 Z
  c   <- ref1 Z
  p   <- ref1 [<]
  s   <- ref1 empty
  db  <- ref1 Dot
  b   <- ref1 ByteString.empty
  er  <- ref1 Nothing
  st  <- ref1 [<]
  pure (SS l c p s db b er st)

%runElab deriveParserState "SSz" "SST"
  [ "Chain", "NewBranch", "SRing", "Closed", "Err", "Atom" ]

endGraph : SSTCK q -> F1 q (Maybe (BoundedErr SmilesErr))
endGraph sk = T1.do
  st    <- replace1 sk.st empty
  write1 sk.dob Dot
  let Right g := toGraph st | Left err => pure (Just err)
  [<] <- replace1 sk.positions_ [<]
    | _:<p => pure $ Just (B (Unclosed "(") (BS p (incCol p)))
  case g.order of
    0 => pure Nothing
    _ => push1 sk.stack_ g >> pure Nothing

onAtom : Elem -> Step1 q SSz SSTCK
onAtom a = \(sk # t) =>
 let s # t := read1 sk.st t
  in case read1 sk.dob t of
       No    # t => writeAs sk.st (plainAtom a s) SRing t
       Bnd b # t =>
        let _ # t := write1 sk.dob No t
         in writeAs sk.st (atomWithBond b a s) SRing t
       Dot # t  =>
        let _ # t := write1 sk.dob No t
         in writeAs sk.st (dottedAtom a s) SRing t

onRing : Ring -> Step1 q SSz SSTCK
onRing r = \(sk # t) =>
  let p # t := getPosition t
      s # t := read1 sk.st t
   in case addRing p r s of
        Right s2 => writeAs sk.st s2 SRing t
        Left  x  => failWith x Err t

atom : List (RExp True, Step q SSz SSTCK)
atom = vals interpolate onAtom values

ring : List (RExp True, Step q SSz SSTCK)
ring = vals interpolate onRing values

bond : List (RExp True, Step q SSz SSTCK)
bond = cexpr '.' dot :: vals interpolate wrt values
  where
    %inline wrt   : Bond -> Step1 q SSz SSTCK
    wrt b = \(sk # t) => writeAs sk.dob (Bnd b) Atom t

    dot : (k : SSTCK q) => F1 q SST
    dot = writeAs k.dob Dot Atom

openClose : List (RExp True, Step q SSz SSTCK)
openClose = [copen '(' opn, cclose ')' cls]
  where
    opn,cls : (k : SSTCK q) => F1 q SST
    opn = read1 k.st >>= \s => writeAs k.st ({stck $= doubleHead} s) NewBranch
    cls = read1 k.st >>= \s => writeAs k.st ({stck $= drop} s) Closed

space : List (RExp True, Step q SSz SSTCK)
space = [conv (plus $ oneof [' ', '\t']) (const end), newline nl end]
  where
    nl : RExp True
    nl = "\r\n" <|> '\n' <|> '\r'

    end : (sk : SSTCK q) => F1 q SST
    end = T1.do
      Nothing <- endGraph sk | Just x => failWith x Err
      pure Chain

smilesTrans : Lex1 q SSz SSTCK
smilesTrans =
  lex1
    [ E Chain     $ dfa (atom ++ space)
    , E Atom      $ dfa atom
    , E SRing     $ dfa (atom ++ ring ++ bond ++ openClose ++ space)
    , E NewBranch $ dfa (atom ++ bond)
    , E Closed    $ dfa (atom ++ bond ++ openClose ++ space)
    ]

smilesErr : Arr32 SSz (SSTCK q -> F1 q (BoundedErr SmilesErr))
smilesErr = arr32 SSz (unexpected []) []

smilesEOI :
     SST
  -> SSTCK q
  -> F1 q (Either (BoundedErr SmilesErr) (List SmilesGraph))
smilesEOI st sk =
  case st == Chain || st == SRing || st == Closed of
    False => arrFail SSTCK smilesErr st sk
    True  => endGraph sk >>= \case
      Just x  => pure (Left x)
      Nothing => getList sk.stack_ >>= pure . Right

export
smiles : P1 q (BoundedErr SmilesErr) SSz SSTCK (List SmilesGraph)
smiles = P Chain init smilesTrans snocChunk smilesErr smilesEOI

||| Parses a list of smiles codes separated by whitespace
export %inline
parseSmiles : Origin -> String -> Either SmilesParseErr (List SmilesGraph)
parseSmiles = parseString smiles

export
readSmilesFrom : Origin -> String -> Either SmilesParseErr SmilesGraph
readSmilesFrom o s =
  case parseSmiles o s of
    Left  x   => Left x
    Right []  => Right (G 0 empty)
    Right [g] => Right g
    Right _   =>
      Left (toParseError o s (B (Custom ManyEntries) NoBounds))

export %inline
readSmiles : String -> Maybe SmilesGraph
readSmiles = eitherToMaybe . readSmilesFrom Virtual

export %inline
readSmilesOrEmpty : String -> SmilesGraph
readSmilesOrEmpty = fromMaybe (G 0 empty) . readSmiles
