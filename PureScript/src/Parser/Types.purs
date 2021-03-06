module Parser.Types where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.Bifunctor (class Bifunctor)
import Data.Either (Either(..), hush)
import Data.Filterable (filterMap)
import Data.Generic.Rep (class Generic)
import Data.Map (Map, SemigroupMap)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Show.Generic (genericShow)
import Data.String (CodePoint)
import Data.String.NonEmpty as NES
import Data.String.NonEmpty.Internal (NonEmptyString)
import Data.Traversable (mapAccumL)
import Data.Tuple.Nested (type (/\))
import Parser.Proto as Proto

newtype Grammar nt r tok = MkGrammar
  (Array (GrammarRule nt r tok))
derive newtype instance showGrammar :: (Show nt, Show r, Show tok) => Show (Grammar nt r tok)
derive instance newtypeGrammar :: Newtype (Grammar nt r tok) _

type GrammarRule nt r tok =
  { pName :: nt -- nonterminal / production rule name
  , rName :: r -- each rule has a unique name
  , rule :: Fragment nt tok -- sequence of nonterminals and terminals that make up the rule
  }

getRulesFor :: forall nt r tok. Eq nt => Array (Produced nt r tok) -> nt -> Array { rule :: Fragment nt tok, produced :: Array tok }
getRulesFor rules nt = rules # filterMap \rule ->
  if rule.production.pName /= nt then Nothing
  else
    Just { rule: rule.production.rule, produced: rule.produced }

type Produced nt r tok =
  { production :: GrammarRule nt r tok
  , produced :: Array tok
  }

type Produceable nt r tok =
  { grammar :: Augmented nt r tok
  , produced :: Array (Produced nt r tok)
  }

type SProduceable = Produceable NonEmptyString String CodePoint

type Augmented nt r tok =
  { augmented :: Grammar nt r tok
  , start :: StateItem nt r tok
  , eof :: tok
  , entry :: nt
  }

type SAugmented = Augmented NonEmptyString String CodePoint



type SGrammar = Grammar NonEmptyString String CodePoint
data Part nt tok = NonTerminal nt | Terminal tok

derive instance eqPart :: (Eq nt, Eq tok) => Eq (Part nt tok)
derive instance ordPart :: (Ord nt, Ord tok) => Ord (Part nt tok)
derive instance genericPart :: Generic (Part state tok) _
instance showPart :: (Show nt, Show tok) => Show (Part nt tok) where
  show x = genericShow x

derive instance functorPart :: Functor (Part nt)
instance bifunctorPart :: Bifunctor Part where
  bimap f _ (NonTerminal nt) = NonTerminal (f nt)
  bimap _ g (Terminal tok) = Terminal (g tok)

type SPart = Part NonEmptyString CodePoint

isNonTerminal :: forall nt tok. Part nt tok -> Boolean
isNonTerminal (NonTerminal _) = true
isNonTerminal _ = false

isTerminal :: forall nt tok. Part nt tok -> Boolean
isTerminal (Terminal _) = true
isTerminal _ = false

unNonTerminal :: forall nt tok. Part nt tok -> Maybe nt
unNonTerminal (NonTerminal nt) = Just nt
unNonTerminal _ = Nothing

unTerminal :: forall nt tok. Part nt tok -> Maybe tok
unTerminal (Terminal t) = Just t
unTerminal _ = Nothing

unSPart :: SPart -> String
unSPart = NES.toString <<< unSPart'

unSPart' :: SPart -> NonEmptyString
unSPart' (Terminal t) = NES.singleton t
unSPart' (NonTerminal nt) = nt

type Fragment nt tok = Array (Part nt tok)
type SFragment = Fragment NonEmptyString CodePoint

data Zipper nt tok = Zipper (Fragment nt tok) (Fragment nt tok)

derive instance eqZipper :: (Eq nt, Eq tok) => Eq (Zipper nt tok)
derive instance ordZipper :: (Ord nt, Ord tok) => Ord (Zipper nt tok)
derive instance genericZipper :: Generic (Zipper nt tok) _
instance showZipper :: (Show nt, Show tok) => Show (Zipper nt tok) where
  show x = genericShow x

type SZipper = Zipper NonEmptyString CodePoint

unZipper :: forall nt tok. Zipper nt tok -> Fragment nt tok
unZipper (Zipper before after) = before <> after

newtype State nt r tok = State (Array (StateItem nt r tok))
derive instance newtypeState :: Newtype (State nt r tok) _

instance eqState :: (Eq nt, Eq r, Eq tok) => Eq (State nt r tok) where
  eq (State s1) (State s2) = s1 == s2 ||
    let
      State s1' = minimizeState s1
      State s2' = minimizeState s2
      State s12 = minimizeState (s1' <> s2')
      State s21 = minimizeState (s2' <> s1')
    in
      s1' == s12 && s2' == s21

instance ordState :: (Ord nt, Ord r, Ord tok) => Ord (State nt r tok) where
  compare (State s1) (State s2) = compare (deepSort s1) (deepSort s2)
    where
    deepSort = Array.sort <<< map \item ->
      item { lookahead = Array.sort item.lookahead }

derive instance genericState :: Generic (State nt r tok) _
instance showState :: (Show nt, Show r, Show tok) => Show (State nt r tok) where
  show = genericShow

instance semigroupState :: (Eq nt, Eq r, Eq tok) => Semigroup (State nt r tok) where
  append (State s1) (State s2) = minimizeState (s1 <> s2)

minimizeState :: forall nt r tok. Eq nt => Eq r => Eq tok => Array (StateItem nt r tok) -> State nt r tok
minimizeState = compose State $ [] # Array.foldl \items newItem ->
  let
    accumulate :: Boolean -> StateItem nt r tok -> { accum :: Boolean, value :: StateItem nt r tok }
    accumulate alreadyFound item =
      if item.rName == newItem.rName && item.rule == newItem.rule then { accum: true, value: item { lookahead = Array.nubEq (item.lookahead <> newItem.lookahead) } }
      else { accum: alreadyFound, value: item }
    { accum: found, value: items' } =
      mapAccumL accumulate false items
  in
    if found then items' else items' <> [ newItem ]

type SState = State NonEmptyString String CodePoint
type Lookahead tok = Array tok
type StateItem nt r tok =
  { rName :: r
  , pName :: nt
  , rule :: Zipper nt tok
  , lookahead :: Lookahead tok
  }

type SStateItem = StateItem NonEmptyString String CodePoint

data ShiftReduce s r
  = Shift s
  | Reduces (NonEmptyArray r)
  | ShiftReduces s (NonEmptyArray r)

derive instance genericShiftReduce :: Generic (ShiftReduce s r) _
instance showShiftReduce :: (Show s, Show r) => Show (ShiftReduce s r) where
  show = genericShow

unShift :: forall s r. ShiftReduce s r -> Maybe s
unShift (Shift s) = Just s
unShift (ShiftReduces s _) = Just s
unShift (Reduces _) = Nothing

-- Prefer shifts because they are unique
decide :: forall s r. ShiftReduce s r -> Maybe (Either s r)
decide (Shift s) = Just (Left s)
decide (ShiftReduces s _) = Just (Left s)
decide (Reduces r) = if NEA.length r == 1 then Just (Right (NEA.head r)) else Nothing

derive instance functorShiftReduce :: Functor (ShiftReduce s)
instance semigroupShiftReduce :: Semigroup (ShiftReduce s r) where
  -- We do not expect to see two shifts, so arbitrarily prefer the first one
  append (Shift s) (Shift _) = Shift s
  append (Shift s) (ShiftReduces _ rs) = ShiftReduces s rs
  append (ShiftReduces s rs) (Shift _) = ShiftReduces s rs
  append (ShiftReduces s rs) (ShiftReduces _ rs') = ShiftReduces s (rs <> rs')
  append (Shift s) (Reduces rs) = ShiftReduces s rs
  append (Reduces rs) (Shift s) = ShiftReduces s rs
  append (Reduces rs) (Reduces rs') = Reduces (rs <> rs')
  append (ShiftReduces s rs) (Reduces rs') = ShiftReduces s (rs <> rs')
  append (Reduces rs) (ShiftReduces s rs') = ShiftReduces s (rs <> rs')

type StateInfo s nt r tok =
  { sName :: s
  , items :: State nt r tok
  , advance :: SemigroupMap tok (ShiftReduce s (nt /\ r))
  , receive :: Map nt s
  }

type SStateInfo = StateInfo Int NonEmptyString String CodePoint

newtype States s nt r tok = States
  (Array (StateInfo s nt r tok))

derive instance newtypeStates :: Newtype (States s nt r tok) _

type SStates = States Int NonEmptyString String CodePoint



data CST r tok
  = Leaf tok
  | Branch r (Array (CST r tok))

type SCST = CST (NonEmptyString /\ String) CodePoint

derive instance genericCST :: Generic (CST r tok) _
instance showCST :: (Show r, Show tok) => Show (CST r tok) where
  show x = genericShow x

data AST r = Layer r (Array (AST r))
type SAST = AST (NonEmptyString /\ String)

derive instance functorAST :: Functor AST
derive instance genericAST :: Generic (AST r) _
instance showAST :: (Show r) => Show (AST r) where
  show x = genericShow x

prune :: forall r tok. CST r tok -> Either tok (AST r)
prune (Leaf tok) = Left tok
prune (Branch r rec) = Right (Layer r (Array.mapMaybe (hush <<< prune) rec))

type StateIndex s = Map s Int
type SStateIndex = StateIndex Int

type SCTable = Proto.Table Int (NonEmptyString /\ String) CodePoint SCST
type SATable = Proto.Table Int (NonEmptyString /\ String) CodePoint (Either CodePoint SAST)

type SAStack = Proto.Stack Int (Either CodePoint SAST)
type SCStack = Proto.Stack Int SCST
type SAParseSteps = Proto.ParseSteps (NonEmptyString /\ String) CodePoint SAStack
type SCParseSteps = Proto.ParseSteps (NonEmptyString /\ String) CodePoint SCStack
