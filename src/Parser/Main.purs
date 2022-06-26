module Parser.Main where

import Prelude

import Bolson.Core (Child(..), dyn, envy, fixed)
import Control.Alt ((<|>))
import Control.Apply (lift2)
import Control.Monad.ST.Class (class MonadST)
import Control.Monad.State (StateT, get, put, runStateT)
import Control.Monad.Trampoline (Trampoline, runTrampoline)
import Control.Plus (empty)
import Data.Array ((..))
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Array.NonEmpty.Internal (NonEmptyArray)
import Data.Bifunctor (class Bifunctor, bimap, lmap)
import Data.Compactable (compact)
import Data.DateTime.Instant (unInstant)
import Data.Either (Either(..), fromRight', hush, note)
import Data.Foldable (foldMap, for_, oneOf, oneOfMap)
import Data.Function (on)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Generic.Rep (class Generic)
import Data.Int (floor)
import Data.List (List)
import Data.Map (Map, SemigroupMap(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust, fromMaybe)
import Data.Newtype (class Newtype, unwrap)
import Data.Number (e, pi)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.String (CodePoint, codePointFromChar)
import Data.String as String
import Data.String.NonEmpty (fromString, toString)
import Data.String.NonEmpty as NES
import Data.String.NonEmpty.Internal (NonEmptyString)
import Data.Time.Duration (Seconds(..))
import Data.Traversable (mapAccumL, traverse)
import Data.TraversableWithIndex (traverseWithIndex)
import Data.Tuple (fst, snd)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Variant (Variant)
import Data.Variant as V
import Data.Variant as Variant
import Deku.Attribute (class Attr, Attribute, cb, (:=))
import Deku.Control (switcher, text, text_)
import Deku.Core (class Korok, Domable, Nut, bus, bussed)
import Deku.Core (vbussed)
import Deku.Core as DC
import Deku.DOM as D
import Deku.Listeners (click, slider)
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Aff.AVar as AVar
import Effect.Class (liftEffect)
import Effect.Class.Console (logShow)
import Effect.Class.Console as Log
import Effect.Now (now)
import Effect.Unsafe (unsafePerformEffect)
import FRP.Behavior (step)
import FRP.Event (class IsEvent, AnEvent, bang, filterMap, fold, fromEvent, keepLatest, mapAccum, memoize, sampleOn, subscribe, sweep, toEvent, withLast)
import FRP.Event.AnimationFrame (animationFrame)
import FRP.Event.Class (biSampleOn)
import FRP.Event.Time (withTime)
import FRP.Event.VBus (V)
import FRP.Rate (Beats(..), RateInfo, timeFromRate)
import FRP.SampleJIT (sampleJIT)
import FRP.SelfDestruct (selfDestruct)
import Parser.Proto (ParseSteps(..), Stack(..), parseSteps, topOf)
import Parser.Proto as Proto
import Parser.ProtoG8 as G8
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import Type.Proxy (Proxy(..))
import Web.Event.Event (target)
import Web.HTML.HTMLInputElement (fromEventTarget, value)

data StepAction = Initial | Toggle | Slider | Play

type Nuts =
  forall s m lock payload
   . DC.Korok s m
  => Array (DC.Domable m lock payload)

newtype Grammar nt r tok = MkGrammar
  ( Array
      { pName :: nt
      , rName :: r
      , rule :: Fragment nt tok
      }
  )
derive instance newtypeGrammar :: Newtype (Grammar nt r tok) _

fromSeed
  :: forall nt r tok
   . Grammar nt r tok
  -> nt
  -> { augmented :: Grammar (Maybe nt) (Maybe r) (Maybe tok)
     , start :: StateItem (Maybe nt) (Maybe r) (Maybe tok)
     }
fromSeed (MkGrammar rules) entry =
  let
    rule0 = { pName: Nothing, rName: Nothing, rule: [ NonTerminal (Just entry), Terminal Nothing ] }
    rules' = rules <#> \{ pName, rName, rule } ->
      { pName: Just pName
      , rName: Just rName
      , rule: bimap Just Just <$> rule
      }
  in
    { augmented: MkGrammar ([ rule0 ] <> rules')
    , start: { pName: Nothing, rName: Nothing, rule: Zipper [] rule0.rule, lookahead: [] }
    }

fromSeed'
  :: forall nt r tok
   . nt
  -> r
  -> tok
  -> Grammar nt r tok
  -> nt
  -> { augmented :: Grammar nt r tok
     , start :: StateItem nt r tok
     }
fromSeed' nt0 r0 tok0 (MkGrammar rules) entry =
  let
    rule0 = { pName: nt0, rName: r0, rule: [ NonTerminal entry, Terminal tok0 ] }
  in
    { augmented: MkGrammar ([ rule0 ] <> rules)
    , start: { pName: nt0, rName: r0, rule: Zipper [] rule0.rule, lookahead: [] }
    }

generate
  :: forall nt r tok
   . Ord nt
  => Eq r
  => Ord tok
  => Grammar nt r tok
  -> nt
  -> Array (State (Maybe nt) (Maybe r) (Maybe tok))
generate initial entry =
  let
    { augmented: grammar, start } = fromSeed initial entry
  in
    closeStates grammar [ close grammar (minimizeState [ start ]) ]

generate'
  :: forall nt r tok
   . Ord nt
  => Eq r
  => Ord tok
  => nt
  -> r
  -> tok
  -> Grammar nt r tok
  -> nt
  -> Array (State nt r tok)
generate' nt0 r0 tok0 initial entry =
  let
    { augmented: grammar, start } = fromSeed' nt0 r0 tok0 initial entry
  in
    closeStates grammar [ close grammar (minimizeState [ start ]) ]

getResult :: forall x y z. Stack x (Either y z) -> Maybe z
getResult (Snoc (Snoc (Zero _) (Right result) _) (Left _) _) = Just result
getResult _ = Nothing

g8Grammar :: Grammar G8.Sorts G8.Rule G8.Tok
g8Grammar = MkGrammar
  [ { pName: G8.RE, rName: G8.RE1, rule: [ Terminal G8.LParen, NonTerminal G8.RL, Terminal G8.RParen ] }
  , { pName: G8.RE, rName: G8.RE2, rule: [ Terminal G8.X ] }
  , { pName: G8.RL, rName: G8.RL1, rule: [ NonTerminal G8.RE ] }
  , { pName: G8.RL, rName: G8.RL2, rule: [ NonTerminal G8.RL, Terminal G8.Comma, NonTerminal G8.RE ] }
  ]

parseIntoGrammar = compose MkGrammar $
  Array.mapMaybe (\r -> NES.fromString r.pName <#> \p -> r { pName = p })
  >>> \grammar ->
    let
      nts = longestFirst (grammar <#> _.pName)
      p = parseDefinition nts
    in grammar <#> \r -> r { rule = p r.rule }

exGrammar :: SGrammar
exGrammar = parseIntoGrammar
  [ { pName: "E", rName: "E1", rule: "(L)" }
  , { pName: "E", rName: "E2", rule: "x" }
  , { pName: "L", rName: "L1", rule: "E" }
  , { pName: "L", rName: "L2", rule: "L,E" }
  ]

g8Seed
  :: { augmented :: Grammar (Maybe G8.Sorts) (Maybe G8.Rule) (Maybe G8.Tok)
     , start :: StateItem (Maybe G8.Sorts) (Maybe G8.Rule) (Maybe G8.Tok)
     }
g8Seed = fromSeed g8Grammar G8.RE

exSeed ::
  { augmented :: SGrammar
  , start :: SStateItem
  }
exSeed = fromSeed' (unsafePartial (fromJust (NES.fromString "T"))) "T0" (codePointFromChar '$') exGrammar (unsafePartial (fromJust (NES.fromString "E")))

g8Generated :: forall a. a -> Array (State (Maybe G8.Sorts) (Maybe G8.Rule) (Maybe G8.Tok))
g8Generated _ = generate g8Grammar G8.RE

exGenerated _ = generate' (unsafePartial (fromJust (NES.fromString "T"))) "T0" (codePointFromChar '$') exGrammar (unsafePartial (fromJust (NES.fromString "E")))

g8States :: forall a. a -> States Int (Maybe G8.Sorts) (Maybe G8.Rule) (Maybe G8.Tok)
g8States a = fromRight' (\_ -> unsafeCrashWith "state generation did not work")
  (numberStates (add 1) g8Seed.augmented (g8Generated a))

exStates a = fromRight' (\_ -> unsafeCrashWith "state generation did not work")
  (numberStates (add 1) exSeed.augmented (exGenerated a))

g8Table :: forall a. a -> Proto.Table Int (Maybe G8.Sorts /\ Maybe G8.Rule) (Maybe G8.Tok) (CST (Maybe G8.Sorts /\ Maybe G8.Rule) (Maybe G8.Tok))
g8Table = toTable <<< g8States

exTable = toTable <<< exStates

g8Table' :: forall a. a -> Proto.Table Int (Maybe G8.Sorts /\ Maybe G8.Rule) (Maybe G8.Tok) (Either (Maybe G8.Tok) (AST (Maybe G8.Sorts /\ Maybe G8.Rule)))
g8Table' = toTable' <<< g8States

exTable' = toTable' <<< exStates

g8FromString :: String -> Maybe (List (Maybe G8.Tok))
g8FromString = G8.g8FromString >>> map map map case _ of
  G8.EOF -> Nothing
  t -> Just t

verifyTokens :: forall nt r tok. Ord tok => Grammar nt r tok -> List tok -> Maybe (List tok)
verifyTokens = traverse <<< verifyToken

verifyToken :: forall nt r tok. Ord tok => Grammar nt r tok -> tok -> Maybe tok
verifyToken = gatherTokens >>> \toks tok ->
  if Set.member tok toks then Just tok else Nothing

gatherTokens :: forall nt r tok. Ord tok => Grammar nt r tok -> Set tok
gatherTokens (MkGrammar rules) = rules # Array.foldMap \{ rule } ->
  Array.mapMaybe unTerminal rule # Set.fromFoldable

exFromString :: String -> Maybe (List CodePoint)
exFromString = flip append "$" >>> String.toCodePointArray >>> Array.toUnfoldable >>> verifyTokens exSeed.augmented

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
type Fragment nt tok = Array (Part nt tok)
type SFragment = Fragment String CodePoint

data Zipper nt tok = Zipper (Fragment nt tok) (Fragment nt tok)

derive instance eqZipper :: (Eq nt, Eq tok) => Eq (Zipper nt tok)
derive instance ordZipper :: (Ord nt, Ord tok) => Ord (Zipper nt tok)
derive instance genericZipper :: Generic (Zipper state tok) _
instance showZipper :: (Show nt, Show tok) => Show (Zipper nt tok) where
  show x = genericShow x

type SZipper = Zipper String CodePoint
newtype State nt r tok = State (Array (StateItem nt r tok))

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

derive instance functorShiftReduce :: Functor (ShiftReduce s)
instance semigroupShiftReduce :: Semigroup (ShiftReduce s r) where
  -- We don't expect to see two shifts
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

newtype States s nt r tok = States
  (Array (StateInfo s nt r tok))
type SStates = States String NonEmptyString String CodePoint

numberStates
  :: forall s nt r tok
   . Ord nt
  => Eq r
  => Ord tok
  => (Int -> s)
  -> Grammar nt r tok
  -> Array (State nt r tok)
  -> Either (Array (StateItem nt r tok)) (States s nt r tok)
numberStates ix grammar states = map States $ states #
  traverseWithIndex \i items ->
    let
      findState seed = note seed $ map ix $
        Array.findIndex (eq (close grammar (minimizeState seed))) states
      next = nextSteps items
      reductions = Reduces <$> getReductions items
    in
      ado
        shifts <- traverse (map Shift <<< findState) $ next.terminal
        receive <- traverse findState $ unwrap $ next.nonTerminal
        in
          { sName: ix i
          , items
          , advance: shifts <> reductions
          , receive
          }

getReduction :: forall nt r tok. Ord tok => StateItem nt r tok -> SemigroupMap tok (nt /\ r)
getReduction { pName, rName, rule: Zipper _ [], lookahead } =
  SemigroupMap $ Map.fromFoldable $ (/\) <$> lookahead <@> (pName /\ rName)
getReduction _ = SemigroupMap $ Map.empty

getReductions :: forall nt r tok. Ord tok => State nt r tok -> SemigroupMap tok (NonEmptyArray (nt /\ r))
getReductions (State items) = items # foldMap \item ->
  NEA.singleton <$> getReduction item

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

findNT
  :: forall nt tok
   . Zipper nt tok
  -> Maybe
       { nonterminal :: nt, following :: Array nt, continue :: Maybe tok }
findNT (Zipper _ after) = Array.uncons after >>= case _ of
  { head: NonTerminal nt, tail } ->
    let
      { following, continue } = preview tail
    in
      Just { nonterminal: nt, following, continue }
  _ -> Nothing

preview
  :: forall nt tok
   . Array (Part nt tok)
  -> { following :: Array nt, continue :: Maybe tok }
preview tail = { following, continue }
  where
  { init, rest } = Array.span isNonTerminal tail
  following = Array.mapMaybe unNonTerminal init
  continue = Array.head rest >>= unTerminal

continueOn :: forall tok. Maybe tok -> Lookahead tok -> Lookahead tok
continueOn continue lookahead = case continue of
  Just tok -> [ tok ]
  Nothing -> lookahead

startRules :: forall nt r tok. Eq nt => Grammar nt r tok -> nt -> (Lookahead tok -> Array (StateItem nt r tok))
startRules (MkGrammar rules) p =
  let
    filtered = Array.filter (\{ pName } -> pName == p) rules
  in
    \lookahead -> filtered <#> \{ pName, rName, rule } -> { pName, rName, rule: Zipper [] rule, lookahead }

closeItem :: forall nt r tok. Eq nt => Grammar nt r tok -> StateItem nt r tok -> Array (StateItem nt r tok)
closeItem grammar item = case findNT item.rule of
  Nothing -> []
  Just { nonterminal: p, following, continue } ->
    startRules grammar p $
      firsts grammar following (continueOn continue item.lookahead)

close1 :: forall nt r tok. Eq nt => Grammar nt r tok -> State nt r tok -> Array (StateItem nt r tok)
close1 grammar (State items) = closeItem grammar =<< items

close
  :: forall nt r tok
   . Eq r
  => Eq nt
  => Eq tok
  => Grammar nt r tok
  -> State nt r tok
  -> State nt r tok
close grammar state0 =
  let
    state' = close1 grammar state0
  in
    if Array.null state' then state0
    else
      let
        state = state0 <> State state'
      in
        if state == state0 then state0 else close grammar state

firsts :: forall nt r tok. Eq nt => Grammar nt r tok -> Array nt -> Lookahead tok -> Lookahead tok
firsts (MkGrammar rules0) ps0 lookahead0 = readyset rules0 ps0 lookahead0
  where
  readyset rules ps lookahead = case Array.uncons ps of
    Just { head, tail } -> go rules head tail lookahead
    _ -> lookahead
  go rules p ps lookahead =
    let
      { yes: matches, no: rules' } = Array.partition (\{ pName } -> pName == p) rules
    in
      matches >>= _.rule >>> preview >>> \{ following, continue } ->
        -- (p : following continue) (ps lookahead)
        case continue of
          Just tok -> readyset rules' following [ tok ]
          Nothing -> readyset rules' (following <> ps) lookahead

nextStep
  :: forall nt r tok
   . StateItem nt r tok
  -> { nonTerminal :: SemigroupMap nt (Array (StateItem nt r tok))
     , terminal :: SemigroupMap tok (Array (StateItem nt r tok))
     }
nextStep item@{ rule: Zipper before after } = case Array.uncons after of
  Nothing ->
    { nonTerminal: SemigroupMap Map.empty
    , terminal: SemigroupMap Map.empty
    }
  Just { head, tail } ->
    let
      nextStateSeed = pure
        { pName: item.pName
        , rName: item.rName
        , rule: Zipper (before <> [ head ]) tail
        , lookahead: item.lookahead
        }
    in
      case head of
        NonTerminal nt ->
          { nonTerminal: SemigroupMap (Map.singleton nt nextStateSeed)
          , terminal: SemigroupMap Map.empty
          }
        Terminal tok ->
          { nonTerminal: SemigroupMap Map.empty
          , terminal: SemigroupMap (Map.singleton tok nextStateSeed)
          }

nextSteps
  :: forall nt r tok
   . Ord nt
  => Ord tok
  => State nt r tok
  -> { nonTerminal :: SemigroupMap nt (Array (StateItem nt r tok))
     , terminal :: SemigroupMap tok (Array (StateItem nt r tok))
     }
nextSteps (State items) = Array.foldMap nextStep items

-- Meant to handle nondeterminacy of shifts, but not reduces
nextSteps'
  :: forall nt r tok
   . Ord nt
  => Ord tok
  => State nt r tok
  -> Array (Part nt tok /\ Array (StateItem nt r tok))
nextSteps' state =
  let
    { nonTerminal: SemigroupMap nts, terminal: SemigroupMap toks } = nextSteps state
  in
    lmap Terminal <$> Map.toUnfoldable toks <|> lmap NonTerminal <$> Map.toUnfoldable nts

newStates
  :: forall nt r tok
   . Ord nt
  => Eq r
  => Ord tok
  => Grammar nt r tok
  -> State nt r tok
  -> Array (State nt r tok)
newStates grammar state =
  Array.nubEq (close grammar <<< minimizeState <<< snd <$> nextSteps' state)

closeStates1
  :: forall nt r tok
   . Ord nt
  => Eq r
  => Ord tok
  => Grammar nt r tok
  -> Array (State nt r tok)
  -> Array (State nt r tok)
closeStates1 grammar states = Array.nubEq (states <> (states >>= newStates grammar))

closeStates
  :: forall nt r tok
   . Ord nt
  => Eq r
  => Ord tok
  => Grammar nt r tok
  -> Array (State nt r tok)
  -> Array (State nt r tok)
closeStates grammar states =
  let
    states' = closeStates1 grammar states
  in
    if states' == states then states else closeStates grammar states'

data CST r tok
  = Leaf tok
  | Branch r (Array (CST r tok))

derive instance genericCST :: Generic (CST r tok) _
instance showCST :: (Show r, Show tok) => Show (CST r tok) where
  show x = genericShow x

data AST r = Layer r (Array (AST r))

derive instance functorAST :: Functor AST
derive instance genericAST :: Generic (AST r) _
instance showAST :: (Show r) => Show (AST r) where
  show x = genericShow x

prune :: forall r tok. CST r tok -> Either tok (AST r)
prune (Leaf tok) = Left tok
prune (Branch r rec) = Right (Layer r (Array.mapMaybe (hush <<< prune) rec))

toTable
  :: forall s nt r tok
   . Ord s
  => Ord nt
  => Eq r
  => Ord tok
  => States s nt r tok
  -> Proto.Table s (nt /\ r) tok (CST (nt /\ r) tok)
toTable (States states) =
  let
    tabulated = Map.fromFoldable $ mapWithIndex (\i { sName } -> sName /\ i) states
    lookupState s = Map.lookup s tabulated >>= Array.index states
    lookupAction tok { advance: SemigroupMap m } = Map.lookup tok m
    lookupReduction (p /\ r) { items: State items } = items # oneOfMap case _ of
      { rule: Zipper parsed [], pName, rName } | pName == p && rName == r ->
        Just parsed
      _ -> Nothing
    takeStack r stack0 parsed =
      let
        take1 (taken /\ stack) = case _ of
          Terminal tok -> case stack of
            Snoc stack' v@(Leaf tok') _ | tok == tok' ->
              Just $ (taken <> [ v ]) /\ stack'
            _ -> unsafeCrashWith "expected token on stack"
          NonTerminal nt -> case stack of
            Snoc stack' v@(Branch (p /\ _) _) _ | p == nt ->
              Just $ (taken <> [ v ]) /\ stack'
            _ -> unsafeCrashWith "expected terminal on stack"
      in
        Array.foldM take1 ([] /\ stack0) (Array.reverse parsed) >>= \(taken /\ stack) ->
          Snoc stack (Branch r taken) <$> goto r (topOf stack)
    goto (p /\ _) s' = lookupState s' >>= _.receive >>> Map.lookup p
  in
    Proto.Table
      { promote: Leaf
      , step: \s tok -> lookupState s >>= lookupAction tok >>= decide
      , goto: \r stack ->
          lookupState (topOf stack) >>= \state -> do
            lookupReduction r state >>= takeStack r stack
      }

toTable'
  :: forall s nt r tok
   . Ord s
  => Ord nt
  => Eq r
  => Ord tok
  => States s nt r tok
  -> Proto.Table s (nt /\ r) tok (Either tok (AST (nt /\ r)))
toTable' (States states) =
  let
    tabulated = Map.fromFoldable $ mapWithIndex (\i { sName } -> sName /\ i) states
    lookupState s = Map.lookup s tabulated >>= Array.index states
    lookupAction tok { advance: SemigroupMap m } = Map.lookup tok m
    lookupReduction (p /\ r) { items: State items } = items # oneOfMap case _ of
      { rule: Zipper parsed [], pName, rName } | pName == p && rName == r ->
        Just parsed
      _ -> Nothing
    takeStack r stack0 parsed =
      let
        take1 (taken /\ stack) = case _ of
          Terminal tok -> case stack of
            Snoc stack' v@(Left tok') _ | tok == tok' ->
              Just $ (taken <> [ v ]) /\ stack'
            _ -> unsafeCrashWith "expected token on stack"
          NonTerminal nt -> case stack of
            Snoc stack' v@(Right (Layer (p /\ _) _)) _ | p == nt ->
              Just $ (taken <> [ v ]) /\ stack'
            _ -> unsafeCrashWith "expected terminal on stack"
      in
        Array.foldM take1 ([] /\ stack0) (Array.reverse parsed) >>= \(taken /\ stack) ->
          Snoc stack (Right (Layer r (Array.mapMaybe hush taken))) <$> goto r (topOf stack)
    goto (p /\ _) s' = lookupState s' >>= _.receive >>> Map.lookup p
  in
    Proto.Table
      { promote: Left
      , step: \s tok -> lookupState s >>= lookupAction tok >>= decide
      , goto: \r stack ->
          lookupState (topOf stack) >>= \state -> do
            lookupReduction r state >>= takeStack r stack
      }

-- Prefer shifts because they are unique
decide :: forall s r. ShiftReduce s r -> Maybe (Either s r)
decide (Shift s) = Just (Left s)
decide (ShiftReduces s _) = Just (Left s)
decide (Reduces r) = if NEA.length r == 1 then Just (Right (NEA.head r)) else Nothing

longestFirst :: Array NonEmptyString -> Array NonEmptyString
longestFirst = Array.sortBy (compare `on` NES.length)

parseDefinition :: Array NonEmptyString -> String -> Fragment NonEmptyString CodePoint
parseDefinition nts s = case String.uncons s of
  Just { head: c, tail: s' } ->
    case recognize nts s of
      Just nt -> [ NonTerminal nt ] <> parseDefinition nts (String.drop (NES.length nt) s)
      Nothing -> [ Terminal c ] <> parseDefinition nts s'
  Nothing -> []

recognize :: Array NonEmptyString -> String -> Maybe NonEmptyString
recognize nts s = nts # Array.find \nt ->
  String.take (NES.length nt) s == NES.toString nt

buttonClass = bang $ D.Class := "bg-blue-500 hover:bg-blue-700 text-white font-bold py-2 px-4 rounded"
arrowClass = bang $ D.Class := "bg-green-500 hover:bg-green-700 text-white font-bold"
inputClass = bang $ D.Class := "shadow appearance-none border rounded py-2 px-3 text-gray-700 leading-tight focus:outline-none focus:shadow-outline"
type Header nt tok = Array tok /\ Array nt

getHeader :: forall s nt r tok. Ord nt => Ord tok => States s nt r tok -> Header nt tok
getHeader (States states) = bimap Array.nub Array.nub $
  states # foldMap \{ items: State items } -> items # foldMap \item ->
    ([] /\ [ item.pName ]) <> foldZipper fromPart item.rule
  where
  foldZipper f (Zipper l r) = foldMap f l <> foldMap f r
  fromPart (NonTerminal nt) = [] /\ [ nt ]
  fromPart (Terminal tok) = [ tok ] /\ []

renderStateTable
  :: forall s nt r tok
   . Show s
  => Show r
  => Show nt
  => Show tok
  => Ord nt
  => Ord tok
  => States s nt r tok
  -> Nut
renderStateTable (States states) =
  let
    terminals /\ nonTerminals = getHeader (States states)
    renderTerminals = text_ <<< show
    renderNonTerminals = text_ <<< show
    renderShiftReduce Nothing = text_ ""
    renderShiftReduce (Just (Shift s)) = text_ $ "s" <> show s
    renderShiftReduce (Just (Reduces rs)) = text_ $ rs # foldMap \r -> "r" <> show r
    renderShiftReduce (Just (ShiftReduces s rs)) = text_ $
      ("s" <> show s) <> (rs # foldMap \r -> "r" <> show r)
    cols state =
      let
        forTerminal tok = map snd <$> Map.lookup tok (unwrap state.advance)
        forNonTerminal nt = Shift <$> Map.lookup nt state.receive
      in
        map forTerminal terminals <> map forNonTerminal nonTerminals
    header = D.tr_ $ map (D.th_ <<< pure) $
      [ text_ "" ] <> map renderTerminals terminals <> map renderNonTerminals nonTerminals
    rows = states <#> \state -> D.tr_
      $ Array.cons (D.th_ [ text_ (show state.sName) ])
      $
        map (D.td_ <<< pure <<< renderShiftReduce) (cols state)
  in
    D.table_ $ pure $ D.tbody_ $ [ header ] <> rows

type StartingTick = Boolean

type ParsedUIAction = V
  ( toggleLeft :: Unit
  , toggleRight :: Unit
  , slider :: Number
  , rate :: Number
  , startState :: Maybe (Effect Unit)
  , animationTick :: StartingTick /\ RateInfo
  )

data TodoAction = Prioritize | Delete

showStack :: forall tok state. Show state => Show tok => Stack state tok -> Nut
showStack i = fixed (go i)
  where
  go (Zero state) = [ D.sub_ [ text_ (show state) ] ]
  go (Snoc stack tok state) = go stack
    <> [ text_ (show tok) ]
    <> [ D.sub_ [ text_ (show state) ] ]

showMaybeStack :: forall tok state. Show tok => Show state => Maybe (Stack state tok) -> Nut
showMaybeStack Nothing = text_ "Parse error"
showMaybeStack (Just stack) = showStack stack

showMaybeParseSteps :: forall input s m lock payload x y z. Show x => Show y => Show z => Korok s m => Show input => Maybe (ParseSteps input (Stack x (Either y (AST z)))) -> SuperStack m (Domable m lock payload)
showMaybeParseSteps Nothing = pure (pure (text_ "Parse error"))
showMaybeParseSteps (Just stack) = showParseSteps stack

getVisibilityAndIncrement
  :: forall m s element
   . MonadST s m
  => Attr element D.Class String
  => SuperStack m (Int /\ AnEvent m (Attribute element))
getVisibilityAndIncrement = getVisibilityAndIncrement' ""

getVisibilityAndIncrement'
  :: forall m s element
   . MonadST s m
  => Attr element D.Class String
  => String
  -> SuperStack m (Int /\ AnEvent m (Attribute element))
getVisibilityAndIncrement' s = do
  n <- get
  put (n + 1)
  pure
    ( \f -> n /\
        ( f n <#> \v ->
            D.Class := (s <> if v then "" else " hidden")
        )
    )

showParseStep
  :: forall r tok state inputs s m lock payload x y z
   . Show tok
  => Show z
  => Show state
  => Show inputs
  => Korok s m
  => Either (Maybe (Stack x (Either y (AST z))))
       { inputs :: inputs
       , stack :: Stack state tok
       | r
       }
  -> SuperStack m (Domable m lock payload)
showParseStep (Left Nothing) = do
  getVisibilityAndIncrement <#> map \(n /\ vi) ->
    D.div vi [ (text_ $ ("Step " <> show n <> ": ") <> "Parse error") ]
showParseStep (Left (Just v)) = do
  getVisibilityAndIncrement <#> map \(n /\ vi) ->
    case getResult v of
      Just r ->
        D.div vi [ text_ $ ("Step " <> show n <> ": ") <> show r ]
      _ ->
        D.div vi [ text_ $ ("Step " <> show n <> ": ") <> "Something went wrong" ]
showParseStep (Right { stack, inputs }) = do
  getVisibilityAndIncrement' "flex justify-between" <#> map \(n /\ vi) ->
    D.div vi [ D.div_ [ text_ ("Step " <> show n <> ": "), showStack stack ], D.div_ [ text_ (show inputs) ] ]

type SuperStack m a = StateT Int Trampoline ((Int -> AnEvent m Boolean) -> a)

showParseSteps
  :: forall input s m lock payload x y z
   . Show input
  => Show x
  => Show y
  => Show z
  => Korok s m
  => ParseSteps input (Stack x (Either y (AST z)))
  -> SuperStack m (Domable m lock payload)
showParseSteps i = map fixed <$> (go i)
  where
  go =
    let
      s v = showParseStep v
    in
      case _ of
        Error -> do
          s (Left Nothing) <#> map \o -> [ o ]
        (Complete v) -> do
          s (Left (Just v)) <#> map \o -> [ o ]
        (Step step more) -> do
          lift2 (\o r -> [ o ] <> r) <$> s (Right step) <*> go more

renderState :: forall nt r tok. Show nt => Show r => Show tok => State nt r tok -> Nut
renderState (State items) = D.ul_ $ D.li_ <<< (\v -> renderItem v) <$> items

renderItem :: forall nt r tok. Show nt => Show r => Show tok => StateItem nt r tok -> Nuts
renderItem { rName, rule, lookahead } =
  [ D.span (bang (D.Class := "rule name")) [ text_ (show rName) ]
  , text_ ": "
  , renderZipper rule
  , text_ " "
  , D.span (bang (D.Class := "lookahead")) [ text_ (show lookahead) ]
  ]

renderZipper :: forall nt tok. Show nt => Show tok => Zipper nt tok -> Nut
renderZipper (Zipper before after) =
  D.span (bang (D.Class := "zipper"))
    [ D.span (bang (D.Class := "text-gray-400 line-through")) $ text_ <<< show <$> before
    , D.span empty $ text_ <<< show <$> after
    ]

counter :: forall s m a. MonadST s m => AnEvent m a → AnEvent m (a /\ Int)
counter event = mapAccum f event 0
  where
  f a b = (b + 1) /\ (a /\ b)

toggle :: forall s m a b. HeytingAlgebra b => MonadST s m => b -> AnEvent m a → AnEvent m b
toggle start event = bang start <|> fold (\_ x -> not x) event start

withLast' :: forall event a. IsEvent event => event a -> event { last :: a, now :: a }
withLast' = filterMap (\{ last, now } -> last <#> { last: _, now }) <<< withLast

dedup :: forall s m a. Eq a => Applicative m => MonadST s m => AnEvent m a -> AnEvent m a
dedup = dedupOn eq

dedupOn :: forall s m a. (a -> a -> Boolean) -> Applicative m => MonadST s m => AnEvent m a -> AnEvent m a
dedupOn feq e = compact $
  mapAccum (\a b -> let ja = Just a in ja /\ (if (feq <$> b <*> ja) == Just true then Nothing else Just a)) e Nothing

interpolate :: Int -> Int -> Array Int
interpolate i j | i > j = j .. (i - 1)
interpolate i j | i < j = i .. (j - 1)
interpolate _ _ = []

stepByStep :: forall s m r. MonadST s m => Boolean -> AnEvent m Int -> ((Int -> AnEvent m Boolean) -> r) -> AnEvent m r
stepByStep start index cb =
  let
    state = withLast' index
    swept = keepLatest $ map (oneOfMap bang) $
      state <#> \{ last, now } -> interpolate last now
  in
    sweep swept \sweeper ->
      let
        sweeper' = toggle start <<< sweeper
      in
        cb sweeper'

type TopLevelUIAction = V
  ( changeText :: String
  , errorMessage :: Maybe String
  , addRule :: Int /\ NonEmptyString /\ String
  , removeRule :: Int
  )

debug :: forall m a. Show a => String -> AnEvent m a -> AnEvent m a
debug tag = map \a -> unsafePerformEffect (a <$ (Log.info (tag <> show a)))

type ListicleEvent a = Variant ( add :: a, remove :: Int )

-- | Render a list of items, with begin, end, separator elements and finalize button
-- | and remove buttons on each item. (All of those are optional, except for the items.)
-- |
-- | [ begin, ...[ item, remove, separator ]..., end, finalize ]
-- |
-- | Start from an initial value, listen for external add events, internal remove events,
-- | raise messages on change, and return the current value on finalize.
listicle :: forall s m lock payload a. Korok s m => Show a =>
  { initial :: Array a -- initial value
  , addEvent :: AnEvent m a -- external add events

  , remove :: Maybe (Effect Unit -> Domable m lock payload) -- remove button
  , finalize :: Maybe (AnEvent m (Array a) -> Domable m lock payload) -- finalize button

  , renderItem :: a -> Domable m lock payload
  , begin :: Maybe (Domable m lock payload)
  , end :: Maybe (Domable m lock payload)
  , separator :: Maybe (Domable m lock payload)
  } ->
  ComponentSpec m lock payload (Array a)
listicle desc = bus \pushRemove removesEvent ->
  let
    initialValue :: Int /\ Array (Int /\ a)
    initialValue = Array.length desc.initial /\ mapWithIndex (/\) desc.initial
    performChange :: ListicleEvent a -> (Int /\ Array (Int /\ a)) -> (Int /\ Array (Int /\ a))
    performChange = V.match
      { add: \v (j /\ vs) -> (j+1) /\ Array.snoc vs (j /\ v)
      , remove: \i -> map (Array.filter \(i' /\ _) -> i' /= i)
      }
    changesEvent =
      Variant.inj (Proxy :: Proxy "add") <$> desc.addEvent
      <|> Variant.inj (Proxy :: Proxy "remove") <$> removesEvent
    currentValue :: AnEvent m (Array (Int /\ a))
    currentValue = map snd $ bang initialValue <|> fold performChange changesEvent initialValue
    intro = case desc.begin of
      Nothing -> []
      Just x -> [x]
    extro = case desc.end of
      Nothing -> []
      Just x -> [x]
    fin = case desc.finalize of
      Nothing -> []
      Just thingy ->
        [ thingy (currentValue <#> map snd) ]
    sep = case desc.separator of
      Nothing -> []
      Just v -> [v]

    withRemover :: Domable m lock payload -> Int -> Array (Array (Domable m lock payload))
    withRemover item idx = pure $ case desc.remove of
      Nothing -> [item]
      Just remover ->
        [ item, remover (pushRemove idx) ]

    renderOne :: Int /\ a -> Array (Array (Domable m lock payload))
    renderOne (idx /\ item) = withRemover (desc.renderItem item) idx

    renderAtOnce :: Array (Int /\ a) -> Domable m lock payload
    renderAtOnce items = D.div_ $
      let
        renderedItems = items <#> renderOne
      in
        intro <> join (Array.intercalate [sep] renderedItems) <> extro <> fin
  in { element: switcher renderAtOnce (debug "element" currentValue), value: map snd <$> debug "value" currentValue }

-- | Abstract component
type ComponentSpec m lock payload d =
  AnEvent m (Component m lock payload d)
-- | Instantiated component
type Component m lock payload d =
  { element :: Domable m lock payload
  , value :: AnEvent m d
  }

-- | Instantiate a component spec to get an actual component, with its element
-- | and value-event.
-- |
-- | Component specs are eventful so they can maintain state, so they need to
-- | be memoized in order that the element and value refer to the same instance,
-- | otherwise the value is attached to a phantom instance that has no DOM
-- | presence, due to the way busses and subscriptions work.
withInstance :: forall s d m lock payload. Korok s m =>
  ComponentSpec m lock payload d ->
  (Component m lock payload d -> Domable m lock payload) ->
  Domable m lock payload
withInstance componentSpec renderer =
  envy $ memoize componentSpec \component ->
    renderer
      { element: envy (component <#> _.element)
      , value: keepLatest (component <#> _.value)
      }

stateComponent :: forall s m lock payload. Korok s m =>
  Domable m lock payload
stateComponent = bussed \addNew addEvent ->
  let
    component0 = listicle
      { begin: Just $ text_ "{ "
      , end: Just $ text_ " }"
      , separator: Just $ text_ ", "
      , renderItem: text_ <<< show
      , remove: Just \rem -> D.button (bang (D.OnClick := rem)) [ text_ "-" ]
      , finalize: Nothing
      , addEvent: addEvent
      , initial: [0, 1]
      }
  in envy $ memoize component0 \component ->
  let
    element = envy (component <#> _.element)
    value = keepLatest (component <#> _.value)
    length = debug "length outer" (map Array.length (debug "length inner" value))
  in D.div_
      -- Without this div, it comes after the button upon update
      [ D.div_ [ element ]
      , D.button ((length <#> \v -> (D.OnClick := addNew v)) <|> buttonClass) [ text_ "Add" ]
      ]

main :: Nut
main =
  ( vbussed (Proxy :: _ TopLevelUIAction) \push event -> do
      let
        currentValue = bang "" <|> event.changeText
        currentRules = bang [] <|> fold
          ( \change rules ->
              case change of
                Left new -> Array.snoc rules new
                Right remove -> Array.filter (fst >>> not eq remove) rules
          )
          (Left <$> event.addRule <|> Right <$> event.removeRule)
          []
        -- _ = unsafePerformEffect $ subscribe currentRules logShow
        top =
          [ D.input
              ( oneOf
                  [ inputClass
                  , bang $ D.OnInput := cb \e -> for_
                      ( target e
                          >>= fromEventTarget
                      )
                      (value >=> push.changeText)
                  ]
              )
              []
          ]
      D.div_
        [ stateComponent
        , D.div_
            [ event.errorMessage # switcher \et -> case et of
                Nothing -> envy empty
                Just e -> D.div_ [ D.span (bang $ D.Class := "text-red-300") [ text_ e ] ]
            ]
        , envy $ bus \lpush -> \levent ->
            let
              currentText =
                bang (Nothing /\ "") <|> fold
                  (\(x /\ s) b -> if x then (fst b /\ s) else (fromString s /\ snd b))
                  levent
                  (Nothing /\ "")
              counted = bang 0 <|> (add 1 <$> fst <$> event.addRule)
              top' =
                [ D.input
                    ( oneOf
                        [ inputClass
                        , bang $ D.OnInput := cb \e -> for_
                            ( target e
                                >>= fromEventTarget
                            )
                            ( value
                                >=> lpush <<< (/\) false
                            )
                        ]
                    )
                    []
                , D.input
                    ( oneOf
                        [ inputClass
                        , bang $ D.OnInput := cb \e -> for_
                            ( target e
                                >>= fromEventTarget
                            )
                            ( value
                                >=> lpush <<< (/\) true
                            )
                        ]
                    )
                    []
                , D.button
                    ( oneOf
                        [ buttonClass
                        , fromEvent $ sampleJIT (toEvent currentText) $ sampleJIT (toEvent counted)
                            $ bang
                            $ \iR textR -> D.OnClick := launchAff_ do
                                liftEffect $ push.errorMessage Nothing
                                i <- AVar.read iR
                                text <- AVar.read textR
                                case fst text of
                                  Nothing -> liftEffect $ push.errorMessage (Just "The first field in a rule can't be empty.")
                                  Just nes -> liftEffect $ push.addRule (i /\ nes /\ snd text)
                        ]
                    )
                    [ text_ "Add" ]
                ]
            in
              D.div_ $ append top' <<< pure $ dyn $ map
                ( \(i /\ txt) -> keepLatest $ bus \p' e' ->
                    ( bang $ Insert $ D.div_
                        [ text_ (toString (fst txt))
                        , text_ " : "
                        , text_ (snd txt)
                        , text_ " "
                        , D.button
                            ( oneOf
                                [ buttonClass
                                , bang $ D.OnClick := (p' Remove *> push.removeRule i)
                                ]
                            )
                            [ text_ "Delete" ]
                        ]
                    ) <|> e'
                )
                event.addRule
        , D.table_ $ pure $ D.tbody_ $
            D.tr_ <<< map D.td_ <$>
              [ [ [ text_ "E" ], [ text_ ":" ], [ text_ "(", text_ "L", text_ ")" ], [ text_ "data E" ], [ text_ "=" ], [ text_ "E1", text_ " ", text_ "L" ] ]
              , [ [], [ text_ "|" ], [ text_ "x" ], [], [ text_ "|" ], [ text_ "E2" ] ]
              , [ [ text_ "L" ], [ text_ ":" ], [ text_ "E" ], [ text_ "data L" ], [ text_ "=" ], [ text_ "L1", text_ " ", text_ "E" ] ]
              , [ [], [ text_ "|" ], [ text_ "L", text_ ",", text_ "E" ], [], [ text_ "|" ], [ text_ "L2", text_ " ", text_ "L", text_ " ", text_ "E" ] ]
              ]
        , D.ul (bang $ D.Class := "pl-14 list-disc list-outside") $ map (D.li_) $ unwrap exSeed.augmented <#> \{ pName, rule } ->
            append [ text_ (NES.toString pName), text_ ":" ] $ rule <#> text_ <<< show
        , D.div_ $ pure $ D.ol (bang $ D.Class := "pl-14 list-decimal list-outside") $ D.li_ <<< pure <<< (\v -> renderState v) <$> exGenerated unit
        , D.div_ $ pure $ renderStateTable (exStates unit)
        , D.div_ top
        , D.div_ $ pure $ currentValue `flip switcher` \v ->
            let
              contentAsMonad = showMaybeParseSteps $ map (map (map (map (map snd)))) $ parseSteps (exTable' unit) <$> exFromString v <@> 1
              -- Run the first layer of the monad, to get the number of items being rendered up-front
              contentAsMonad2 /\ nEntities = runTrampoline (runStateT contentAsMonad 0)
            in
              vbussed (Proxy :: _ ParsedUIAction) \pPush pEvent ->
                let
                  -- Maintain the current index, clamped between 0 and nEntitities
                  -- (Note: it is automatically reset, since `switcher` resubscribes,
                  -- creating new state for it)
                  startState = pEvent.startState <|> bang Nothing
                  rate = pEvent.rate <|> bang 1.0
                  animationTick = compact $ mapAccum
                    ( \i@(tf /\ { beats: Beats beats }) { target: Beats target' } ->
                        let
                          target = if tf then 0.0 else target'
                        in
                          if target > beats then ({ target: Beats target } /\ Nothing)
                          else ({ target: Beats (target + 1.0) } /\ Just i)
                    )
                    pEvent.animationTick
                    { target: Beats 0.0 }
                  currentIndex = dedupOn (eq `on` fst) $ bang (nEntities /\ Initial) <|>
                    mapAccum
                      (\(f /\ a) x -> let fx = clamp 0 nEntities (f x) in fx /\ fx /\ a)
                      ( oneOf
                          [ ((_ - 1) /\ Toggle) <$ pEvent.toggleLeft
                          , ((_ + 1) /\ Toggle) <$ pEvent.toggleRight
                          -- if we're starting and at the end of a play, loop back to the beginning
                          , (\(tf /\ _) -> if tf then ((\n -> if n == nEntities then 0 else n + 1) /\ Play) else ((_ + 1) /\ Play)) <$> animationTick
                          , (floor >>> const >>> (_ /\ Slider)) <$> pEvent.slider
                          ]
                      )
                      nEntities
                in
                  -- Memoize it and run it through `stepByStep` to toggle each
                  -- item individually
                  envy $ keepLatest $ memoize currentIndex \stackIndex ->
                    stepByStep true (map fst stackIndex) \sweeper ->
                      let
                        content = contentAsMonad2 sweeper
                      in
                        D.div_
                          [ D.div_
                              [ D.button
                                  ( oneOf
                                      [ buttonClass
                                      , (biSampleOn rate ((/\) <$> startState)) <#> \(s /\ rt) -> D.OnClick := do
                                          case s of
                                            Just unsub -> do
                                              unsub
                                              pPush.startState Nothing
                                            Nothing -> do
                                              let toSeconds = unInstant >>> unwrap >>> (_ / 1000.0)
                                              t <- toSeconds <$> now
                                              sub <- subscribe
                                                ( selfDestruct (\((isStart /\ _) /\ ci) -> (fst ci == nEntities && not isStart)) (pPush.startState Nothing)
                                                    ( sampleOn (toEvent currentIndex)
                                                        ( (/\) <$> mapAccum (\i tf -> false /\ tf /\ i)
                                                            ( timeFromRate (step rt $ toEvent pEvent.rate)
                                                                ( _.time
                                                                    >>> toSeconds
                                                                    >>> (_ - t)
                                                                    >>> Seconds <$> withTime (animationFrame)
                                                                )
                                                            )
                                                            true
                                                        )
                                                    )
                                                )
                                                \(info /\ _) -> pPush.animationTick info
                                              pPush.startState (Just sub)
                                      ]
                                  )
                                  [ text
                                      ( startState <#> case _ of
                                          Just _ -> "Pause"
                                          Nothing -> "Play"
                                      )
                                  ]
                              ]
                          , D.div_
                              [ text_ "Speed"
                              , D.span_ $ join $ map
                                  ( \(n /\ l) ->
                                      [ D.input
                                          ( oneOfMap bang
                                              [ D.Xtype := "radio"
                                              , D.Checked := show (l == "1x")
                                              , D.Name := "speed"
                                              , D.Value := show n
                                              , D.OnClick := cb \_ -> pPush.rate n
                                              ]
                                          )
                                          []
                                      , D.label_ [ text_ l ]
                                      ]
                                  )
                                  [ 1.0 /\ "1x", (1.0 / e) /\ "ex", (1.0 / pi) /\ "pix" ]
                              ]
                          , D.div_
                              [ D.input
                                  ( oneOf
                                      [ bang $ D.Xtype := "range"
                                      , bang $ D.Min := "0"
                                      , bang $ D.Max := show nEntities
                                      , stackIndex
                                          # filterMap case _ of
                                              _ /\ Slider -> Nothing
                                              x /\ _ -> Just x
                                          <#> (\si -> D.Value := show si)
                                      , slider $ startState <#> case _ of
                                          Nothing -> pPush.slider
                                          Just unsub -> \n -> pPush.slider n
                                            *> unsub
                                            *> pPush.startState Nothing
                                      ]
                                  )
                                  []
                              ]
                          , let
                              clickF f = click $
                                startState <#>
                                  ( case _ of
                                      Nothing -> f unit
                                      Just unsub -> f unit
                                        *> unsub
                                        *> pPush.startState Nothing
                                  )
                            in
                              D.div_
                                [ D.button
                                    (oneOf [ arrowClass, clickF $ pPush.toggleLeft ])
                                    [ text_ "<" ]
                                , D.button (oneOf [ arrowClass, clickF $ pPush.toggleRight ])
                                    [ text_ ">" ]
                                ]
                          , D.div_ [ content ]
                          ]
        ]
  )
