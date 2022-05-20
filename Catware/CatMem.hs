
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}

module Catware.CatMem where
--
--                   (X)
--                o
--              .
--         ^  ^       /
-- X <--- (*w*)______/
--            /      \
--
-- The cat sees and it remembers.

import Control.Applicative
import Data.Function
import Data.Functor
import Data.Int
import Data.Maybe
import Data.Tuple
import GHC.Enum
import GHC.TypeLits

import Clash.Prelude.RAM
import Clash.Promoted.Nat
import Clash.Signal
import Clash.XException



-- | Memory with categorical semantics.
--
-- The semantics of memory are often different from the literal
-- values stored in the circuit. Consider a counter: the counter
-- may count up by one, count down by one, or do nothing. It stores
-- the current count as its value. It would violate the semantics
-- of the counter for it to increase its count by two, or decrease
-- it by two. 
--
-- The behaviour of memory on updates must be constrained in some
-- way for the typechecker to guarantee semantic correctness of
-- changes. Let C be the type of all possible changes to the
-- memory value, and let B be the type of all semantically correct
-- behaviours. We constrain changes by providing a map
-- @h : B -> C@ which sends behaviours to their prescribed
-- changes.
--
-- Returning to the counter example, the semantic behaviours are
-- B := CountUp, CountDown, Stop. We can define the map
--  >>> toChange :: B -> (p -> Maybe p)
--  >>> toChange CountUp   = Just . succ
--  >>> toChange CountDown = Just . pred
--  >>> toChange Stop      = const Nothing
-- Therefore, we have a direct conversion between semantic meaning
-- and literal value-updates. With the constraint in place,
-- there's no worry that our circuit might be connected improperly.
--
data CatMem mem view behaviour change
    = CatMem
        { toChange :: behaviour -> change
        -- ^ Convert an abstract behaviour into a concrete change on
        -- the memory value.
        , memorize :: forall dom. HiddenClockResetEnable dom
                   => mem
                   -> Signal dom change
                   -> Signal dom view
        -- ^ Take a stream of changes to produce a stream of output
        -- values.
        }

-- | Run a memory on its semantic behaviours.
--
-- An interesting note is that memories with semantics are
-- propositional types. They say "if you have a memory function,
-- and a way to constrain it to some semantics, then you have
-- a semantic memory." This function says in turn "if you have
-- a proof that something is a semantic memory, then I can provide
-- an equivalent abstract memory function."
--
-- The realization of semantic memories as propositional types
-- may have implications on the philosophical conception of
-- hardware devices. The notion might be extended usefully to
-- other areas of the system.
--
runMem
    :: HiddenClockResetEnable dom
    => CatMem m v b c
    -> m
    -> Signal dom b
    -> Signal dom v
runMem (CatMem c m) r = m r . fmap c


-- | Create a Mealy machine from a CatMem and transition
-- function.
--
catMealy
    :: HiddenClockResetEnable dom
    => CatMem m v b c
    -> m
    -> (i -> v -> (o, b))
    -> Signal dom i
    -> Signal dom o
catMealy m r f i = fst <$> y where
    y = f <$> i <*> x
    x = runMem m r $ snd <$> y

-- | Create a Mealy machine from a CatMem that takes a transition
-- function already fmapped into Signal.
--
-- Sometimes we want to Mealy a function that has several inputs, in
-- which case it can be very convenient to do:
--  >>> main cMem rst in1 in2 in3 = out where
--  >>>   trans = f <$> in1 <*> in2 <*> in3
--  >>>   out   = catMealyA cMem rst trans
--
catMealyA
    :: HiddenClockResetEnable dom
    => CatMem m v b c
    -> m
    -> Signal dom (v -> (o, b))
    -> Signal dom o
catMealyA m r f = fst <$> y where
    y = f <*> x
    x = runMem m r $ snd <$> y
    

-- | Common register with enable.
--
type Reg a = CatMem a a (Maybe a) (Maybe a)

-- | Registers are very straightforward: their semantics are the
-- same as their changes. They only need to be constrained by 'id'.
--
catReg :: NFDataX a => Reg a
catReg = CatMem id regMaybe


-- | Semantics of random access readable memories.
--
data RandomRead index a
    = Read index

-- | Semantics of random access writeable memories.
--
data RandomWrite index a
    = Write index a
    | DontWrite

-- | Semantics of random access read/write memories.
--
type RandomAccess index a =
    (RandomRead index a, RandomWrite index a)

type AsyncRam n index a =
    CatMem (SNat n) a (RandomAccess index a) (index, Maybe (index, a))

-- | The semantics of random-access memories are split into reading and
-- writing. We always read from RAM, and can optionally write new data
-- to it.
--
-- The literal changes are similar, though they use general rather than
-- dedicated types.
--
catAsyncRam
    :: (Enum index, NFDataX index, NFDataX a)
    => AsyncRam n index a
catAsyncRam = CatMem {..} where
    toChange (Read readIx, write) = 
        let write' = case write of
                Write writeIx a -> Just (writeIx, a)
                DontWrite       -> Nothing
        in (readIx, write')

    memorize sn c = asyncRam sn (fst <$> c) (snd <$> c)


-- | Semantics of counters.
--
data CountDirection
    = CountUp
    | CountDown
    | DontCount

type Counter a
    = CatMem a a CountDirection (a -> Maybe a)

-- | Complete form of the counter example above.
--
catCounter :: (Enum a, NFDataX a) => Counter a
catCounter = CatMem {..} where
    toChange CountUp   = Just . succ
    toChange CountDown = Just . pred
    toChange DontCount = const Nothing

    memorize reset c = y where
        x = c <*> y
        y = regMaybe reset x

