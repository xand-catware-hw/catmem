
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}


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

import              Control.Applicative
import              Control.Monad
import              Data.Eq
import              Data.Function
import              Data.Functor
import qualified    Data.Kind as Kind
import              Data.Maybe
import              Data.Tuple
import              GHC.Enum
import              GHC.Int
import              GHC.TypeLits

import              Clash.Prelude.RAM
import              Clash.Promoted.Nat
import              Clash.Signal
import              Clash.Sized.Vector
import              Clash.XException



-- | Type-checked, categorically semantic memory types.
--
-- Non-contradiction should be enforced by the type system. But
-- typechecking can only make guarantees about types that are
-- themselves restricted to correct and consistent values.
--
-- Consider the category of memory types: every memory type is either
-- primitive, or a product of precursor types. The same is true when
-- it comes to updating those memories.
--
-- The problem with the category of memories when it comes to
-- typechecking is that products are "too permissive". While
-- we can enforce the correctness of individual primitives, there is
-- nothing to restrict how they act when put together.
--
-- For a concrete example, take queues and stacks. Both are similar
-- in their construction, being made of a RAM block and a counter.
-- If we naively leave it at that, then there's no guarantee that a
-- stack will indeed behave like a stack and not a queue.
--
-- To properly make guarantees about the correctness of memory updates,
-- their type must be restricted to only allow the correct kinds of
-- actions.
--
-- Let V be a category of memory types. Define B to be a memory
-- /behaviour/ for some memory M in V if there is a heteromorphism
-- @h : B -> V (M, M)@ that sends B to automorphisms on M.
--
-- Each B is a collection of behaviours valid for a specific domain.
-- Thus typechecking guarantees the validity of memory behaviours
-- as long as the heteromorphism is correct.
--
class CatMem mem behaviour where

    -- | Automorphisms on unspecialized memory.
    --
    -- In cases where the new value of a memory depends on its old
    -- value, we can use a lambda taking @ViewOf mem@, and wire it
    -- up in @catmem'@.
    --
    -- Otherwise, a simpler type will suffice.
    --
    data MemMorph mem behaviour :: Kind.Type
    
    -- | Send a behaviour to a concrete automorphism on our memory type.
    --
    memMorph :: behaviour -> MemMorph mem behaviour

    type ViewOf mem :: Kind.Type
    type instance ViewOf mem = View mem
    
    -- | Apply a stream of automorphisms to the starting value to get
    -- a stream of viewable values.
    --
    catmem'
        :: HiddenClockResetEnable dom
        => mem
        -> Signal dom (MemMorph mem behaviour)
        -> Signal dom (ViewOf mem)

-- | Compose a behaviour heteromorphism with @catmem'@ to get an
-- abstract memory component.
--
catmem
    :: CatMem mem behaviour
    => HiddenClockResetEnable dom
    => mem
    -> Signal dom behaviour
    -> Signal dom (ViewOf mem)
catmem reset = catmem' reset . fmap memMorph


data family View m   :: Kind.Type

-- | Avoid namespace pollution by using the 'Change' data family for
-- single-use behaviours.
--
data family Change m :: Kind.Type


-- | Simple register storing exactly one value.
--
newtype Reg a = Reg a

instance NFDataX a => CatMem (Reg a) (Maybe a) where   
    newtype MemMorph (Reg a) _ =
        MkRegMorph { runRegMorph :: Maybe a }
    -- ^ Very simple morphisms that forget the previous value, and replace
    -- it with a new one.
    
    memMorph = MkRegMorph

    type ViewOf (Reg a) = a
    
    catmem' (Reg reset) = regMaybe reset . fmap runRegMorph
    

type RandomAccess (n :: Nat) a = (Int, RandomWrite n a)

data RandomWrite (n :: Nat) a
    = RamWrite Int a
    | RamNothing

-- | Asynchronous RAM blocks whose values aren't defined until written.
--
data AsyncRam (n :: Nat) a = AsyncRam

instance (KnownNat n, NFDataX a)
    => CatMem (AsyncRam n a) (Int, RandomWrite n a)
  where    
    data MemMorph (AsyncRam n a) _ = MkAsyncRamMorph
        { read  :: Int
        , write :: Maybe (Int, a) }
    -- ^ RAM types have more complex morphisms that must capture both
    -- read and write behaviours.
    -- Fortunately, very easy with a product type.
    
    memMorph (readIx, w) = MkAsyncRamMorph readIx $ case w of
        RamNothing         -> Nothing
        RamWrite writeIx d -> Just (writeIx, d)

    type ViewOf (AsyncRam n a) = a
       
    catmem' (AsyncRam :: AsyncRam n a) x =
        asyncRam (SNat :: SNat n) (read <$> x) (write <$> x)

    
newtype Counter a = Counter a

data instance Change (Counter a)
    = CountUp
    | CountDown
    | DontCount
    
instance (Enum a, NFDataX a)
    => CatMem (Counter a) (Change (Counter a))
  where    
    newtype MemMorph (Counter a) _ =
        MkCounterMorph { runCounterMorph :: a -> Maybe a }
    -- ^ Counters showcase types whose abstract behaviour has a finite
    -- number of correct values, but whose internal value may be infinite,
    -- and depends on the prior value.
    
    memMorph = MkCounterMorph . \case
        CountUp   -> Just . succ
        CountDown -> Just . pred
        DontCount -> const Nothing

    type ViewOf (Counter a) = a
    
    catmem' (Counter a) f = y where
        x = runCounterMorph <$> f <*> y
        y = regMaybe a x


