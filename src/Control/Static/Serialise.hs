{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}

module Control.Static.Serialise where

-- external
import qualified Codec.Serialise      as SR
import qualified Data.Binary          as BN
import qualified Data.ByteString.Lazy as LBS

import           Codec.Serialise      (Serialise)
import           Data.Binary          (Binary)
import           Data.Dynamic         (Dynamic, fromDynamic, toDyn)
import           Data.Kind            (Type)
import           Data.Singletons      (Sing)
import           Data.Singletons.TH   (genDefunSymbols)
import           GHC.Generics         (Generic)
import           Type.Reflection      ((:~~:) (..), TypeRep, Typeable,
                                       eqTypeRep, typeRep)


-- | Serialisable external value, with an associated static-key.
--
-- @g@ is a type that can generically represent all the external interface of
-- your static values. See 'RepVal' and 'DoubleEncoding' for more details.
data SKeyedExt g = SKeyedExt !String !g
  deriving (Read, Show, Generic, Binary, Serialise, Eq, Ord, Functor)

-- | Possible errors when resolving a key in a static table.
data SKeyedError =
   SKeyedNotFound String
 | SKeyedExtDecodeFailure String
 deriving (Read, Show, Generic, Binary, Serialise, Eq, Ord)

-- | A value and its external representation, indexed by some key.
class RepVal g (v :: Type) (k :: kt) where
  -- | Convert an external value into its generic representation.
  toRep :: Sing k -> v -> g
  -- | Convert a generic representation into its external value.
  --
  -- This may fail, since @g@ may have to represent several other @v'@ as well,
  -- which @k@ should help determine.
  fromRep :: Sing k -> g -> Either String v
genDefunSymbols [''RepVal]

castOrFail :: forall s t . (Typeable s, Typeable t) => s -> Either String t
castOrFail s = case reps `eqTypeRep` rept of
  Just HRefl -> Right s
  Nothing ->
    Left
      $  "fromTypeable: type-mismatch, expecting: "
      <> show rept
      <> "; actual: "
      <> show reps
 where
  rept = typeRep :: TypeRep t
  reps = typeRep :: TypeRep s

-- | 'RepVal' instance for 'Dynamic'.
--
-- Note that by nature this is not serialisable, and is only really meant for
-- testing purposes. Neither can it support a generic 'Eq' or 'Ord' instance;
-- if you need that then try 'DSerialise' or 'DBinary'.
instance Typeable v => RepVal Dynamic v k where
  toRep _ = toDyn
  fromRep _ s = case fromDynamic s of
    Nothing -> Left "fromDynamic failed; type-mismatch"
    -- annoyingly, Dynamic doesn't expose the type for us to print it, nor the
    -- value for us to pass it to castOrFail. If you replace this subexpression
    -- with castOrFail this will type-check as it will try to cast the Dynamic
    -- itself, and always fail at runtime.
    Just v  -> Right v

-- | Uniform generic wrapper.
--
-- In a type-safe language like Haskell, one needs to know in advance the type
-- of something in order to deserialise it successfully. In many applications
-- however, the point at which data enters the program is separate from the
-- point at which we have enough type information to fully deserialise a
-- statically-keyed value. Between these points, we often want to deserialise
-- the /other/ parts of that data, and perform logic based on its value.
--
-- This wrapper works around that fact by double-encoding the static-value.
-- This is perhaps suboptimal performance-wise, but is simple to implement and
-- use, especially in a compositional manner. When data first enters the
-- program, one can deserialise the whole data using the mechanism represented
-- by @s@, which will then contain @'HalfEncoded' b@ instances of this type
-- inside it. When you finally have enough type information to perform the rest
-- of the deserialise you can call 'fromRep' on these parts, to recovered the
-- typed value corresponding to each part.
--
-- This wrapper also short-circuits the case of calling 'toRep' then 'fromRep'
-- without attempting to serialise the value in between. In this case the
-- original value is simply wrapped in the 'Decoded' constructor, no attempt to
-- serialise based on @s@ is actually made, and no value based on @b@ is ever
-- constructed.
--
-- If you need optimal performance and really must avoid double-serialising,
-- you can instead define your own ADT as a sum-type over all your possible
-- serialisation types, make this serialisable, and implement 'RepVal' for it.
--
-- @s@ is a constraint over serialisable types, e.g 'Serialise' or 'Binary'.
-- @b@ is the concrete serialisation type, e.g. 'LBS.ByteString'.
data DoubleEncoding s b where
  Decoded :: (Typeable t, s t) => !t -> DoubleEncoding s b
  HalfEncoded :: !b -> DoubleEncoding s b

type DSerialise = DoubleEncoding Serialise LBS.ByteString

instance Serialise DSerialise where
  encode (Decoded t) = SR.encode
    (HalfEncoded (SR.serialise t) :: DoubleEncoding Serialise LBS.ByteString)
  encode (HalfEncoded t) = SR.encode t
  decode = HalfEncoded <$> SR.decode

instance (Typeable v, Serialise v) => RepVal DSerialise v k where
  toRep _ = Decoded
  fromRep _ (Decoded     v) = castOrFail v
  fromRep _ (HalfEncoded s) = case SR.deserialiseOrFail s of
    Left  e -> Left (show e)
    Right v -> Right v

instance Eq DSerialise where
  a == b = SR.serialise a == SR.serialise b

instance Ord DSerialise where
  compare a b = compare (SR.serialise a) (SR.serialise b)

type DBinary = DoubleEncoding Binary LBS.ByteString

decodeFullyOrFail :: Binary a => LBS.ByteString -> Either String a
decodeFullyOrFail s = case BN.decodeOrFail s of
  Left  e          -> Left ("Data.Binary decode failure: " <> show e)
  Right (bs, o, v) -> if LBS.null bs
    then Right v
    else Left ("Data.Binary decode leftovers: " <> show (bs, o))

instance Binary DBinary where
  put (Decoded t) =
    BN.put (HalfEncoded (BN.encode t) :: DoubleEncoding Binary LBS.ByteString)
  put (HalfEncoded t) = BN.put t
  get = HalfEncoded <$> BN.get

instance (Typeable v, Binary v) => RepVal DBinary v k where
  toRep _ = Decoded
  fromRep _ (Decoded     v) = castOrFail v
  fromRep _ (HalfEncoded s) = decodeFullyOrFail s

instance Eq DBinary where
  a == b = BN.encode a == BN.encode b

instance Ord DBinary where
  compare a b = compare (BN.encode a) (BN.encode b)
