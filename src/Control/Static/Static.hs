{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE DeriveFunctor            #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}

module Control.Static.Static where

-- external
import           Data.Constraint          (Dict (..))
import           Data.Kind                (Type)
import           Data.Singletons.Prelude
import           Data.Singletons.TH       (genDefunSymbols)
import           Data.Text                (pack, unpack)

-- internal
import           Control.Static.Common
import           Control.Static.Serialise


-- | Standalone static key with no associated value.
--
-- Users typically don't need this, and should use 'SKeyed' or 'SKeyedExt'
-- as appropriate.
type SKey (k :: Symbol) = Sing k

-- | Internal value, typed-indexed by an associated static-key.
--
-- Generally, @v@ is not expected to be serialisable or otherwise representable
-- outside of the program. For cases where it is, you should define an instance
-- of 'RepVal'. That then enables you to use 'toSKeyedExt' and
-- other utility functions with this constraint.
data SKeyed k v = SKeyed !(SKey k) !v
  deriving Functor

-- | Similar to 'withSomeSing' for a 'SKeyedExt', extract the type from
-- the 'String' key and run a typed function on the typed value.
withSKeyedExt :: SKeyedExt g -> (forall (a :: Symbol) . SKeyed a g -> r) -> r
withSKeyedExt (SKeyedExt s a) f = withSomeSing (pack s) $ \k -> f (SKeyed k a)

-- | Convert an internal value to an external value, depending on the existence
-- of an instance of 'RepVal' to help perform the conversion.
toSKeyedExt :: RepVal g v k => SKeyed k v -> SKeyedExt g
toSKeyedExt (SKeyed k v) = SKeyedExt (unpack (fromSing k)) (toRep k v)

toSKeyedEither
  :: Sing (k :: Symbol) -> Maybe (Either String v) -> Either SKeyedError v
toSKeyedEither k Nothing          = Left $ SKeyedNotFound $ unpack $ fromSing k
toSKeyedEither _ (Just (Left  e)) = Left $ SKeyedExtDecodeFailure e
toSKeyedEither _ (Just (Right v)) = Right v

-- | Helper function for building 'TCTab's.
skeyedCons
  :: (c @@ k @@ v) => SKeyed k v -> TCTab c kk vv -> TCTab c (k ': kk) (v ': vv)
skeyedCons (SKeyed k v) = TCCons k v

-- | @RepExt c g ext k v@ is a constraint comprising:
--
--  *  @RepVal g (ext v) k@
--  *  @c k v@
--
-- modulo singletons defunctionalisation on @c@ and @ext@.
type RepExtSym3 c g ext
  = AndC2 c (FlipSym1 (TyCon2 (RepVal g) .@#@$$$ ApplySym1 ext))
{- Implementation note: this is equivalent to:

type family RepExt c g ext k v :: Constraint where
  RepExt c g ext k v = (c @@ k @@ v, RepVal g (ext @@ v) k)
genDefunSymbols [''RepExt]

However it must be of the form @AndC2 x y@ so that we can define 'repClosureTab'
in terms of 'strengthenTC', which uses 'AndC2'.
-}

-- | A continuation from an internal and external value, to a result type @r@.
type family TyContIX r ext (v :: Type) where
  TyContIX r ext v = v -> ext @@ v -> r
genDefunSymbols [''TyContIX]
--type TyContIXSym2 r ext
--  = ApSym2 (TyCon2 (->)) ((FlipSym1 (TyCon2 (->)) @@ r) .@#@$$$ ApplySym1 ext)

-- | Given an 'SKeyed' of an external value @g@, do the following:
--
-- 1. Lookup the corresponding internal value (I) of type @v@.
-- 2. Decode the external value (X) of type @g@, if its type can be decoded
--    into the type @ext v@.
-- 3. Lookup the corresponding continuation (C).
-- 4. Apply (C) to (I) and (X), returning a value of type @r@.
gwithStatic
  :: forall c0 c1 f g ext (k :: Symbol) (kk :: [Symbol]) vv r
   . TCTab (RepExtSym3 c0 g ext) kk vv
  -> SKeyed k g
  -> TCTab c1 kk (Fmap f vv)
  -> (  forall k' v
      . 'Just '(k', v) ~ LookupKV k kk vv
     => 'Just '(k', f @@ v) ~ Fmap (FmapSym1 f) (LookupKV k kk vv)
     => (c0 @@ k' @@ v)
     => (c1 @@ k' @@ (f @@ v))
     => Sing k'
     -> (f @@ v)
     -> v
     -> (ext @@ v)
     -> r
     )
  -> Either SKeyedError r
gwithStatic tab val@(SKeyed k ga) post go =
  toSKeyedEither k $ case lookupTC2 @_ @_ @_ @f k tab post of
    (TCNothing       , TCNothing      ) -> Nothing
    (TCJust Dict k' v, TCJust Dict _ p) -> Just $ go k' p v <$> fromRep k' ga
  -- note: yes, it's possible to implement this in terms of withStaticCxt
  -- IMO this version is a bit nicer

withStaticCts
  :: forall c0 c1 g ext (k :: Symbol) (kk :: [Symbol]) vv r
   . TCTab (RepExtSym3 c0 g ext) kk vv
  -> SKeyed k g
  -> TCTab c1 kk (Fmap (TyContIXSym2 r ext) vv)
  -> Either SKeyedError r
withStaticCts tab val post =
  gwithStatic @_ @_ @(TyContIXSym2 r ext) tab val post (const id)

withSomeStaticCts
  :: forall c0 c1 g ext (kk :: [Symbol]) vv r
   . TCTab (RepExtSym3 c0 g ext) kk vv
  -> SKeyedExt g
  -> TCTab c1 kk (Fmap (TyContIXSym2 r ext) vv)
  -> Either SKeyedError r
withSomeStaticCts tab ext post =
  withSKeyedExt ext $ \(val :: SKeyed k g) -> withStaticCts tab val post

withStaticCxt
  :: forall c f g ext (k :: Symbol) (kk :: [Symbol]) vv r
   . TCTab (RepExtSym3 c g ext) kk vv
  -> SKeyed k g
  -> (  forall k' v
      . 'Just '(k', v) ~ LookupKV k kk vv
     => ProofLookupKV f k kk vv
     => (c @@ k' @@ v) => Sing k' -> v -> (ext @@ v) -> r
     )
  -> Either SKeyedError r
withStaticCxt tab val@(SKeyed k ga) go =
  toSKeyedEither k $ case lookupTC @_ @_ @f k tab of
    (TCNothing       , _   ) -> Nothing
    (TCJust Dict k' v, Dict) -> Just $ go k' v <$> fromRep k' ga

withSomeStaticCxt
  :: forall c f g ext (kk :: [Symbol]) vv r
   . TCTab (RepExtSym3 c g ext) kk vv
  -> SKeyedExt g
  -> (  forall k k' v
      . 'Just '(k', v) ~ LookupKV k kk vv
     => ProofLookupKV f k kk vv
     -- keep above constraints; caller can either use or ignore as they wish
     -- without them, caller is prevented from using them at all
     => (c @@ k' @@ v) => Sing k' -> v -> (ext @@ v) -> r
     )
  -> Either SKeyedError r
withSomeStaticCxt tab ext go =
  withSKeyedExt ext $ \(val :: SKeyed k g) -> withStaticCxt @_ @f tab val (go @k)
