{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Static.Static where

-- external
import           Data.Constraint          (Dict (..))
import           Data.Kind                (Type)
import           Data.Singletons.Prelude
import           Data.Singletons.TH       (genDefunSymbols)

-- internal
import           Control.Static.Common
import           Control.Static.Serialise



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

-- | A continuation from an internal and external value, to a result type 'r'.
type family TyContIX r ext (v :: Type) where
  TyContIX r ext v = v -> ext @@ v -> r
genDefunSymbols [''TyContIX]
--type TyContIXSym2 r ext
--  = ApSym2 (TyCon2 (->)) ((FlipSym1 (TyCon2 (->)) @@ r) .@#@$$$ ApplySym1 ext)


-- | Generalised version of 'withStaticCts' that parameterises the way to apply
-- (C) to (I) and (X). (C) does not need to be a continuation, as long as the
-- @apply@ method understands how to use it.
gwithStatic
  :: forall c0 c1 f g ext (k :: Symbol) (kk :: [Symbol]) vv r
   . TCTab (RepExtSym3 c0 g ext) kk vv
  -> SKeyedInternal k g
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
gwithStatic tab val@(SKeyedInternal k ga) post go =
  toSKeyedEither k $ case lookupTC2 @_ @_ @_ @f k tab post of
    (TCNothing       , TCNothing      ) -> Nothing
    (TCJust Dict k' v, TCJust Dict _ p) -> Just $ go k' p v <$> fromRep k' ga
  -- note: yes, it's possible to implement this in terms of withStaticCxt
  -- IMO this version is a bit nicer

-- | Given a 'StaticExtern' with a key, do the following:
--
-- 1. Lookup the corresponding internal value (I)
-- 2. Decode the external value (X), if its type matches the one prescribed by
--    the internal value, via the type family @ext@.
-- 3. Lookup the corresponding continuation (C).
-- 4. Apply (C) to (I) and (X), returning a value of type @x@.
withStaticCts
  :: forall c0 c1 g ext (k :: Symbol) (kk :: [Symbol]) vv r
   . TCTab (RepExtSym3 c0 g ext) kk vv
  -> SKeyedInternal k g
  -> TCTab c1 kk (Fmap (TyContIXSym2 r ext) vv)
  -> Either SKeyedError r
withStaticCts tab val post =
  gwithStatic @_ @_ @(TyContIXSym2 r ext) tab val post (flip const)

withSomeStaticCts
  :: forall c0 c1 g ext (kk :: [Symbol]) vv r
   . TCTab (RepExtSym3 c0 g ext) kk vv
  -> SKeyedExternal g
  -> TCTab c1 kk (Fmap (TyContIXSym2 r ext) vv)
  -> Either SKeyedError r
withSomeStaticCts tab ext post = withSKeyedExternal ext
  $ \(val :: SKeyedInternal k g) -> withStaticCts tab val post

withStaticCxt
  :: forall c f g ext (k :: Symbol) (kk :: [Symbol]) vv r
   . TCTab (RepExtSym3 c g ext) kk vv
  -> SKeyedInternal k g
  -> (  forall k' v
      . 'Just '(k', v) ~ LookupKV k kk vv
     => ProofLookupKV f k kk vv
     => (c @@ k' @@ v) => Sing k' -> v -> (ext @@ v) -> r
     )
  -> Either SKeyedError r
withStaticCxt tab val@(SKeyedInternal k ga) go =
  toSKeyedEither k $ case lookupTC @_ @_ @f k tab of
    (TCNothing       , _   ) -> Nothing
    (TCJust Dict k' v, Dict) -> Just $ go k' v <$> fromRep k' ga

withSomeStaticCxt
  :: forall c f g ext (kk :: [Symbol]) vv r
   . TCTab (RepExtSym3 c g ext) kk vv
  -> SKeyedExternal g
  -> (  forall k k' v
      . 'Just '(k', v) ~ LookupKV k kk vv
     => ProofLookupKV f k kk vv
     -- keep above constraints; caller can either use or ignore as they wish
     -- without them, caller is prevented from using them at all
     => (c @@ k' @@ v) => Sing k' -> v -> (ext @@ v) -> r
     )
  -> Either SKeyedError r
withSomeStaticCxt tab ext go = withSKeyedExternal ext
  $ \(val :: SKeyedInternal k g) -> withStaticCxt @_ @f tab val (go @k)
