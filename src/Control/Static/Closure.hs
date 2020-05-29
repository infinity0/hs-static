{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}

module Control.Static.Closure where

-- external
import           Data.Constraint          (Dict (..))
import           Data.Functor             (($>))
import           Data.Kind                (Constraint)
import           Data.Singletons.Prelude
import           Data.Singletons.TH       (genDefunSymbols)

-- internal
import           Control.Static.Common
import           Control.Static.Serialise
import           Control.Static.Static


-- | Closure, internal representation.
--
-- The type parameter @env@ is meant for a bag of functions known statically at
-- compile time, that you don't need to serialise and so don't want the added
-- complexity of dealing with $(mkStatic). For example, if your function takes
-- in extra utility functions, but these are all statically-known. The type
-- parameter @cxt@ are the constraint types, which is effectively similar to
-- @env@ except that Haskell deals with them slightly differently.
type ClosureFunc cxt env arg res = CxtW cxt (env -> arg -> res)

-- | An applied closure, consisting of its static key and an argument.
type ClosureApply g = SKeyedExt g

-- | Create a 'ClosureApply' in its serialisable static form.
applyClosure
  :: RepVal g arg k
  => SKeyed k (CxtW cxt (env -> arg -> res))
  -> arg
  -> ClosureApply g
applyClosure (SKeyed k cl) arg = toSKeyedExt (SKeyed k arg)

envTabCons
  :: SKeyed k (CxtW cxt (env -> arg -> res))
  -> env
  -> TTab kk vv
  -> TTab (k ': kk) (env ': vv)
envTabCons cl env = skeyedCons (cl $> env)

envTabNil :: TTab '[] '[]
envTabNil = TCNil @NullC2Sym0

-- | A pre-closure is a function that takes two statically-known arguments:
-- a constraint, and an explicit argument; and gives a closure.
--
-- Typically, you define a bunch of top-level functions of the form @(ctx =>
-- env -> arg -> res)@, then create a table of pre-closures using the TH
-- function 'Control.Static.TH.mkStaticTab'.
class Closure (Part pcl) => PreClosure pcl where
  type Cxt pcl :: Constraint
  type Env pcl
  type Part pcl
  applyPre :: Cxt pcl => pcl -> Env pcl -> Part pcl

instance PreClosure (CxtW c (e -> v -> r)) where
  type Cxt (CxtW c (e -> v -> r)) = c
  type Env (CxtW c (e -> v -> r)) = e
  type Part (CxtW c (e -> v -> r)) = v -> r
  applyPre (CxtW pcl) = pcl

-- | A closure is a function that takes a runtime argument, and gives a result.
--
-- It is created by applying a constraint and environment to a pre-closure.
-- Typically you do this once on a table of pre-closures, using 'mkClosureTab'.
class Closure cl where
  type Arg cl
  type Res cl
  apply :: cl -> Arg cl -> Res cl

instance Closure (v -> r) where
  type Arg (v -> r) = v
  type Res (v -> r) = r
  apply = ($)

-- | A post-closure is a function that takes a runtime result, and converts all
-- the results of all different closures into the same type.
class PostClosure x f where
  type Pre f
  applyPost :: f -> Pre f -> x

instance PostClosure x (r -> x) where
  type Pre (r -> x) = r
  applyPost = ($)

genDefunSymbols [''Cxt, ''Env, ''Part, ''Arg, ''Res, ''Pre]


-- | A continuation from the result type to @x@.
type ResCont x = TyContSym1 x .@#@$$$ ResSym0


-- | Apply a table of pre-closures to its inputs, creating a table of closures.
applyClosureTabPre
  :: forall c1 kk vv
   . ConstrainList (Fmap CxtSym0 vv)
  => TCTab' PreClosure kk vv
  -> TCTab c1 kk (Fmap EnvSym0 vv)
  -> TCTab' Closure kk (Fmap PartSym0 vv)
applyClosureTabPre tab env =
  zipWith3TC @_ @_ @_ @_ @_ @(DictOf CxtSym0) @EnvSym0 @PartSym0 tab cxt env
    $ \_ cl _ Dict _ e -> (applyPre cl e, Dict)
  where cxt = toTCDict @_ @_ @CxtSym0 tab

-- | Apply a table of closures to its inputs, creating a table of results.
applyClosureTab
  :: forall c1 kk vv
   . TCTab' Closure kk vv
  -> TCTab c1 kk (Fmap ArgSym0 vv)
  -> TTab kk (Fmap ResSym0 vv)
applyClosureTab tab arg =
  zipWithTC @_ @_ @_ @_ @ArgSym0 @ResSym0 tab arg $ \_ cl _ a -> (apply cl a, Dict)

-- | Apply a table of results to its post-closures, creating a table of values.
applyClosureTabPost
  :: forall c0 kk rr x
   . TCTab c0 kk rr
  -> TCTab' (PostClosure x) kk (Fmap (TyContSym1 x) rr)
  -> TTab kk (Fmap (ConstSym1 x) rr)
applyClosureTabPost res post =
  zipWithTC @_ @_ @_ @_ @(TyContSym1 x) @(ConstSym1 x) res post
    $ \_ r _ p -> (applyPost p r, Dict)

-- | Apply a table of closures to a table of inputs and post-closures, giving a
-- table of values.
--
-- This method is just a demo, users will want one of the exported functions.
evalClosureTab
  :: forall (kk :: [Symbol]) vv x
   . TCTab' Closure kk vv
  -> TTab kk (Fmap ArgSym0 vv)
  -> TCTab' (PostClosure x) kk (Fmap (ResCont x) vv)
  -> TTab kk (Fmap (ConstSym1 x) vv)
evalClosureTab tab arg post =
  -- we could do this:
  --   let res = applyClosureTab tab arg
  --   in  applyClosureTabPost @_ @kk @(Fmap ResSym0 vv) res post
  -- but it does not work as-is; we first have to:
  -- write proofs (no-op functions) to convert
  --   TCTab c kk (Fmap (f .@#@$$$ g) vv)
  -- into
  --   TCTab c kk (Fmap f (Fmap g vv))
  -- in order to call applyClosureTabPost,
  -- as well as proofs to convert
  --   TCTab c kk (Fmap (ConstSym1 x) (Fmap f vv))
  -- into
  --   TCTab c kk (Fmap (ConstSym1 x) vv)
  -- in order to return the result.
  --
  -- OTOH zipWith3TC inlines these proofs for us already, so we use that
  zipWith3TC @_ @_ @_ @_ @_ @ArgSym0 @(ResCont x) @(ConstSym1 x) tab arg post
    $ \_ cl _ a _ p -> (applyPost p (apply cl a), Dict)


-- | Create a table of closures from a table of pre-closures.
--
-- We apply the relevant constraints and environment arguments,
-- statically-known at compile time.
mkClosureTab
  :: forall c1 kk vv
   . ConstrainList (Fmap CxtSym0 vv)
  => ConstrainList (ZipWith (ConstSym1 (TyCon1 PreClosure)) kk vv)
  => TTab kk vv
  -> TCTab c1 kk (Fmap EnvSym0 vv)
  -> TCTab' Closure kk (Fmap PartSym0 vv)
mkClosureTab = applyClosureTabPre . strengthenTC0

-- | @RepClosure c g k v@ is a constraint comprising:
--
--  *  @RepVal g (Arg v) k@
--  *  @c k (Res v)@
--  *  @Closure v@
--
-- modulo singletons defunctionalisation on @c@.
type RepClosure c g
  = RepExtSym3
      (AndC2 (ConstSym1 (TyCon1 Closure)) (FlipSym2 (.@#@$) ResSym0 .@#@$$$ c))
      g
      ArgSym0

-- | A 'RepClosure' whose result is exactly @r@.
type RepClosure' r g = RepClosure (ConstSym1 (TyCon1 ((~) r))) g

-- | Convert a 'Closure' table into a 'RepClosure' table, deducing constraints.
--
-- This is used to convert the result of 'mkClosureTab' into a form that can be
-- passed to the other functions e.g. 'evalSomeClosure'.
repClosureTab
  :: forall c g (kk :: [Symbol]) vv
   . ConstrainList (ZipWith (FlipSym2 (.@#@$) ResSym0 .@#@$$$ c) kk vv)
  => ConstrainList
       (ZipWith (FlipSym1 (TyCon2 (RepVal g) .@#@$$$ ApplySym1 ArgSym0)) kk vv)
  => TCTab' Closure kk vv
  -> TCTab (RepClosure c g) kk vv
repClosureTab = strengthenTC . strengthenTC

-- | Apply a closure table to a single input and a post-processing table,
-- giving a single result (if the input key was found).
--
-- This is the statically-typed version; for a version that runs for unknown
-- keys see 'withEvalSomeClosureCts'.
withEvalClosureCts
  :: forall c g (k :: Symbol) (kk :: [Symbol]) vv x
   . TCTab (RepClosure c g) kk vv
  -> SKeyed k g
  -> TCTab' (PostClosure x) kk (Fmap (ResCont x) vv)
  -> Either SKeyedError x
withEvalClosureCts tab val post = gwithStatic @_ @_ @(ResCont x) tab val post
  $ \_ cont cl -> applyPost cont . apply cl

-- | Apply a closure table to a single input and a post-processing table,
-- giving a single result (if the input key was found).
--
-- This is the dynamically-typed version; for a version that type-checks for
-- statically-known keys see 'withEvalClosureCts'.
withEvalSomeClosureCts
  :: forall c g (kk :: [Symbol]) vv x
   . TCTab (RepClosure c g) kk vv
  -> ClosureApply g
  -> TCTab' (PostClosure x) kk (Fmap (ResCont x) vv)
  -> Either SKeyedError x
withEvalSomeClosureCts tab ext post =
  withSKeyedExt ext $ \val -> withEvalClosureCts tab val post

-- | Apply a closure table to a single input, and pass the constrained result
-- to a continuation (if the input key was found).
--
-- This is the statically-typed version; for a version that runs for unknown
-- keys see 'withEvalSomeClosureCxt'.
withEvalClosureCxt
  :: forall c f g (k :: Symbol) (kk :: [Symbol]) vv r
   . TCTab (RepClosure c g) kk vv
  -> SKeyed k g
  -> (  forall k' v
      . 'Just '(k', v) ~ LookupKV k kk vv
     => ProofLookupKV f k kk vv
     => (c @@ k' @@ Res v) => Sing k' -> Res v -> r
     )
  -> Either SKeyedError r
withEvalClosureCxt tab val go =
  withStaticCxt @_ @f tab val $ \k' cl a -> go k' (apply cl a)

-- | Apply a closure table to a single input, and pass the constrained result
-- to a continuation (if the input key was found).
--
-- This is the dynamically-typed version; for a version that type-checks for
-- statically-known keys see 'withEvalClosureCxt'.
withEvalSomeClosureCxt
  :: forall c f g (kk :: [Symbol]) vv r
   . TCTab (RepClosure c g) kk vv
  -> ClosureApply g
  -> (  forall k k' v
      . 'Just '(k', v) ~ LookupKV k kk vv
     => ProofLookupKV f k kk vv
     -- keep above constraints; caller can either use or ignore as they wish
     -- without them, caller is prevented from using them at all
     => (c @@ k' @@ Res v) => Sing k' -> Res v -> r
     )
  -> Either SKeyedError r
withEvalSomeClosureCxt tab ext go = withSKeyedExt ext
  $ \(val :: SKeyed k g) -> withEvalClosureCxt @_ @f tab val (go @k)

-- | Evaluate a closure application with statically-known type, against a table
-- of closures, that all have the same result type.
evalClosure
  :: forall g (k :: Symbol) (kk :: [Symbol]) vv r
   . TCTab (RepClosure' r g) kk vv
  -> SKeyed k g
  -> Either SKeyedError r
evalClosure tab val = withEvalClosureCxt tab val $ const id

-- | Evaluate a closure application with statically-unknown type, against a
-- table of closures, that all have the same result type.
evalSomeClosure
  :: forall g (kk :: [Symbol]) vv r
   . TCTab (RepClosure' r g) kk vv
  -> ClosureApply g
  -> Either SKeyedError r
evalSomeClosure tab ext = withSKeyedExt ext $ evalClosure tab
