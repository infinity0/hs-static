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
{-# LANGUAGE UndecidableInstances     #-}

module Control.Static.Common where

-- external
import           Data.Constraint         (Class (..), Dict (..), (:-) (..))
import           Data.Kind               (Constraint, Type)
import           Data.Singletons.Prelude
import           Data.Singletons.TH      (genDefunSymbols, singletons)


-- | Type family representing the type of a continuation.
type family TyCont r (a :: Type) where
  TyCont r a = a -> r
genDefunSymbols [''TyCont]

-- | Type family representing the type of a continuation of 2 args.
type family TyCont2 r (a1 :: Type) (a2 :: Type) where
  TyCont2 r a1 a2 = a1 -> a2 -> r
genDefunSymbols [''TyCont2]

-- | Type family representing the type of a continuation of 3 args.
type family TyCont3 r (a1 :: Type) (a2 :: Type) (a3 :: Type) where
  TyCont3 r a1 a2 a3 = a1 -> a2 -> a3 -> r
genDefunSymbols [''TyCont3]

singletons [d|
  -- -| S combinator, not yet in singletons
  -- https://github.com/goldfirere/singletons/issues/455
  ap :: (x -> y -> z) -> (x -> y) -> (x -> z)
  ap f g x = f x (g x)
  |]


-- | Data type wrapping a constraint, to avoid ImpredicativeTypes GHC error.
newtype CxtW c a = CxtW { unCxtW :: c => a }

-- | Convert a list of constraints into a single constraint
type family ConstrainList (cc :: [Constraint]) :: Constraint where
  ConstrainList '[] = ()
  ConstrainList (c ': cc) = (c, ConstrainList cc)

-- | Null constraint over 1 type param.
type family NullC (t :: k) :: Constraint where
  NullC t = ()
genDefunSymbols [''NullC]

-- | Null constraint over 2 type params.
type family NullC2 (t :: k) (t' :: k') :: Constraint where
  NullC2 t t' = ()
genDefunSymbols [''NullC2]

-- | Combine two constraints
type family AndC c0 c1 :: Constraint where
  AndC c0 c1 = (c0, c1)
genDefunSymbols [''AndC]

-- | Combine two constraint constructors into a single constraint constructor.
--
-- This is analogous to the term-level idiom @ap ((,) . c0) c1@ that combines
-- two functions c0, c1 into a single one.
type AndC1 c0 c1 = ApSym2 (AndCSym0 .@#@$$$ c0) c1

-- | Combine two constraint constructors, each taking 2 type params, into
-- a single constraint constructor taking 2 type params.
--
-- This is analogous to the term-level idiom @ap (ap . ((,) .) . c0) c1@ that
-- combines two functions c0, c1 that each take 2 params, into a single one.
type AndC2 c0 c1 = ApSym2 (ApSym0 .@#@$$$ (.@#@$$) AndCSym0 .@#@$$$ c0) c1

-- | Entailment over 2 type params.
type family Class2 c0 c1 t t' where
  Class2 c0 c1 t t' = Class (c0 @@ t @@ t') (c1 @@ t @@ t')
genDefunSymbols [''Class2]


singletons [d|
  -- note: subexpressions are lifted out to the top-level due to
  -- https://github.com/goldfirere/singletons/issues/339#issuecomment-612530482

  lookupKV :: Eq k => k -> [k] -> [v] -> Maybe (k, v)
  lookupKV k [] []           = Nothing
  lookupKV k (k':kk) (v':vv) = lookupKV_If k k' kk v' vv (k == k')

  lookupKV_If :: Eq k => k -> k -> [k] -> v -> [v] -> Bool -> Maybe (k, v)
  lookupKV_If k k' _ v' _  True = Just (k', v')
  lookupKV_If k _ kk _ vv False = lookupKV k kk vv
  |]

{-
Proof that fmap f (lookupKV k kk vv) == lookupKV k kk (fmap f vv)

The proof roughly follows the below structure, modulo the fact that we split
out lookupKV into 2 functions due to a singletons / template-haskell issue,
discussed in the link above.

Inducting on kk vv:

Given:
Wf. (Fmap f (LookupKV k  kk  vv) ~ LookupKV k kk (Fmap f vv))
Sf. Just (f @@ v') ~ Fmap f (Just v')
Tf. f @@ v' ': Fmap f vv ~ Fmap f (v' ': vv)

Deduce:
(Fmap f (LookupKV k (k' ': kk) (v' ': vv)) ~ LookupKV k (k' ': kk) (Fmap f (v' ': vv)))
                                                          by (Tf), ~
                                             LookupKV k (k' ': kk) (f @@ v' ': Fmap f vv)

if k == k'                                   if k == k'
 then -> Fmap f (Just v')          by (Sf) ~  then -> Just (f @@ v')
 else -> Fmap f (LookupKV k kk vv) by (Wf) ~  else -> Lookup k kk (Fmap f vv)

[].

Note that GHC deduces Sf and Tf automatically, so they don't need to appear
explicitly in the code proof below.
-}

class (Fmap (FmapSym1 f) (LookupKV k kk vv) ~
       LookupKV k kk (Fmap f vv))
  => ProofLookupKV f k (kk :: [kt]) vv where
instance -- base case
     ProofLookupKV f k        '[]        '[]
instance -- implicit (f @@ v' ': Fmap f vv ~ Fmap f (v' ': vv)) =>
    (ProofLookupKV_If f k k' kk v' vv (k == k'))
  => ProofLookupKV f (k :: kt) (k' ': kk) (v' ': vv)

class (Fmap (FmapSym1 f) (LookupKV_If k k' kk v' vv eq) ~
       LookupKV_If k k' kk (f @@ v') (Fmap f vv) eq)
  => ProofLookupKV_If f (k :: kt) k' kk v' vv eq where
instance -- implicit (Just (f @@ v') ~ Fmap f (Just v')) =>
     ProofLookupKV_If f k k' kk v' vv 'True  -- Just v
instance
     ProofLookupKV f k kk vv
  => ProofLookupKV_If f k k' kk v' vv 'False -- lookupKV kk vv


-- | Maybe that carries its type.
data TMaybe :: forall k. Maybe k -> Type where
  TNothing :: TMaybe 'Nothing
  TJust :: !t -> TMaybe ('Just t)

-- | Heterogeneous constrained table.
data TCTab (c :: kt ~> Type ~> Constraint) (kk :: [kt]) (vv :: [Type]) :: Type where
  TCNil :: TCTab c '[] '[]
  TCCons :: (c @@ k @@ v) => !(Sing (k :: kt)) -> !v -> !(TCTab c kk vv) -> TCTab c (k : kk) (v : vv)

-- | A 'TCTab' with a constraint that applies only to the value, not the key.
type TCTab' c = TCTab (ConstSym1 (TyCon1 c))

-- | Heterogeneous unconstrained table.
--
-- To add or remove constraints, see 'strengthenTC0', 'strengthenTC' and
-- 'weakenTC'.
type TTab = TCTab NullC2Sym0

-- | Result type of 'lookupTC'.
data TCMaybe c (t :: Maybe (kt, Type)) where
  TCNothing :: TCMaybe c 'Nothing
  TCJust :: Dict (c @@ k @@ v) -> !(Sing k) -> !v -> TCMaybe c ('Just '(k, v))

-- | Lookup an element in the table, and generate some proofs about the result
-- that can be used by the caller.
lookupTC
  :: forall kt c f (k :: kt) (kk :: [kt]) vv
   . SEq kt
  => Sing k
  -> TCTab c kk vv
  -> (TCMaybe c (LookupKV k kk vv), Dict (ProofLookupKV f k kk vv))
lookupTC k TCNil             = (TCNothing, Dict)
lookupTC k (TCCons k' v tab) = case k %== k' of
  STrue  -> (TCJust Dict k' v, Dict)
  SFalse -> case lookupTC @kt @c @f k tab of
    (res, Dict) -> (res, Dict) -- generate new proof from old proof

-- | Lookup two elements in two related tables.
--
-- The types of the outputs are provably related.
lookupTC2
  :: forall kt c0 c1 f (k :: kt) (kk :: [kt]) vv
   . SEq kt
  => Sing k
  -> TCTab c0 kk vv
  -> TCTab c1 kk (Fmap f vv)
  -> ( TCMaybe c0 (LookupKV k kk vv)
     , TCMaybe c1 (Fmap (FmapSym1 f) (LookupKV k kk vv))
     )
lookupTC2 k TCNil             TCNil               = (TCNothing, TCNothing)
lookupTC2 k (TCCons k' v tab) (TCCons k'' p post) = case k %== k' of
  STrue  -> (TCJust Dict k' v, TCJust Dict k'' p)
  SFalse -> lookupTC2 @kt @c0 @c1 @f k tab post

-- | Zip two related tables, giving a third table related to both.
--
-- The types of the outputs are provably related.
zipWithTC
  :: forall kt c0 c1 cr f1 r (kk :: [kt]) vv
   . TCTab c0 kk vv
  -> TCTab c1 kk (Fmap f1 vv)
  -> (  forall k0 k1 v
      . (c0 @@ k0 @@ v)
     => (c1 @@ k1 @@ (f1 @@ v))
     => Sing k0
     -> v
     -> Sing k1
     -> (f1 @@ v)
     -> (r @@ v, Dict (cr @@ k0 @@ (r @@ v)))
     )
  -> TCTab cr kk (Fmap r vv)
zipWithTC TCNil            TCNil              f = TCNil
zipWithTC (TCCons k0 v t0) (TCCons k1 f1v t1) f = case f k0 v k1 f1v of
  (v', Dict) -> TCCons k0 v' (zipWithTC @kt @c0 @c1 @cr @f1 @r t0 t1 f)

-- | Zip three related tables, giving a fourth table related to both.
--
-- The types of the outputs are provably related.
zipWith3TC
  -- brittany-disable-next-binding
  -- https://github.com/lspitzner/brittany/issues/299
  :: forall kt c0 c1 c2 cr f1 f2 r (kk :: [kt]) vv
   . TCTab c0 kk vv
  -> TCTab c1 kk (Fmap f1 vv)
  -> TCTab c2 kk (Fmap f2 vv)
  -> (  forall k0 k1 k2 v
      . (c0 @@ k0 @@ v)
     => (c1 @@ k1 @@ (f1 @@ v))
     => (c2 @@ k2 @@ (f2 @@ v))
     => Sing k0 -> v
     -> Sing k1 -> f1 @@ v
     -> Sing k2 -> f2 @@ v
     -> (r @@ v, Dict (cr @@ k0 @@ (r @@ v)))
     )
  -> TCTab cr kk (Fmap r vv)
zipWith3TC TCNil            TCNil              TCNil              f = TCNil
zipWith3TC (TCCons k0 v t0) (TCCons k1 f1v t1) (TCCons k2 f2v t2) f =
  case f k0 v k1 f1v k2 f2v of
    (v', Dict) ->
      TCCons k0 v' (zipWith3TC @kt @c0 @c1 @c2 @cr @f1 @f2 @r t0 t1 t2 f)

type DictOf c = TyCon1 Dict .@#@$$$ c

withTCDict
  :: forall kt c0 c (kk :: [kt]) vv r
   . TCTab c0 kk vv
  -> TTab kk (Fmap (DictOf c) vv)
  -> (ConstrainList (Fmap c vv) => r)
  -> r
withTCDict TCNil           TCNil              f = f
withTCDict (TCCons _ _ tv) (TCCons _ Dict tc) f = withTCDict @_ @_ @c tv tc f

toTCDict
  :: forall kt c0 c (kk :: [kt]) vv
   . ConstrainList (Fmap c vv)
  => TCTab c0 kk vv
  -> TTab kk (Fmap (DictOf c) vv)
toTCDict TCNil           = TCNil
toTCDict (TCCons k _ xs) = TCCons k Dict (toTCDict @_ @_ @c xs)

-- | Weaken the constraint on a 'TCTab'.
weakenTC
  :: forall kt c0 c1 (kk :: [kt]) vv
   . ConstrainList (ZipWith (Class2Sym2 c1 c0) kk vv)
  => TCTab c0 kk vv
  -> TCTab c1 kk vv
weakenTC TCNil = TCNil
weakenTC (TCCons (k :: Sing k) (v :: v) tab) =
  case cls @(c1 @@ k @@ v) @(c0 @@ k @@ v) of
    Sub Dict -> TCCons k v (weakenTC tab)

-- | Strengthen the constraint on a 'TCTab'.
strengthenTC
  :: forall kt c0 c1 (kk :: [kt]) vv
   . ConstrainList (ZipWith c1 kk vv)
  => TCTab c0 kk vv
  -> TCTab (AndC2 c0 c1) kk vv
strengthenTC TCNil           = TCNil
strengthenTC (TCCons k v xs) = TCCons k v (strengthenTC @_ @_ @c1 xs)

-- | Strengthen the constraint on a 'TTab'.
strengthenTC0
  :: forall kt c1 (kk :: [kt]) vv
   . ConstrainList (ZipWith c1 kk vv)
  => TTab kk vv
  -> TCTab c1 kk vv
strengthenTC0 TCNil           = TCNil
strengthenTC0 (TCCons k v xs) = TCCons k v (strengthenTC0 @_ @c1 xs)
