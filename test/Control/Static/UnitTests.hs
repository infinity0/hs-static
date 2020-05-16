{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf            #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}

module Control.Static.UnitTests where

-- external, testing
import           Test.Tasty
import           Test.Tasty.HUnit

-- external
import           Control.Monad.RWS.Strict   (RWST (..), evalRWST)
import           Control.Monad.State.Class  (MonadState (..))
import           Control.Monad.Writer.Class (MonadWriter (..))
import           Control.Static             (ClosureApply, DSerialise,
                                             NullC2Sym0, RepVal (..),
                                             TCTab (..), applyClosure,
                                             evalSomeClosure, mkClosureTab,
                                             repClosureTab)
import           Control.Static.TH          (mkDefStaticTab, mkStatics,
                                             mkStaticsWithRefs, staticKey,
                                             staticKeyType, staticRef)

-- These unit tests are written to showcase all the features & possibilities of
-- using this library. It is certainly not the simplest way of achieving what
-- it is actually doing. When using this library, bear this in mind and don't
-- just blindly copy the below - aim to simplify as much of it as possible.

data TEnv m g = TEnv {
    pushTask :: !(ClosureApply g -> m ())
  , pushLog  :: !(String -> m ())
}

writeLog :: MonadWriter [String] m => () -> String -> m [Int]
writeLog _ x = tell [x] >> pure []
mkStatics ['writeLog]
-- note: the above call to mkStatics is actually redundant; mkDefStaticTab
-- automatically will do this for any passed-in names that did not already have
-- statics created for them. We call it here for demonstration purposes.

collatzCycle0 :: [Integer]
collatzCycle0 = [0]
collatzCycle1 :: [Integer]
collatzCycle1 = [1, 4, 2]
collatzCycle2 :: [Integer]
collatzCycle2 = [-1, -2]
collatzCycle3 :: [Integer]
collatzCycle3 = [-5, -14, -7, -20, -10]
collatzCycle4 :: [Integer]
collatzCycle4 =
  [-17, -50, -25, -74, -37, -110, -55, -164, -82, -41]
    ++ [-122, -61, -182, -91, -272, -136, -68, -34]

mkStaticsWithRefs $ \(~[collatz', collatzOdd', collatzEven']) -> [d|
  collatz
    :: RepVal g Integer $(staticKeyType 'collatzOdd)
    => RepVal g Integer $(staticKeyType 'collatzEven)
    => Monad m => TEnv m g -> Integer -> m [Int]
  collatz env x = do
    pushLog $ "got: " <> show x
    if
      | x `elem` collatzCycle0 -> pure [0]
      | x `elem` collatzCycle1 -> pure [1]
      | x `elem` collatzCycle2 -> pure [2]
      | x `elem` collatzCycle3 -> pure [3]
      | x `elem` collatzCycle4 -> pure [4]
      | x `mod` 2 == 1 -> do
        pushTask (applyClosure $(pure collatzOdd') x)
        pure []
      | otherwise -> do
        pushTask (applyClosure $(pure collatzEven') x)
        pure []
    where TEnv {..} = env

  collatzOdd
    :: RepVal g Integer $(staticKeyType 'collatz)
    => Monad m => TEnv m g -> Integer -> m [Int]
  collatzOdd env x = do
    pushLog $ "got odd: " <> show x
    pushTask (applyClosure $(pure collatz') (3 * x + 1))
    pure []
    where TEnv {..} = env

  collatzEven
    :: RepVal g Integer $(staticKeyType 'collatz)
    => Monad m => TEnv m g -> Integer -> m [Int]
  collatzEven env x = do
    pushLog $ "got even: " <> show x
    pushTask (applyClosure $(pure collatz') (x `div` 2))
    pure []
    where TEnv {..} = env
  |]

mkDefStaticTab ['writeLog, 'collatz, 'collatzOdd, 'collatzEven]

-- In most use-cases, you don't need to distinguish between the tasks, and
-- 'TaskArg' (further below) is simpler and better . On the off-chance that you
-- do need to, this is how you would do that, using @$(staticKeyType 'KEY)@.
data Task =
    TaskLog !String
  | TaskCollatz !Integer
  | TaskCollatzOdd !Integer
  | TaskCollatzEven !Integer
  deriving (Show, Read, Eq, Ord)
instance RepVal Task String $(staticKeyType 'writeLog) where
  toRep _ = TaskLog
  fromRep _ (TaskLog i) = Right i
  fromRep _ t           = Left $ "expect TaskLog, got " <> show t
instance RepVal Task Integer $(staticKeyType 'collatz) where
  toRep _ = TaskCollatz
  fromRep _ (TaskCollatz i) = Right i
  fromRep _ t               = Left $ "expect TaskCollatz, got " <> show t
instance RepVal Task Integer $(staticKeyType 'collatzOdd) where
  toRep _ = TaskCollatzOdd
  fromRep _ (TaskCollatzOdd i) = Right i
  fromRep _ t                  = Left $ "expect TaskCollatzOdd, got " <> show t
instance RepVal Task Integer $(staticKeyType 'collatzEven) where
  toRep _ = TaskCollatzEven
  fromRep _ (TaskCollatzEven i) = Right i
  fromRep _ t                   = Left $ "expect TaskCollatzEven, got " <> show t

-- You can either define your own 'g' like here, or use one of the provided
-- ones, like 'DSerialise' or 'DBinary'.
data TaskArg =
    ArgString !String
  | ArgInteger !Integer
  deriving (Show, Read, Eq, Ord)
instance RepVal TaskArg String k where
  toRep _ = ArgString
  fromRep _ (ArgString i) = Right i
  fromRep _ t             = Left $ "expect ArgString, got " <> show t
instance RepVal TaskArg Integer k where
  toRep _ = ArgInteger
  fromRep _ (ArgInteger i) = Right i
  fromRep _ t              = Left $ "expect ArgInteger, got " <> show t

monadEnv
  :: RepVal g String $(staticKeyType 'writeLog)
  => MonadState [ClosureApply g] m => String -> TEnv m g
monadEnv prefix =
  let pushTask t = state (\tt -> ((), tt ++ [t]))
      pushLog s = pushTask (applyClosure $(staticRef 'writeLog) s)
  in  TEnv { .. }

runAllTasks
  :: forall g tm
   . RepVal g String $(staticKeyType 'writeLog)
  => RepVal g Integer $(staticKeyType 'collatz)
  => RepVal g Integer $(staticKeyType 'collatzOdd)
  => RepVal g Integer $(staticKeyType 'collatzEven)
  => MonadWriter [String] (tm IO)
  => MonadState [ClosureApply g] (tm IO)
  => MonadFail (tm IO)
  => (String -> TEnv (tm IO) g)
  -> (tm IO Int -> [ClosureApply g] -> IO (Int, [String]))
  -> [ClosureApply g]
  -> Int
  -> [String]
  -> IO ()
runAllTasks mkEnv evalT initCl expectRuns expectLogs = do
  (actualRuns, actualLogs) <- evalT (go 0) initCl
  assertEqual "runs" expectRuns actualRuns
  assertEqual "logs" expectLogs actualLogs
 where
  go i = state popTask >>= \case
    Nothing -> pure i
    Just t  -> do
      res <- run t
      let msg = (\c -> "result: cycle #" <> show c) <$> res
      state $ pushTasks $ applyClosure $(staticRef 'writeLog) <$> msg
      go (i + 1)
  popTask []       = (Nothing, [])
  popTask (h : tl) = (Just h, tl)
  pushTasks tt' tt = ((), tt ++ tt')
  run cl = case evalSomeClosure closureTab cl of
    Left  e -> fail (show e)
    Right r -> r
  closureTab =
    repClosureTab @_ @g
      $ mkClosureTab staticTab
      $ TCCons $(staticKey 'writeLog)    ()
      $ TCCons $(staticKey 'collatz)     (mkEnv "collatz")
      $ TCCons $(staticKey 'collatzOdd)  (mkEnv "collatzOdd")
      $ TCCons $(staticKey 'collatzEven) (mkEnv "collatzEven")
      $ TCNil @NullC2Sym0

tests :: TestTree
tests = testGroup
  "Control.Static.UnitTests"
  [ testCase "smoke @Task" $ do
    runAllTasks @Task @(RWST () [String] [ClosureApply Task])
      monadEnv
      (`evalRWST` ())
      [applyClosure $(staticRef 'collatz) (4 :: Integer)]
      3
      ["got: 4", "result: cycle #1"]
  , testCase "smoke @TaskArg" $ do
    runAllTasks @TaskArg @(RWST () [String] [ClosureApply TaskArg])
      monadEnv
      (`evalRWST` ())
      [applyClosure $(staticRef 'collatz) (30 :: Integer)]
      67
      (  ["got: 30", "got even: 30", "got: 15", "got odd: 15", "got: 46"]
      ++ ["got even: 46", "got: 23", "got odd: 23", "got: 70", "got even: 70"]
      ++ ["got: 35", "got odd: 35", "got: 106", "got even: 106", "got: 53"]
      ++ ["got odd: 53", "got: 160", "got even: 160", "got: 80", "got even: 80"]
      ++ ["got: 40", "got even: 40", "got: 20", "got even: 20", "got: 10"]
      ++ ["got even: 10", "got: 5", "got odd: 5", "got: 16", "got even: 16"]
      ++ ["got: 8", "got even: 8", "got: 4", "result: cycle #1"]
      )
  , testCase "smoke @DSerialise" $ do
    runAllTasks @DSerialise @(RWST () [String] [ClosureApply DSerialise])
      monadEnv
      (`evalRWST` ())
      [applyClosure $(staticRef 'collatz) (-30 :: Integer)]
      39
      (  ["got: -30", "got even: -30", "got: -15", "got odd: -15", "got: -44"]
      ++ ["got even: -44", "got: -22", "got even: -22", "got: -11"]
      ++ ["got odd: -11", "got: -32", "got even: -32", "got: -16"]
      ++ ["got even: -16", "got: -8", "got even: -8", "got: -4", "got even: -4"]
      ++ ["got: -2", "result: cycle #2"]
      )
  ]
