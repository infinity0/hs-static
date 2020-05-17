module Control.Static
  (
  -- * Common definitions
    TCTab(..)
  -- * Static keys and values
  , SKey
  , SKeyed(..)
  , SKeyedExt(..)
  , withSKeyedExt
  , toSKeyedExt
  -- * Static tables and resolving values
  , gwithStatic
  , withStaticCts
  , withSomeStaticCts
  , withStaticCxt
  , withSomeStaticCxt
  -- * Static closures
  , PreClosure(..)
  , Closure(..)
  , PostClosure(..)
  , ClosureApply
  , applyClosure
  , envTabCons
  , envTabNil
  , mkClosureTab
  , RepClosure
  , RepClosure'
  , repClosureTab
  , withEvalClosureCts
  , withEvalSomeClosureCts
  , withEvalClosureCxt
  , withEvalSomeClosureCxt
  , evalClosure
  , evalSomeClosure
  -- * Serialisation
  , RepVal(..)
  , SKeyedError(..)
  , DoubleEncoding(..)
  , DSerialise
  , DBinary
  )
where

import           Control.Static.Closure
import           Control.Static.Common
import           Control.Static.Serialise
import           Control.Static.Static

-- Note, the implementation comments in these files make various references to
-- "singletons defunctionalisation symbols", see here for an approachable
-- explanation:
--
-- https://blog.jle.im/entry/introduction-to-singletons-4.html#defunctionalization
--
-- You may want to start from part 1, if you have trouble jumping in the middle.
