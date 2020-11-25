{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Control.Static.TH
  ( staticRef
  , staticKey
  , staticKeyType
  , mkStatics
  , mkStaticsWithRefs
  , defaultStaticTab
  , mkDefStaticTab
  , mkStaticTab
  -- special utils some users might need
  , CxtW(..)
  ) where

-- external
import           Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import           Data.Functor            (($>))
import           Data.List               (unzip5)
import           Data.Singletons         (sing)
import           GHC.IO.Unsafe           (unsafeDupableInterleaveIO)
import           Language.Haskell.TH

-- internal
import           Control.Static.Common   (CxtW (..), TCTab (..), TTab)
import           Control.Static.Static   (SKeyed (..), skeyedCons)


-- | Needed for 'mkStaticsWithRefs', definition taken from
-- https://gitlab.haskell.org/ghc/ghc/issues/12073
mfixQ :: (b -> Q b) -> Q b
mfixQ k = do
  m      <- runIO newEmptyMVar
  ans    <- runIO (unsafeDupableInterleaveIO (takeMVar m))
  result <- k ans
  runIO (putMVar m result)
  pure result

-- | Create top-level statically-keyed values from regular top-level values.
mkStatics :: [Name] -> Q [Dec]
mkStatics ns = mapM getType ns >>= createStatics Nothing

-- | Create top-level statically-keyed values from regular top-level values,
-- when their definitions need to refer to other statically-keyed values.
--
-- Since TH cannot handle references to names defined later in the source file,
-- it is not possible to use 'mkStatics' for this purpose; you must use this
-- function instead, and then register the names later using 'mkStaticTab'.
--
-- See unit tests for example usage.
mkStaticsWithRefs :: ([Exp] -> Q [Dec]) -> Q [Dec]
mkStaticsWithRefs mkDecs = do
  statics  <- mfixQ f
  decls    <- mkDecs statics
  closures <- createStatics Nothing (sigsOf decls)
  pure $ decls <> closures
 where
  -- note: f must be like this; as per the contract to 'mfix' one must not
  -- evaluate its argument in the definition, or we'll get an infinite loop
  f :: ([Exp] -> Q [Exp])
  f statics = do
    decls <- mkDecs statics
    traverse (staticRef . fst) (sigsOf decls)

defaultStaticTab :: Name
defaultStaticTab = mkName "staticTab"

-- | Create a table holding the static values for a list of top-level names,
-- binding it to the top-level name "staticTab".
mkDefStaticTab :: [Name] -> Q [Dec]
mkDefStaticTab = mkStaticTab defaultStaticTab

-- | Create a table holding the static values for a list of top-level names,
-- binding it to the given top-level name.
mkStaticTab :: Name -> [Name] -> Q [Dec]
mkStaticTab tabName ns = mapM getType ns >>= createStatics (Just tabName)

-- | Refer to a static value, as a 'SKeyed'.
--
-- Be sure to pass the argument to 'mkStaticTab' so the referent exists.
staticRef :: Name -> Q Exp
staticRef = varE . staticName

-- | Get the symbol key of a static value, as a 'Control.Static.SKey'.
--
-- Be sure to pass the argument to 'mkStaticTab' so the referent exists.
--
-- Users typically don't need this; 'staticRef' is more type-safe as it
-- includes the type of the value, and this does not.
staticKey :: Name -> Q Exp
staticKey name = [| sing @ $(symFQN name) |]

-- | Get the symbol key type of a static value, as a type-level string.
staticKeyType :: Name -> Q Type
staticKeyType = symFQN

-- Internal

createStatics :: Maybe Name -> [(Name, Type)] -> Q [Dec]
createStatics tabName sigs = do
  (closures, tyVars, keys, vals, inserts) <- unzip5 <$> mapM genStaticDefs sigs
  staticTab <- maybe (pure [])
                     (\n -> genStaticTab n (concat tyVars) keys vals inserts)
                     tabName
  pure $ concat closures <> staticTab

genStaticTab :: Name -> [TyVarBndr] -> [Q Type] -> [Q Type] -> [Q Exp] -> Q [Dec]
genStaticTab name tyVars keys vals is = sequence
  [ sigD name $ do
    ForallT tyVars [] <$> [t| TTab $(tyList keys) $(tyList vals) |]
  , sfnD name $ apList is [| TCNil |]
  ]

genStaticDefs :: (Name, Type) -> Q ([Dec], [TyVarBndr], Q Type, Q Type, Q Exp)
genStaticDefs (fullName, fullType) = do
  tyTval <- [t| SKeyed |]
  tyCxtw <- [t| CxtW |]
  --fail $ show fullType
  let (tyVars', tyCxt', typ') = case fullType of
        ForallT vars cxt' mono -> (vars, cxt', mono)
        _                      -> ([], [], fullType)
  let tyCxt1 = cxtToType tyCxt'

  -- If there is a constraint, have it wrapped in a CxtW later
  let cxtVal mk n = appE (conE 'CxtW) (mk n)
      (maybeCxt, maybeCxtTy) = case tyCxt' of
        [] -> (id, pure)
        _  -> (cxtVal, \typ -> pure (tyCxtw `AppT` tyCxt1 `AppT` typ))

  -- If the type is of the special forms
  --   - (SKeyed s T -> T) or
  --   - (C => SKeyed s (CxtW C T) -> T)
  -- this means it wants the staticRef passed in as an argument, so arrange for
  -- that to be done later too.
  --
  -- TODO: we probably don't need this, now that we have 'mkStaticsWithRefs'.
  let
    fixVal mk n = appE (mk n) (staticRef n)
    (maybeFix, tyVars, typ) = case typ' of
      ArrowT `AppT` (t `AppT` (VarT sym) `AppT` (c `AppT` cxt' `AppT` typ_)) `AppT` typX
        | t == tyTval && c == tyCxtw && cxt' == tyCxt1 && typ_ == typX
        -> (fixVal, filter (\v -> tyVarName v /= sym) tyVars', typX)

      ArrowT `AppT` (tyTval' `AppT` (VarT sym) `AppT` typ_) `AppT` typX
        | tyTval' == tyTval && typ_ == typX
        -> (fixVal, filter (\v -> tyVarName v /= sym) tyVars', typX)

      _ -> (id, tyVars', typ')

  let mkVal = maybeCxt (maybeFix varE)
  let tyK   = symFQN fullName
  let tyV   = maybeCxtTy typ
  let name  = staticName fullName

  -- define the static only if it wasn't already defined, e.g. via mkStaticsWithRefs
  static <- flip recover (reify name $> []) $ sequence
    [ sigD name $ ForallT tyVars [] <$> [t| SKeyed $(tyK) $(tyV) |]
    , sfnD name [| SKeyed sing $(mkVal fullName) |]
    ]
  pure (static, tyVars, tyK, tyV, [| skeyedCons $(staticRef fullName) |])

staticName :: Name -> Name
staticName n = mkName $ nameBase n ++ "__static"

-- Utils

-- | Apply a list of expressions to a base expression.
apList :: [Q Exp] -> Q Exp -> Q Exp
apList []       base = base
apList (e : es) base = [| $e $ $(apList es base) |]

-- | Construct a promoted-list of types.
tyList :: [Q Type] -> Q Type
tyList []       = promotedNilT
tyList (h : tl) = do
  ty <- h
  (PromotedConsT `AppT` ty `AppT`) <$> tyList tl

-- | Convert a context (a list of types) to a single type.
cxtToType :: Cxt -> Type
cxtToType cxt' = case cxt' of
  []  -> TupleT 0
  [t] -> t
  _   -> go (TupleT (length cxt')) cxt'   where
    go part []       = part
    go part (h : tl) = go (part `AppT` h) tl

-- | Look up the "original name" (module:name) and type of a top-level function
getType :: Name -> Q (Name, Type)
getType name = do
  info <- reify name
  case info of
    VarI origName typ _ -> pure (origName, typ)
    _                   -> fail $ show name ++ " not a type: " ++ show info

-- | Extract type info from top-level decls without using 'reify'.
sigsOf :: [Dec] -> [(Name, Type)]
sigsOf []              = []
sigsOf (SigD n t : tl) = (n, simplifyType t) : sigsOf tl
sigsOf (_        : tl) = sigsOf tl

-- | Simplify a source-level type. This attempts to do what 'reify' does but
-- without needing the definition to exist at the splice point.
simplifyType :: Type -> Type
simplifyType (ForallT t0 c0 (ForallT t1 c1 t)) =
  simplifyType (ForallT (t0 <> t1) (c0 <> c1) t)
simplifyType t = t

-- | Variation on 'funD' which takes a single expression to define the function
sfnD :: Name -> Q Exp -> Q Dec
sfnD n e = funD n [clause [] (normalB e) []]

-- | The name of a type variable binding occurrence
tyVarName :: TyVarBndr -> Name
tyVarName (PlainTV n   ) = n
tyVarName (KindedTV n _) = n

-- | Fully qualified name, as a type-level String literal of kind Symbol
symFQN :: Name -> Q Type
symFQN n = do
  loc <- location
  pure $ LitT $ StrTyLit $ loc_module loc ++ "." ++ nameBase n
