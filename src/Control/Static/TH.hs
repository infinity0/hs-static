{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Control.Static.TH
  ( staticRef
  , staticKey
  , staticKeyType
  , mkStaticTab
  , mkStaticTab'
  -- special utils some users might need
  , CxtW(..)
  )
where

-- external
import           Data.List                (unzip5)
import           Data.Singletons          (type (@@), sing)
import           Language.Haskell.TH

-- internal
import           Control.Static.Common    (CxtW (..), TCTab (..), TTab)
import           Control.Static.Serialise (SKeyedInternal (..))


-- | Create a table holding the static values for a list of top-level names,
-- binding it to the top-level name "staticTab".
mkStaticTab :: [Name] -> Q [Dec]
mkStaticTab = mkStaticTab' (mkName "staticTab")

-- | Create a table holding the static values for a list of top-level names,
-- binding it to the given top-level name.
mkStaticTab' :: Name -> [Name] -> Q [Dec]
mkStaticTab' tabName ns = do
  types     <- mapM getType ns
  (closures, tyVars, keys, vals, inserts) <- unzip5 <$> mapM generateDefs types
  staticTab <- createMetaData tabName (concat tyVars) keys vals inserts
  pure $ concat closures ++ staticTab

-- | Refer to a static value, as a 'SKeyedInternal'.
--
-- Be sure to pass the argument to 'mkStaticTab' so the referent exists.
staticRef :: Name -> Q Exp
staticRef = varE . staticName

-- | Get the symbol key of a static value, as a 'SKey'.
--
-- Be sure to pass the argument to 'mkStaticTab' so the referent exists.
--
-- This is useful for referring to the key inside the definition of the value
-- itself, e.g. inside a recursive function or mutually-recursive functions.
--
-- Note: this omits the type of the value, so the caller is responsible for
-- using it with a value of the correct associated type. If this is not done,
-- then a later attempt at runtime to resolve this in a static table will cause
-- a 'Control.Static.Serialise.SKeyedExtDecodeFailure'.
--
-- One way of recovering compile-time type safety is to ensure that an instance
-- of 'RepVal g v k' exists only for your desired @g@ @v@ and @k@, but this may
-- be less convenient than defining a generic instance for all @k@.
staticKey :: Name -> Q Exp
staticKey name = [| sing @ $(symFQN name) |]

staticKeyType :: Name -> Q Type
staticKeyType = symFQN

-- Internal

createMetaData :: Name -> [TyVarBndr] -> [Q Type] -> [Q Type] -> [Q Exp] -> Q [Dec]
createMetaData name tyVars keys vals is = sequence
  [ sigD name $ do
    ForallT tyVars [] <$> [t| TTab $(tyList keys) $(tyList vals) |]
  , sfnD name $ apList is [| TCNil |]
  ]

generateDefs :: (Name, Type) -> Q ([Dec], [TyVarBndr], Q Type, Q Type, Q Exp)
generateDefs (fullName, fullType) = do
  tyTval <- [t| SKeyedInternal |]
  tyCxtw <- [t| CxtW |]
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
  --   - (SKeyedInternal s T -> T) or
  --   - (C => SKeyedInternal s (CxtW C T) -> T)
  -- this means it wants the staticRef passed in as an argument, so arrange for
  -- that to be done later too.
  --
  -- TODO: maybe we actually don't need this, now that we have 'staticKey'.
  -- however it is a bit more type-safe than 'staticKey'.
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
  static <- sequence
    [ sigD name $ ForallT tyVars [] <$> [t| SKeyedInternal $(tyK) $(tyV) |]
    , sfnD name [| SKeyedInternal sing $(mkVal fullName) |]
    ]
  pure (static, tyVars, tyK, tyV, [| tcCons $(staticRef fullName) |])

tcCons
  :: (c @@ k @@ v)
  => SKeyedInternal k v
  -> TCTab c kk vv
  -> TCTab c (k ': kk) (v ': vv)
tcCons (SKeyedInternal k v) = TCCons k v

staticName :: Name -> Name
staticName n = mkName $ nameBase n ++ "__static"

-- Utils

apList :: [Q Exp] -> Q Exp -> Q Exp
apList []       base = base
apList (e : es) base = [| $e $ $(apList es base) |]

tyList :: [Q Type] -> Q Type
tyList []       = promotedNilT
tyList (h : tl) = do
  ty <- h
  (PromotedConsT `AppT` ty `AppT`) <$> tyList tl

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
