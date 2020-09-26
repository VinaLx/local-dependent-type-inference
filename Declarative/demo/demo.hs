{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer

import Data.Char (ord, chr)
import Data.List

import Text.Printf (printf)
import Debug.Trace


data Kind = KStar | KBox | KEx Int
  deriving (Eq)

smallIntToChar :: Char -> Int -> Char
smallIntToChar a n = chr (ord a + n)

intToVar' :: Char -> Int -> String
intToVar' a n | n < 26 = return $ smallIntToChar a n
intToVar' a n =
  intToVar' a  (n `div` 26) ++ return (smallIntToChar a (n `mod` 26))

intToVar :: Int -> String
intToVar = intToVar' 'a'

intToTypeVar :: Int -> String
intToTypeVar = intToVar' 'A'

instance Show Kind where
  show = \case
    KStar -> "*"
    KBox -> "<>"
    KEx n -> printf "<%s>" (intToVar n)

data Expr
  = Var  Int
  | ExVar Int
  | EKind Kind
  | EInt
  | ELit  Int
  | EApp Expr Expr
  | EAbs Expr (Expr -> Expr)
  | EPi  Expr (Expr -> Expr)
  | EAll Expr (Expr -> Expr)
  | EBind   Expr (Expr -> Expr)
  | EMu Expr (Expr -> Expr)
  | ECastUp Expr Expr
  | ECastDn Expr

showE' :: Int -> Expr -> State Int String
showE' prec = \case
  Var x   -> return $ intToVar x
  ExVar x -> return $ '^' : intToVar x
  EKind k -> return $ show k
  EInt -> return "Int"
  ELit n -> return $ show n
  EApp e1 e2 -> enclose 10 $
    return (printf "(%s) %s") <*> showE' 10 e1 <*> showE' 9 e2
  EAbs  a b -> showBinder "lambda" a b
  EPi   a b -> showBinder "pi"     a b
  EAll  a b -> showBinder "forall" a b
  EBind a b -> showBinder "bind"   a b
  EMu   a b -> showBinder "mu"   a b
  ECastUp a b -> enclose 10 $
    return (printf "castup [%s] %s") <*> showE' 0 a <*> showE' 10 b
  ECastDn a -> enclose 10 $
    return (printf "castdn %s") <*> showE' 10 a
  where
    showBinder :: String -> Expr -> (Expr -> Expr) -> State Int String
    showBinder symbol a b = enclose 10 $ get >>= \n -> do
      modify (+1)
      sa <- showE' 10 a
      let sv = intToVar n
      sb <- showE' 9 (b (Var n))
      return $ printf "%s %s : %s. %s" symbol sv sa sb
    enclose :: Int -> State Int String -> State Int String
    enclose p m = if p > prec then m else printf "(%s)" <$> m

showE :: Int -> Expr -> String
showE n = flip evalState n . (showE' 0)

instance Show Expr where
  show = showE 0

eArrow :: Expr -> Expr -> Expr
eArrow a b = EPi a (const b)

eStar :: Expr
eStar = EKind KStar

eBox :: Expr
eBox = EKind KBox

eqExpr :: Int -> Expr -> Expr -> Bool
eqExpr n = curry $ \case
  (Var  n1, Var  n2) -> n1 == n2
  (ExVar n1, ExVar n2) -> n1 == n2
  (EKind k1, EKind k2) -> k1 == k2
  (ELit  n1, ELit  n2) -> n1 == n2
  (EInt, EInt) -> True
  (EApp f1 a1, EApp f2 a2) -> eqExpr n f1 f2 && eqExpr n a1 a2
  (EAbs a1 b1, EAbs a2 b2) ->
    eqExpr n a1 a2 && eqExpr (n + 1) (b1 (Var n)) (b2 (Var n))
  (EPi a1 b1, EPi a2 b2) ->
    eqExpr n a1 a2 && eqExpr (n + 1) (b1 (Var n)) (b2 (Var n))
  (EAll a1 b1, EAll a2 b2) ->
    eqExpr n a1 a2 && eqExpr (n + 1) (b1 (Var n)) (b2 (Var n))
  (EBind a1 b1, EBind a2 b2) ->
    eqExpr n a1 a2 && eqExpr (n + 1) (b1 (Var n)) (b2 (Var n))
  (EMu a1 b1, EMu a2 b2) ->
    eqExpr n a1 a2 && eqExpr (n + 1) (b1 (Var n)) (b2 (Var n))
  (ECastUp a1 b1, ECastUp a2 b2) -> eqExpr n a1 a2 && eqExpr n b1 b2
  (ECastDn a1, ECastDn a2) -> eqExpr n a1 a2
  _ -> False

instance Eq Expr where
  (==) = eqExpr 0

substEx :: Int -> Expr -> Expr -> Expr
substEx n e v = case e of
  ExVar n'    -> if n == n' then v else ExVar n'
  EApp e1 e2  -> EApp    (recurse e1) (recurse e2)
  EAbs    a b -> EAbs    (recurse a) $ recurse . b
  EPi     a b -> EPi     (recurse a) $ recurse . b
  EAll    a b -> EAll    (recurse a) $ recurse . b
  EBind   a b -> EBind   (recurse a) $ recurse . b
  EMu     a b -> EMu     (recurse a) $ recurse . b
  ECastUp a b -> ECastUp (recurse a) (recurse b)
  ECastDn a   -> ECastDn (recurse a)
  e'          -> e'
  where
    recurse e' = substEx n e' v

substK' :: Int -> Kind -> Kind -> Kind
substK' n k v = case k of
  KEx n' -> if n == n' then v else (KEx n')
  _      -> k

substK :: Int -> Expr -> Kind -> Expr
substK n e k = case e of
  EKind k'    -> EKind (substK' n k' k)
  EApp e1 e2  -> EApp    (recurse e1) (recurse e2)
  EAbs    a b -> EAbs    (recurse a) $ recurse . b
  EPi     a b -> EPi     (recurse a) $ recurse . b
  EAll    a b -> EAll    (recurse a) $ recurse . b
  EBind   a b -> EBind   (recurse a) $ recurse . b
  EMu     a b -> EMu     (recurse a) $ recurse . b
  ECastUp a b -> ECastUp (recurse a) (recurse b)
  ECastDn a   -> ECastDn (recurse a)
  e'          -> e'
  where
    recurse e' = substK n e' k

substV :: Int -> Expr -> Expr -> Expr
substV n e v = case e of
  Var n'      -> if n == n' then v else Var n'
  EApp e1 e2  -> EApp    (recurse e1) (recurse e2)
  EAbs    a b -> EAbs    (recurse a) $ recurse . b
  EPi     a b -> EPi     (recurse a) $ recurse . b
  EAll    a b -> EAll    (recurse a) $ recurse . b
  EBind   a b -> EBind   (recurse a) $ recurse . b
  EMu     a b -> EMu     (recurse a) $ recurse . b
  ECastUp a b -> ECastUp (recurse a) (recurse b)
  ECastDn a   -> ECastDn (recurse a)
  e'          -> e'
  where
    recurse e' = substV n e' v

occurV :: Int -> Expr -> Bool
occurV n e = case e of
  Var n'      -> n == n'
  EApp e1 e2  -> occurV n e1 || occurV n e2
  EAbs    a b -> occurV n a || occurV n (b EInt)
  EPi     a b -> occurV n a || occurV n (b EInt)
  EAll    a b -> occurV n a || occurV n (b EInt)
  EBind   a b -> occurV n a || occurV n (b EInt)
  EMu     a b -> occurV n a || occurV n (b EInt)
  ECastUp a b -> occurV n a || occurV n b
  ECastDn a   -> occurV n a
  e'          -> False


occurEx :: Int -> Expr -> Bool
occurEx n e = case e of
  ExVar n'    -> n == n'
  EApp e1 e2  -> occurEx n e1 || occurEx n e2
  EAbs    a b -> occurEx n a || occurEx n (b EInt)
  EPi     a b -> occurEx n a || occurEx n (b EInt)
  EAll    a b -> occurEx n a || occurEx n (b EInt)
  EBind   a b -> occurEx n a || occurEx n (b EInt)
  EMu     a b -> occurEx n a || occurEx n (b EInt)
  ECastUp a b -> occurEx n a || occurEx n b
  ECastDn a   -> occurEx n a
  e'          -> False

occurK :: Int -> Expr -> Bool
occurK n e = case e of
  EKind (KEx n') -> n == n'
  EApp   e1 e2   -> occurK n e1 || occurK n e2
  EAbs    a b    -> occurK n a || occurK n (b EInt)
  EPi     a b    -> occurK n a || occurK n (b EInt)
  EAll    a b    -> occurK n a || occurK n (b EInt)
  EBind   a b    -> occurK n a || occurK n (b EInt)
  EMu     a b    -> occurK n a || occurK n (b EInt)
  ECastUp a b    -> occurK n a || occurK n b
  ECastDn a      -> occurK n a
  e'             -> False

fvEx :: Expr -> [Int]
fvEx = \case
  ExVar n    -> [n]
  EApp e1 e2  -> fvEx e1 `union` fvEx e2
  EAbs    a b -> fvEx a `union` fvEx (b EInt)
  EPi     a b -> fvEx a `union` fvEx (b EInt)
  EAll    a b -> fvEx a `union` fvEx (b EInt)
  EBind   a b -> fvEx a `union` fvEx (b EInt)
  EMu     a b -> fvEx a `union` fvEx (b EInt)
  ECastUp a b -> fvEx a `union` fvEx b
  ECastDn a   -> fvEx a
  e'          -> []

data Work
  = WCheck Expr Expr Expr
  | WVar   Int Expr
  | WExVar Int Expr
  | WKEx   Int
  | WInfer Expr Expr (Expr -> [Work])
  | WInferApp Expr Expr (Expr -> [Work])
  | WDone Expr
  | WUnifyL Int Expr
  | WUnifyR Expr Int
  | WUnifyK Int Kind
  | WReduce Expr (Expr -> [Work])
  | WFail InferError

type WorkList = [Work]

showW' :: Int -> Work -> String
showW' n = \case
  WCheck e1 e2 e3 ->
    printf "%s <: %s : %s" (showE n e1) (showE n e2) (showE n e3)
  WVar n' e ->
    printf "%s : %s" (intToVar n') (showE n e)
  WExVar n' e ->
    printf "^%s : %s" (intToVar n') (showE n e)
  WKEx n' -> printf "<%s>" (intToVar n')
  WInfer e1 e2 k ->
    printf "%s <: %s =>%s (%s)"
      (showE n e1) (showE n e2) (intToVar n) (showWL' (n + 1) (k (Var n)))
  WInferApp a e k ->
    printf "%s . %s =>%s (%s)"
      (showE n a) (showE n e) (intToVar n) (showWL' (n + 1) (k (Var n)))
  WDone e -> showE n e
  WUnifyL n' e ->
    printf "^%s <: %s" (intToVar n') (showE n e)
  WUnifyR e n' ->
    printf "%s <: ^%s" (showE n e) (intToVar n')
  WUnifyK n' k ->
    printf "<%s> = %s" (intToVar n') (show k)
  WReduce e k ->
    printf "%s -->%s (%s)"
      (showE n e) (intToVar n) (showWL' (n + 1) (k (Var n)))
  WFail e ->
    "ERROR"


maxVarNum :: [Work] -> Int
maxVarNum = flip foldr (-1) $ \w n -> case w of
  WVar n' _   -> max n n'
  WExVar n' _ -> max n n'
  WKEx n'     -> max n n'
  _           -> n

showWL' :: Int -> [Work] -> String
showWL' n ws = intercalate " |- " (showW' startN <$> reverse ws)
  where startN = max (maxVarNum ws + 1) n

showWL :: [Work] -> String
showWL = showWL' 0

assocV :: Int -> WorkList -> Maybe Expr
assocV _ []             = Nothing
assocV m (WVar n e : _) | m == n = Just e
assocV m (_ : ws)       = assocV m ws

assocE :: Int -> WorkList -> Maybe Expr
assocE _ []               = Nothing
assocE m (WExVar n e : _) | m == n = Just e
assocE m (_ : ws)         = assocV m ws

data InferState
  = InferState
  { varCounter :: Int
  , workList   :: WorkList
  }

betaReduce :: Expr -> Maybe Expr
betaReduce = \case
  EApp (EAbs a b) e -> return $ b e
  EApp f e -> (\f' -> EApp f' e) <$> betaReduce f
  e@(EMu a b) -> return $ b e
  _ -> Nothing


data InferError
  = EmptyStack
  | TypeError
  | SubtypeError Expr Expr
  | OutOfScopeVar Int
  | OccurenceError Int Expr
  | NoInstantiation Expr
  | IrreducibleExpr Expr
  deriving Show


newtype RuleLog = RuleLog [String]
  deriving (Semigroup, Monoid)

popWork :: MonadError InferError m
        => MonadState InferState m
        => m Work
popWork = workList <$> get >>= \case
  [] -> throwError EmptyStack
  w : ws -> putWork ws >> return w

modifyWork :: MonadState InferState m
           => ([Work] -> [Work]) -> m ()
modifyWork f = get >>= \InferState {..} ->
  put $ InferState varCounter (f workList)

getWork :: MonadState InferState m
        => m [Work]
getWork = workList <$> get

putWork :: MonadState InferState m
        => [Work] -> m ()
putWork = modifyWork . const

pushWork :: MonadState InferState m
         => Work -> m ()
pushWork = modifyWork . (:)

prependWorks :: MonadState InferState m
             => [Work] -> m ()
prependWorks = modifyWork . (++)

nextVar :: MonadState InferState m
        => m Int
nextVar = get >>= \InferState {..} ->
  put (InferState (1 + varCounter) workList) >>
  return varCounter

isMono :: Expr -> Bool
isMono = \case
  EAll    a b -> False
  EApp  e1 e2 -> isMono e1 && isMono e2
  EAbs    a b -> isMono a && isMono (b EInt)
  EPi     a b -> isMono a && isMono (b EInt)
  EBind   a b -> isMono a && isMono (b EInt)
  EMu     a b -> isMono a && isMono (b EInt)
  ECastUp a b -> isMono a && isMono b
  ECastDn a   -> isMono a
  e'          -> True

freshKind :: MonadState InferState m => m Kind
freshKind = do
  n <- nextVar
  pushWork $ WKEx n
  return (KEx n)

freshExOf :: MonadState InferState m => Expr -> m Expr
freshExOf e = do
  n <- nextVar
  pushWork $ WExVar n e
  return (ExVar n)

freshVarOf :: MonadState InferState m => Expr -> m Expr
freshVarOf e = do
  n <- nextVar
  pushWork $ WVar n e
  return (Var n)

varNum :: Expr -> Int
varNum = \case
  Var n -> n
  ExVar n -> n
  _ -> error "Fatal error: not a variable"

substWorkList'
  :: MonadError InferError m
  => Int -> Expr -> [Work] -> [Work] -> m [Work]
substWorkList' ex v replaces = \case
  [] -> return []
  w : ws -> case w of
    WVar n e | occurV n v -> throwError (OutOfScopeVar n)
    WVar n e -> (WVar n (subst e) :) <$> recurse ws
    WExVar n e | n == ex ->
      return $ replaces ++ ws
    WExVar n e | occurEx n v ->
      substWorkList' ex v (w : replaces) ws
    WExVar n e ->
      (WExVar n (subst e) :) <$> recurse ws
    WKEx n | occurK n v ->
      substWorkList' ex v (w : replaces) ws
    WKEx n ->
      (w :) <$> recurse ws
    WCheck e1 e2 e3 ->
      consRecurse (WCheck (subst e1) (subst e2) (subst e3)) ws
    WInfer e1 e2 k ->
      consRecurse
        (WInfer (subst e1) (subst e2) (\e -> recurse' (k e))) ws
    WInferApp e1 e2 k ->
      consRecurse
        (WInferApp (subst e1) (subst e2) (\e -> recurse' (k e))) ws
    WDone e ->
      consRecurse (WDone (subst e)) ws
    WUnifyL n e ->
      consRecurse (WUnifyL n (subst e)) ws
    WUnifyR e n ->
      consRecurse (WUnifyR (subst e) n) ws
    WUnifyK n k ->
      consRecurse (WUnifyK n k) ws
    WReduce e k ->
      consRecurse
        (WReduce (subst e) (\e' -> recurse' (k e'))) ws
    WFail e ->
      consRecurse w ws
  where
    subst e = substEx ex e v
    recurse = substWorkList' ex v replaces
    consRecurse w ws = (w :) <$> recurse ws
    recurse' = substWorkListNoScope ex v

substWorkListNoScope :: Int -> Expr -> [Work] -> [Work]
substWorkListNoScope ex v = \case
  [] -> []
  w : ws -> case w of
    WVar n e | occurV n v ->
      error ("Fatal error: invalid scope of variable" ++ show n)
    WVar n e ->
      WVar n (subst e) : recurse ws
    WExVar n e | n == ex ->
      error ("Fatal error: existential declared in a continuation: " ++ show n)
    WExVar n e | occurV n v ->
      error ("Fatal error: invalid scope of existential: " ++ show n)
    WExVar n e ->
      WExVar n (subst e) : recurse ws
    WKEx n | occurV n v ->
      error ("Fatal error: invalid scope of kind existential: " ++ show n)
    WKEx n ->
      WKEx n : recurse ws
    WCheck e1 e2 e3 ->
      WCheck (subst e1) (subst e2) (subst e3) : recurse ws
    WInfer e1 e2 k ->
      WInfer (subst e1) (subst e2) (\e -> recurse (k e)) : recurse ws
    WInferApp e1 e2 k ->
      WInferApp (subst e1) (subst e2) (\e -> recurse (k e)) : recurse ws
    WDone e ->
      WDone (subst e) : recurse ws
    WUnifyL n e ->
      WUnifyL n (subst e) : recurse ws
    WUnifyR e n ->
      WUnifyR (subst e) n : recurse ws
    WUnifyK n k ->
      WUnifyK n k : recurse ws
    WReduce e k ->
      WReduce (subst e) (\e' -> recurse (k e)) : recurse ws
    WFail e ->
      w : recurse ws
  where
    subst e = substEx ex e v
    recurse = substWorkListNoScope ex v

substWorkListK' :: Int -> Kind -> [Int] -> [Work] -> [Work]
substWorkListK' ex k replaces = \case
  [] -> []
  w : ws -> case w of
    WVar n e ->
      WVar n (subst e) : recurse ws
    WExVar n e ->
      WExVar n (subst e) : recurse ws
    WKEx n | n == ex ->
      fmap WKEx replaces ++ ws
    WKEx n -> case k of
      KEx n' | n == n' -> substWorkListK' ex k (n : replaces) ws
      _                -> w : recurse ws
    WCheck e1 e2 e3 ->
      WCheck (subst e1) (subst e2) (subst e3) : recurse ws
    WInfer e1 e2 k ->
      WInfer (subst e1) (subst e2) (\e -> recurse (k e)) : recurse ws
    WInferApp e1 e2 k ->
      WInferApp (subst e1) (subst e2) (\e -> recurse (k e)) : recurse ws
    WDone e ->
      WDone (subst e) : recurse ws
    WUnifyL n e ->
      WUnifyL n (subst e) : recurse ws
    WUnifyR e n ->
      WUnifyR (subst e) n : recurse ws
    WUnifyK n k' ->
      WUnifyK n (substK' ex k' k) : recurse ws
    WReduce e k ->
      WReduce (subst e) (\e' -> recurse (k e')) : recurse ws
    WFail e ->
      w : recurse ws
  where
    subst e = substK ex e k
    recurse = substWorkListK' ex k replaces

substWorkListK :: Int -> Kind -> [Work] -> [Work]
substWorkListK ex k = substWorkListK' ex k []

substWorkList
  :: MonadError InferError m
  => Int -> Expr -> [Work] -> m [Work]
substWorkList ex v = substWorkList' ex v []

infer :: MonadState InferState m
      => MonadWriter RuleLog m
      => MonadError InferError m
      => (Expr -> [Work]) -> Expr -> Expr -> m [Work]
infer c = curry $ \case
  (Var n1, Var n2) | n1 == n2 ->
    assocV n1 <$> getWork >>= \case
      Just e  -> return $ c e
      Nothing -> throwError (OutOfScopeVar n1)
  (EKind KStar, EKind KStar) -> return $ c $ EKind KBox
  (EInt, EInt) -> return $ c $ EKind KStar
  (ELit m, ELit n) | m == n -> return $ c EInt
  (EApp f1 a1, EApp f2 a2) | a1 == a2 && isMono a1 -> do
    return [WInfer f1 f2 $ \tf -> [WInferApp tf a1 c]]
  (EAbs a1 b1, EAbs a2 b2) | a1 == a2 -> do
    k1 <- freshKind
    k2 <- freshKind
    v <- freshVarOf a1
    return $
      [ WCheck a1 a2 (EKind k1)
      , WInfer (b1 v) (b2 v) $ \tb ->
          WCheck tb tb (EKind k2) :
          c (EPi a1 (\e -> substV (varNum v) tb e))
      ]
  (EPi a1 b1, EPi a2 b2) -> do
    k1 <- freshKind
    k2 <- freshKind
    v1 <- freshVarOf a1
    v2 <- freshVarOf a2
    return $
      [ WCheck a2 a1 (EKind k1)
      , WCheck (b1 v1) (b1 v1) (EKind k1)
      , WCheck (b1 v2) (b2 v2) (EKind k2)]
      ++ c (EKind k2)
  (EBind a1 b1, EBind a2 b2) | a1 == a2 -> do
    k <- freshKind
    x <- freshVarOf a1
    return $
      [ WCheck a1 a2 (EKind k)
      , WInfer (b1 x) (b2 x) $ \tb ->
          WCheck tb tb eStar :
          c (EAll a1 (\e -> substV (varNum x) tb e))
      ]
  (e1@(EMu a1 b1), e2@(EMu a2 b2)) | a1 == a2 -> do
    k <- freshKind
    x <- freshVarOf a1
    let b1' = b1 x
        b2' = b2 x
    if b1' == b2'
      then return $
        [ WCheck a1 a2 (EKind k)
        , WInfer b1' b2' $ \tb ->
           WCheck tb a1 (EKind k) : c a1
        ]
      else throwError $ SubtypeError e1 e2
  (ECastUp a1 b1, ECastUp a2 b2) | a1 == a2 -> do
    k <- freshKind
    return $ return $ WInfer b1 b2 $ \e -> case betaReduce a1 of
      Nothing -> return $ WFail $ IrreducibleExpr a1
      Just a' -> return $ WCheck e a' (EKind k)
  (ECastDn a1, ECastDn a2) -> return $ return $ WInfer a1 a2 $ \e ->
     return $ WReduce e $ \e' -> c e'

  (EAll a1 b1, EAll a2 b2) | a1 == a2 -> do
    k <- freshKind
    x <- freshVarOf a1
    return $
      [ WCheck a1 a2 (EKind k)
      , WCheck (b1 x) (b2 x) eStar] ++ c eStar
  (e, EAll a b) -> do
    k <- freshKind
    x <- freshVarOf a
    return $
      [ WCheck a a (EKind k)
      , WCheck a (b x) eStar] ++ c eStar
  (EAll a b, e) -> do
    k <- freshKind
    x <- freshVarOf a
    v <- freshExOf a
    return $
      [ WCheck a a (EKind k)
      , WCheck (b x) (b x) eStar
      , WCheck (b v) e eStar] ++ c eStar
  (ExVar n1, ExVar n2) | n1 == n2 ->
    assocE n1 <$> getWork >>= \case
      Nothing -> throwError (OutOfScopeVar n1)
      Just t -> return $ c t
  (ExVar n, e) -> return [WUnifyL n e]
  (e, ExVar n) -> return [WUnifyR e n]
  (e1, e2) -> throwError $ SubtypeError e1 e2

doWorkListSubst
  :: MonadState InferState m
  => MonadWriter RuleLog m
  => MonadError InferError m
  => Int -> Expr -> m ()
doWorkListSubst ex v = if occurEx ex v
  then throwError $ OccurenceError ex v
  else getWork >>= substWorkList ex v >>= putWork

check :: MonadState InferState m
      => MonadWriter RuleLog m
      => MonadError InferError m
      => Expr -> Expr -> Expr -> m [Work]
check e1 e2 t = do
  k <- freshKind
  return $ return $ WInfer e1 e2 $ \t' ->
    case (t, t') of
      (EKind KBox, EKind KBox) -> []
      (EKind (KEx k1), EKind (KEx k2)) | k1 == k2 -> []
      (EKind k1, EKind (KEx kex)) -> return $ WUnifyK kex k1
      (EKind (KEx kex), EKind k2) -> return $ WUnifyK kex k2
      _ -> return $ WCheck t' t (EKind k)

inferApp
  :: MonadState InferState m
  => MonadWriter RuleLog m
  => MonadError InferError m
  => (Expr -> [Work]) -> Expr -> Expr -> m [Work]
inferApp k = curry $ \case
  (EPi a b, e) -> return $ WCheck e e a : k (b e)
  (EAll a b, e) -> do
    ex <- freshExOf a
    return [WInferApp (b ex) e k]
  (ExVar n, e) -> undefined


findLessThan'
  :: MonadState InferState m
  => MonadError InferError m
  => Expr -> Expr -> m Expr
findLessThan' o = \case
  EApp e1 e2 | not (isMono e2) -> noInstantiationError
  EApp e1 e2 -> (\e1' -> EApp e1' e2) <$> recurse e1
  EAbs a b | not (isMono a) -> noInstantiationError
  EAbs a b -> do
    n <- nextVar
    b' <- recurse (b (Var n))
    return $ EAbs a $ \e -> substV n b' e
  EPi a b -> do
    a' <- findGreaterThan' o a
    n <- nextVar
    b' <- recurse (b (Var n))
    return $ EPi a $ \e -> substV n b' e
  EAll a b -> freshVarOf a >>= recurse . b
  EBind a b | not (isMono a) -> noInstantiationError
  EBind a b -> do
    n <- nextVar
    b' <- recurse (b (Var n))
    return $ EBind a $ \e -> substV n b' e
  EMu a b -> if isMono (EMu a b)
    then return $ EMu a b
    else noInstantiationError
  ECastUp a b | not (isMono a) -> noInstantiationError
  ECastUp a b -> ECastUp a <$> recurse b
  ECastDn a -> ECastDn <$> recurse a
  e -> return e
  where
    noInstantiationError = throwError (NoInstantiation o)
    recurse = findLessThan' o

findLessThan
  :: MonadState InferState m
  => MonadError InferError m
  => Expr -> m Expr
findLessThan = join findLessThan'

findGreaterThan'
  :: MonadState InferState m
  => MonadError InferError m
  => Expr -> Expr -> m Expr
findGreaterThan' o = \case
  EApp e1 e2 | not (isMono e2) -> noInstantiationError
  EApp e1 e2 -> (\e1' -> EApp e1' e2) <$> recurse e1
  EAbs a b | not (isMono a) -> noInstantiationError
  EAbs a b -> do
    n <- nextVar
    b' <- recurse (b (Var n))
    return $ EAbs a $ \e -> substV n b' e
  EPi a b -> do
    a' <- findLessThan' o a
    n <- nextVar
    b' <- recurse (b (Var n))
    return $ EPi a $ \e -> substV n b' e
  EAll a b -> freshExOf a >>= recurse . b
  EBind a b | not (isMono a) -> noInstantiationError
  EBind a b -> do
    n <- nextVar
    b' <- recurse (b (Var n))
    return $ EBind a $ \e -> substV n b' e
  EMu a b -> if isMono (EMu a b)
    then return $ EMu a b
    else noInstantiationError
  ECastUp a b | not (isMono a) -> noInstantiationError
  ECastUp a b -> ECastUp a <$> recurse b
  ECastDn a -> ECastDn <$> recurse a
  e -> return e
  where
    noInstantiationError = throwError (NoInstantiation o)
    recurse = findGreaterThan' o

findGreaterThan
  :: MonadState InferState m
  => MonadError InferError m
  => Expr -> m Expr
findGreaterThan = join findGreaterThan'

generalReduce
  :: MonadState InferState m
  => MonadError InferError m
  => (Expr -> [Work]) -> Expr -> m [Work]
generalReduce k = \case
  EAll a b -> do
    ex <- freshExOf a
    return $ return $ WReduce (b ex) k
  EApp (EAbs a b) e ->
    return $ k (b e)
  EApp f a ->
    return $ return $ WReduce f $ \f' ->
      k (EApp f' a)
  e@(EMu a b) ->
    return $ k (b e)
  e -> throwError $ IrreducibleExpr e

ruleLog :: String -> RuleLog
ruleLog = RuleLog . return

logWorkList
  :: MonadWriter RuleLog m
  => MonadState InferState m
  => m ()
logWorkList = RuleLog . return . showWL <$> getWork >>= tell

wlStep :: MonadState InferState m
       => MonadWriter RuleLog m
       => MonadError InferError m
       => m Expr
wlStep = logWorkList >> popWork >>= \case
  WVar   _ _ -> wlStep
  WExVar _ _ -> wlStep
  WKEx _ -> wlStep
  WDone  e -> return e
  WInfer e1 e2 k -> infer k e1 e2 >>= prependWorks >> wlStep
  WInferApp tf a k -> inferApp k tf a >>= prependWorks >> wlStep
  WCheck e1 e2 a -> check e1 e2 a >>= prependWorks >> wlStep
  WUnifyL n e -> findLessThan e >>= doWorkListSubst n >> wlStep
  WUnifyR e n -> findGreaterThan e >>= doWorkListSubst n >> wlStep
  WUnifyK n k -> modifyWork (substWorkListK n k) >> wlStep
  WReduce e k -> generalReduce k e >>= prependWorks >> wlStep
  WFail e -> throwError e

wlStepImpl :: Inferencer Expr
wlStepImpl = wlStep

type Inferencer a = StateT InferState (ExceptT InferError (Writer RuleLog)) a

runInfer :: Expr -> IO (Either InferError Expr)
runInfer e =
   let (r, RuleLog logs) =
         runWriter $ runExceptT $ evalStateT
         wlStepImpl (InferState 0 [WInfer e e $ \e' -> return $ WDone e'])
   in forM_ logs putStrLn >> return r