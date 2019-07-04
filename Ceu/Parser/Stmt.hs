module Ceu.Parser.Stmt where

import Debug.Trace
import Data.Bool              (bool)
import Data.Char              (isLower)
import Data.Maybe             (isJust, isNothing, fromJust)
import qualified Data.Set as Set
import Control.Monad          (guard, when)

import Text.Parsec            (eof, parserZero)
import Text.Parsec.Prim       ((<|>), (<?>), try, getPosition, many, unexpected)
import Text.Parsec.Char       (char, anyChar)
import Text.Parsec.String     (Parser)
import Text.Parsec.Combinator (notFollowedBy, many1, chainl, chainl1, chainr1, option, optionMaybe, optional)

import Ceu.Parser.Common
import Ceu.Parser.Token
import Ceu.Parser.Type          (pTypeContext,pContext)

import Ceu.Grammar.Globals            (Source, ID_Var, ID_Class)
import Ceu.Grammar.Constraints as Cs  (cz,cv,cvc)
import Ceu.Grammar.Type               (Type(..), TypeC)
import Ceu.Grammar.Ann                (annz, source, getAnn, Ann(..))
import Ceu.Grammar.Full.Full

singleton x = [x]

-------------------------------------------------------------------------------

data PPat = BOTH | SET | CHK

-- (x, (y,_))
pPat :: PPat -> Parser Exp  -- True=only vars (no exps)
pPat v = lany  <|> lvar <|> try lunit  <|> lnumber <|>
         lcons <|> lexp <|> try ltuple <|> (tk_sym "(" *> (pPat v <* tk_sym ")"))
          <?> "pattern"
  where
    lany    = do
                pos  <- pos2src <$> getPosition
                void <- tk_key "_"
                return $ EAny annz{source=pos}
    lvar    = do
                void <- case v of
                          BOTH -> tk_sym "="
                          SET  -> tk_sym ""
                          CHK  -> parserZero
                pos  <- pos2src <$> getPosition
                var  <- tk_var
                return $ EVar annz{source=pos} var
    lunit   = do
                pos  <- pos2src <$> getPosition
                void <- tk_sym "("
                void <- tk_sym ")"
                return $ EUnit annz{source=pos}
    lnumber = do
                pos  <- pos2src <$> getPosition
                num <- tk_num
                return $ ECons annz{source=pos} ["Int", show num]
    lcons   = do
                pos  <- pos2src <$> getPosition
                cons <- tk_data_hier
                loc  <- optionMaybe (pPat v)
                return $ case loc of
                          Nothing -> ECons annz{source=pos} cons
                          Just l  -> ECall annz{source=pos} (ECons annz{source=pos} cons) l
    ltuple  = do
                pos  <- pos2src <$> getPosition
                locs <- list2 (pPat v)
                return (ETuple annz{source=pos} $ locs)
    lexp    = do
                void <- case v of
                          BOTH -> tk_sym "~"
                          SET  -> parserZero
                          CHK  -> tk_sym ""
                pos  <- pos2src <$> getPosition
                exp  <- expr
                return $ EExp annz{source=pos} exp

matchLocType1 :: Source -> Exp -> TypeC -> Maybe Stmt
matchLocType1 src loc (tp_,ctrs) = case (aux src loc tp_) of
                                    Nothing -> Nothing
                                    Just v  -> Just $ foldr (Seq annz) (Nop annz) v
  where
    aux :: Source -> Exp -> Type -> Maybe [Stmt]
    aux pos (EAny   _)     _           = Just []
    aux pos (EUnit  _)     TUnit       = Just []
    aux pos (EVar   _ var) tp_         = Just [Var annz{source=pos} var (tp_,ctrs)]
    aux pos (ETuple _ [])  (TTuple []) = Just []
    aux pos (ETuple _ [])  _           = Nothing
    aux pos (ETuple _ _)   (TTuple []) = Nothing
    aux pos (ETuple _ (v1:vs1))
            (TTuple (v2:vs2))          = (fmap (++) (aux pos v1 v2)) <*>
                                          (aux pos (ETuple annz{source=pos} vs1) (TTuple vs2))
    aux pos (ETuple _ _)  _            = Nothing
    aux pos loc         tp_            = error $ show (pos,loc,tp_)

matchLocType2 :: Source -> Exp -> TypeC -> Maybe Stmt
matchLocType2 src loc (tp_,ctrs) = if length vars /= length tps_ then Nothing else
                                    Just $ foldr (Seq annz) (Nop annz) dcls
  where
    tps_ = tp2list (length vars) tp_
    vars = getVars loc

    dcls = map f $ map (\(Just v,t) -> (v,t)) $ filter (\(v,_) -> isJust v) $ zip vars tps_ where
            f (var,tp_) = Var annz{source=src} var (tp_,ctrs)

    getVars :: Exp -> [Maybe ID_Var]
    getVars (EAny   _)               = []
    getVars (EUnit  _)               = []
    getVars (EVar   _ var)           = [Just var]
    getVars (ETuple _ es)            = concatMap getVars es
    getVars (ECons  _ _)             = []
    getVars (ECall  _ (ECons _ _) e) = getVars e

    tp2list :: Int -> Type -> [Type]
    tp2list 1 tp_@(TTuple tps_) = [tp_]
    tp2list _     (TTuple tps_) = tps_
    tp2list _     tp_           = [tp_]

-------------------------------------------------------------------------------

stmt_nop :: Parser Stmt
stmt_nop = do
  pos  <- pos2src <$> getPosition
  return $ Nop annz{source=pos}

stmt_ret :: Parser Stmt
stmt_ret = do
  pos  <- pos2src <$> getPosition
  void <- try $ tk_key "return"
  e  <- expr
  return $ Ret annz{source=pos} e

stmt_error :: Parser Stmt
stmt_error = do
  pos  <- pos2src <$> getPosition
  void <- try $ tk_key "error"
  e    <- expr_number
  return $ let (ECons z ["Int",n]) = e in
            Ret annz{source=pos} (EError z $ read n)

-------------------------------------------------------------------------------

stmt_class :: Parser Stmt
stmt_class = do
  pos  <- pos2src <$> getPosition
  void <- try $ tk_key "constraint"
  par  <- optionMaybe $ try $ tk_sym "("
  cls  <- tk_class
  void <- tk_key "for"
  var  <- tk_var
  void <- if isJust par then do tk_sym ")" else do { return () }
  ctx  <- option [] $ try pContext
  void <- tk_key "with"
  ifc  <- stmt
  void <- tk_key "end"
  return $ let ctrs = case ctx of
                        []                       -> cv var
                        [(var',sup)] | var==var' -> cvc (var,sup)
                                     | otherwise -> error "TODO: multiple variables"
                        otherwise                -> error "TODO: multiple constraints"
            in
              Class annz{source=pos} cls ctrs ifc where

stmt_inst :: Parser Stmt
stmt_inst = do
  pos  <- pos2src <$> getPosition
  void <- try $ tk_key "instance"
  void <- tk_key "of"
  par  <- optionMaybe $ try $ tk_sym "("
  cls  <- tk_class
  void <- tk_key "for"
  tp   <- pTypeContext
  void <- if isJust par then do tk_sym ")" else do { return () }
  void <- tk_key "with"
  imp  <- stmt
  void <- tk_key "end"
  return $ Inst annz{source=pos} cls tp imp

stmt_data :: Parser Stmt
stmt_data = do
  pos     <- pos2src <$> getPosition
  void    <- try $ tk_key "data"
  id      <- tk_data_hier
  ofs     <- option [] $ try $ tk_key "for" *> (map TAny <$> (try (list1 tk_var) <|> (singleton <$> tk_var)))
  (st,cs) <- option (TUnit,cz) $ try $ tk_key "with" *> pTypeContext
  return $ Data annz{source=pos} (TData id ofs st, cs) False

pMatch :: Source -> Bool -> Exp -> Parser Stmt
pMatch pos chk loc = do
  --pos  <- pos2src <$> getPosition
  void <- tk_sym "="
  exp  <- expr
  return $ Set annz{source=pos} chk loc exp

stmt_var :: Parser Stmt
stmt_var = do
  pos  <- pos2src <$> getPosition
  var  <- (try $ tk_key "var!") <|> (try $ tk_key "var") <?> "var"
  loc  <- pPat SET
  void <- tk_sym ":"
  tp   <- pTypeContext
  --guard (isJust $ matchLocType pos loc tp) <?> "arity match"
  when (isNothing $ matchLocType2 pos loc tp) $ unexpected "arity mismatch"
  s    <- option (Nop $ annz{source=pos}) $
                 try $ pMatch pos (var=="var!") loc
  --s'   <- fromJust $ matchLocType2 pos loc tp)
            --Nothing -> do { fail "arity mismatch" }
            --Just v  -> return $ Seq annz{source=pos} v s
  return $ Seq annz{source=pos} (fromJust $ matchLocType2 pos loc tp) s

stmt_set :: Parser Stmt
stmt_set = do
  pos  <- pos2src <$> getPosition
  set  <- (try $ tk_key "set!") <|> (try $ tk_key "set") <?> "set"
  loc  <- pPat SET
  void <- tk_sym "="
  exp  <- expr
  return $ Set annz{source=pos} (set=="set!") loc exp

stmt_match :: Parser Stmt
stmt_match = do
  pos  <- pos2src <$> getPosition
  set  <- (try $ tk_key "match!") <|> (try $ tk_key "match") <?> "match"
  exp  <- expr
  void <- tk_sym "with"
  loc  <- pPat BOTH
  return $ Set annz{source=pos} (set=="match!") loc exp

pCase :: Parser (Exp, Stmt)
pCase = do
  void <- try $ tk_sym "case"
  patt <- pPat BOTH
  void <- tk_sym "then"
  s    <- stmt
  return $ (patt, s)

stmt_cases :: Parser Stmt
stmt_cases = do
  pos1  <- pos2src <$> getPosition
  set   <- (try $ tk_key "match!") <|> (try $ tk_key "match") <?> "match"
  exp   <- expr
  void  <- tk_sym "with"
  cases <- many1 pCase
  pos2  <- pos2src <$> getPosition
  celse <- option (Nop annz{source=pos2}) $ try $ tk_key "else" *> stmt
  void  <- tk_key "end"
  return $ Match annz{source=pos1} exp (cases ++ [(EAny annz{source=pos2}, celse)])

stmt_call :: Parser Stmt
stmt_call = do
  pos  <- pos2src <$> getPosition
  set  <- try $ tk_key "call"
  e    <- expr
  return $ CallS annz{source=pos} e

-------------------------------------------------------------------------------

stmt_do :: Parser Stmt
stmt_do = do
  pos  <- pos2src <$> getPosition
  void <- try $ tk_key "do"
  s    <- stmt
  void <- tk_key "end"
  return $ Scope annz{source=pos} s

stmt_if :: Parser Stmt
stmt_if = do
  pos1 <- pos2src <$> getPosition
  void <- try $ tk_key "if"
  exp  <- expr
  void <- tk_key "then"
  s1   <- stmt
  ss   <- many $ ((,,) <$> pos2src <$> getPosition <*>
                 (try (tk_key "else/if") *> expr) <*> (tk_key "then" *> stmt))
  pos2 <- pos2src <$> getPosition
  s2   <- option (Nop annz{source=pos2}) $ try $ tk_key "else" *> stmt
  void <- tk_key "end"
  return $ foldr (\(p,e,s) acc -> If annz{source=p} e s acc) s2 ([(pos1,exp,s1)] ++ ss)

stmt_loop :: Parser Stmt
stmt_loop = do
  pos1 <- pos2src <$> getPosition
  void <- try $ tk_key "loop"
  void <- tk_key "do"
  s    <- stmt
  --pos2 <- pos2src <$> getPosition
  void <- tk_key "end"
  return $ Loop annz{source=pos1} s

-------------------------------------------------------------------------------

stmt1 :: Parser Stmt
stmt1 = do
  s <- stmt_class   <|>
       stmt_inst    <|>
       stmt_data    <|>
       stmt_var     <|>
       stmt_funcs   <|>
       stmt_set     <|>
       try stmt_match   <|>
       stmt_cases   <|>
       stmt_call    <|>
       stmt_do      <|>
       stmt_if      <|>
       stmt_loop    <|>
       stmt_ret     <|>
       stmt_error   <?> "statement"
  return s

stmt_seq :: Source -> Parser Stmt
stmt_seq src = option (Nop annz{source=src}) $
                      try $ chainr1 stmt1 (do return (\a b->Seq annz{source=src} a b))

stmt :: Parser Stmt
stmt = do
  pos <- pos2src <$> getPosition
  s   <- stmt_seq pos
  return s

prog :: Parser Stmt
prog = do
  void <- tk_spc
  s    <- stmt
  void <- eof
  return s

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

expr_number :: Parser Exp
expr_number = do
  pos <- pos2src <$> getPosition
  num <- tk_num
  return $ ECons annz{source=pos} ["Int", show num]

expr_cons :: Parser Exp
expr_cons = do
  pos  <- pos2src <$> getPosition
  cons <- tk_data_hier
  return $ ECons annz{source=pos} cons

expr_read :: Parser Exp
expr_read = do
  pos <- pos2src <$> getPosition
  str <- try tk_var <|> tk_op
  return $ EVar annz{source=pos} str

expr_func :: Parser Exp
expr_func = do
  pos      <- pos2src <$> getPosition
  void     <- try $ tk_key "func"
  (tp,imp) <- func pos
  return $ EFunc annz{source=pos} tp imp

expr_unit :: Parser Exp
expr_unit = do
  pos  <- pos2src <$> getPosition
  void <- tk_sym "("
  void <- tk_sym ")"
  return $ EUnit annz{source=pos}

expr_parens :: Parser Exp
expr_parens = do
  void <- tk_sym "("
  exp  <- expr
  void <- tk_sym ")"
  return exp

expr_tuple :: Parser Exp
expr_tuple = do
  pos  <- pos2src <$> getPosition
  exps <- try $ list2 expr
  return $ ETuple annz{source=pos} exps

expr' :: Parser Exp
expr' =
  expr_number     <|>
  expr_cons       <|>
  expr_read       <|>
  try expr_unit   <|>
  try expr_parens <|>
  expr_tuple      <|>
  expr_func       <?> "expression"

-- 0:   e1            matches           e2
-- 1:   e             e                 1
-- 2:   e1  op        ECall op e1       a?  5!
-- 3:   e1  e2        ECall e1 e2       -1  +(2,3)  add(2,3)
-- 4:   e1  e2  e3    ECall e2 (e1,e3)  1+1  t1 isSupOf t2
expr :: Parser Exp
expr = do
  e1  <- expr'
  m   <- optionMaybe $ try (tk_sym "matches") *> (pos2src <$> getPosition)
  case m of
    Just pos -> do
      e2 <- pPat CHK
      return $ EMatch annz{source=pos} e1 e2
    Nothing  -> do
      e2' <- optionMaybe $ try expr'
      case e2' of
        Nothing -> do { return e1 }               -- case 1
        Just e2 -> do                             -- case 2-4
          e3' <- optionMaybe $ try expr'
          return $
            case e3' of                           -- case 4
              Just e3 -> ECall (getAnn e2) e2 (ETuple (getAnn e1) [e1,e3])
              Nothing -> ECall (getAnn f)  f  e    -- case 2-3
                          where
                            (f,e) = bool (neg e1,e2) (e2,e1) (isOp e2)
                            isOp (EVar _ (c:op)) = not $ isLower c
                            isOp _               = False
                            neg  (EVar z "-")    = EVar z "negate"
                            neg  e               = e

-------------------------------------------------------------------------------

func :: Source -> Parser (TypeC, Stmt)
func pos = do
  loc  <- pPat SET
  void <- tk_sym ":"
  tp   <- pTypeContext

  dcls <- let (TFunc tp' _,ctrs) = tp
              dcls = (matchLocType1 pos loc (tp',ctrs))
          in
            case dcls of
              Nothing    -> do { fail "arity mismatch" }
              Just dcls' -> return dcls'

  void <- tk_key "do"
  imp  <- stmt
  void <- tk_key "end"

  ann  <- do { return annz{source=pos} }

  return $ (tp,
            Seq ann
                dcls
                (Seq ann
                  (Set ann False loc (EArg ann))
                  imp))

stmt_funcs :: Parser Stmt
stmt_funcs = do
  pos    <- pos2src <$> getPosition
  void   <- tk_key "func"
  f      <- tk_op <|> tk_var
  tp_imp <- optionMaybe $ try $ func pos
  ann  <- do { return annz{source=pos} }
  ret  <- case tp_imp of
            Nothing -> do
              void <- tk_sym ":"
              tp   <- pTypeContext
              return $ Var ann f tp
            Just (tp,imp) -> do
              return $ FuncS ann f tp imp
  return ret
