module Ceu.Parser.Stmt where

import Debug.Trace
import Data.Bool              (bool)
import Data.Char              (isLower)
import Data.Maybe             (isJust, isNothing, fromJust)
import qualified Data.Set as Set
import Control.Monad          (guard, when)

import Text.Parsec.Prim       ((<|>), (<?>), try, getPosition, many, unexpected)
import Text.Parsec.Char       (char, anyChar)
import Text.Parsec.String     (Parser)
import Text.Parsec.Combinator (notFollowedBy, many1, chainl, chainl1, chainr1, option, optionMaybe, optional)

import Ceu.Parser.Common
import Ceu.Parser.Token
import Ceu.Parser.Type        (pType, type_F)

import Ceu.Grammar.Globals    (Source, ID_Var, ID_Class)
import Ceu.Grammar.Type       (Type(..))
import Ceu.Grammar.Ann        (annz, source, getAnn, Ann(..))
import Ceu.Grammar.Full.Full

-------------------------------------------------------------------------------

pSet :: Bool -> Loc -> Parser Stmt
pSet chk loc = do
  pos  <- pos2src <$> getPosition
  void <- tk_sym "<-"
  exp  <- expr
  return $ Set annz{source=pos} chk loc exp

-- (x, (y,_))
pLoc :: Parser Loc
pLoc = lany  <|> lvar <|> try lunit  <|> lnumber <|>
       lcons <|> lexp <|> try ltuple <|> (tk_sym "(" *> (pLoc <* tk_sym ")"))
       <?> "location"
  where
    lany    = do
                void <- tk_key "_"
                return LAny
    lvar    = do
                var <- tk_var
                return $ LVar var
    lunit   = do
                void <- tk_sym "("
                void <- tk_sym ")"
                return LUnit
    lnumber = do
                num <- tk_num
                return $ LNumber num
    lcons   = do
                cons <- tk_data_hier
                loc  <- option LUnit pLoc
                return $ LCons cons loc
    ltuple  = do
                locs <- list pLoc
                return (LTuple $ locs)
    lexp    = do
                exp <- tk_sym "`" *> expr <* tk_sym "´"
                return $ LExp exp

matchLocType :: Source -> Loc -> Type -> Maybe Stmt
matchLocType src loc tp = case (aux src loc tp) of
                            Nothing -> Nothing
                            Just v  -> Just $ foldr (Seq annz) (Nop annz) v
  where
    aux :: Source -> Loc -> Type -> Maybe [Stmt]
    aux pos LAny        _          = Just []
    aux pos LUnit       Type0      = Just []
    aux pos (LVar var)  tp         = Just [Var annz{source=pos} var tp]
    aux pos (LTuple []) (TypeN []) = Just []
    aux pos (LTuple []) _          = Nothing
    aux pos (LTuple _)  (TypeN []) = Nothing
    aux pos (LTuple (v1:vs1)) (TypeN (v2:vs2)) = (fmap (++) (aux pos v1 v2)) <*>
                                                 (aux pos (LTuple vs1) (TypeN vs2))
    aux pos (LTuple _)  _          = Nothing

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
  return $ let (Number z n) = e in
            Ret annz{source=pos} (Error z n)

-------------------------------------------------------------------------------

pClassFor :: Parser a -> Parser (String,a)
pClassFor p = do
  par  <- optionMaybe $ tk_sym "("
  cls  <- tk_class
  void <- tk_key "for"
  v    <- p             -- TODO: list of ps
  void <- if isJust par then do tk_sym ")" else do { return () }
  return (cls,v)

stmt_class :: Parser Stmt
stmt_class = do
  pos       <- pos2src <$> getPosition
  void      <- try $ tk_key "interface"
  (cls,var) <- pClassFor tk_var
  exts      <- optionMaybe $ (tk_key "extends" *> pClassFor tk_var)
  void      <- tk_key "with"
  ifc       <- stmt
  void      <- tk_key "end"
  return $ let exts' = case exts of
                        Just (sup,var') -> [(sup,[var'])]
                        Nothing         -> []
           in
            (Class annz{source=pos} (cls,[var]) exts' ifc)

stmt_inst :: Parser Stmt
stmt_inst = do
  pos      <- pos2src <$> getPosition
  void     <- try $ tk_key "implementation"
  (cls,tp) <- pClassFor pType
  void     <- tk_key "with"
  imp      <- stmt
  void     <- tk_key "end"
  return $ Inst annz{source=pos} (cls,[tp]) imp

stmt_data :: Parser Stmt
stmt_data = do
  pos  <- pos2src <$> getPosition
  void <- try $ tk_key "data"
  id   <- tk_data_hier
  with <- option Type0 (tk_key "with" *> pType)
  return $ Data annz{source=pos} id [] with False

stmt_var :: Parser Stmt
stmt_var = do
  pos  <- pos2src <$> getPosition
  void <- try $ tk_key "var"
  loc  <- pLoc
  void <- tk_sym ":"
  tp   <- pType
  --guard (isJust $ matchLocType pos loc tp) <?> "arity match"
  when (isNothing $ matchLocType pos loc tp) $ unexpected "arity mismatch"
  s    <- option (Nop $ annz{source=pos})
                 (pSet False loc)
  --s'   <- fromJust $ matchLocType pos loc tp)
            --Nothing -> do { fail "arity mismatch" }
            --Just v  -> return $ Seq annz{source=pos} v s
  return $ Seq annz{source=pos} (fromJust $ matchLocType pos loc tp) s

stmt_attr :: Parser Stmt
stmt_attr = do
  --pos  <- pos2src <$> getPosition
  set  <- (try $ tk_key "set!") <|> (try $ tk_key "set") <?> "set"
  loc  <- pLoc
  s    <- pSet (set=="set!") loc
  return s

stmt_call :: Parser Stmt
stmt_call = do
  pos  <- pos2src <$> getPosition
  set  <- tk_key "call"
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

pMatch pos = option (LExp $ Read annz{source=pos} "_true") (try $ pLoc <* tk_sym "<-")

stmt_match :: Parser Stmt
stmt_match = do
  pos1 <- pos2src <$> getPosition
  void <- try $ tk_key "if"
  loc  <- pMatch pos1
  exp  <- expr
  void <- tk_key "then"
  s1   <- stmt
  ss   <- many $ ((,,,) <$> pos2src <$> getPosition <*>
                 (try (tk_key "else/if") *> pMatch pos1) <*> expr <*> (tk_key "then" *> stmt))
  pos2 <- pos2src <$> getPosition
  s2   <- option (Nop annz{source=pos2}) (try (tk_key "else") *> stmt)
  void <- tk_key "end"
  return $ foldr (\(p,l,e,s) acc -> Match annz{source=p} l e s acc) s2 ([(pos1,loc,exp,s1)] ++ ss)

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
       stmt_attr    <|>
       stmt_call    <|>
       stmt_do      <|>
       stmt_match   <|>
       stmt_loop    <|>
       stmt_ret     <|>
       stmt_error   <?> "statement"
  return s

stmt_seq :: Source -> Parser Stmt
stmt_seq src = option (Nop annz{source=src})
                      (chainr1 stmt1 (do return (\a b->Seq annz{source=src} a b)))

stmt :: Parser Stmt
stmt = do
  pos <- pos2src <$> getPosition
  s   <- stmt_seq pos
  return s

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

expr_number :: Parser Exp
expr_number = do
  pos <- pos2src <$> getPosition
  num <- tk_num
  return $ Number annz{source=pos} num

expr_cons :: Parser Exp
expr_cons = do
  pos1 <- pos2src <$> getPosition
  cons <- tk_data_hier
  pos2 <- pos2src <$> getPosition
  exp  <- option (Unit annz{source=pos2}) expr
  return $ Cons annz{source=pos1} cons exp

expr_read :: Parser Exp
expr_read = do
  pos <- pos2src <$> getPosition
  str <- try tk_var <|> tk_op
  return $ Read annz{source=pos} str

expr_func :: Parser Exp
expr_func = do
  pos      <- pos2src <$> getPosition
  void     <- try $ tk_key "func"
  (tp,imp) <- func pos
  return $ Func annz{source=pos} tp imp

expr_unit :: Parser Exp
expr_unit = do
  pos  <- pos2src <$> getPosition
  void <- tk_sym "("
  void <- tk_sym ")"
  return $ Unit annz{source=pos}

expr_parens :: Parser Exp
expr_parens = do
  void <- tk_sym "("
  exp  <- expr
  void <- tk_sym ")"
  return exp

expr_tuple :: Parser Exp
expr_tuple = do
  pos  <- pos2src <$> getPosition
  exps <- try $ list expr
  return $ Tuple annz{source=pos} exps

expr' :: Parser Exp
expr' =
  expr_number     <|>
  expr_cons       <|>
  expr_read       <|>
  try expr_unit   <|>
  try expr_parens <|>
  expr_tuple      <|>
  expr_func       <?> "expression"

-- 1:   e             e                 1
-- 2:   e1  op        Call op e1        a?  5!
-- 3:   e1  e2        Call e1 e2        -1  +(2,3)  add(2,3)
-- 4:   e1  e2  e3    Call e2 (e1,e3)   1+1  t1 isSupOf t2
expr :: Parser Exp
expr = do
  e1  <- expr'
  e2' <- optionMaybe (try expr')
  case e2' of
    Nothing -> do { return e1 }               -- case 1
    Just e2 -> do                             -- case 2-4
      e3' <- optionMaybe (try expr')
      return $
        case e3' of                           -- case 4
          Just e3 -> Call (getAnn e2) e2 (Tuple (getAnn e1) [e1,e3])
          Nothing -> Call (getAnn f)  f  e    -- case 2-3
                      where
                        (f,e) = bool (neg e1,e2) (e2,e1) (isOp e2)
                        isOp (Read _ (c:op)) = not $ isLower c
                        isOp _               = False
                        neg  (Read z "-")    = Read z "negate"
                        neg  e               = e

-------------------------------------------------------------------------------

func :: Source -> Parser (Type, Stmt)
func pos = do
  loc  <- pLoc
  void <- tk_sym ":"
  tp   <- type_F

  dcls <- let (TypeF tp' _) = tp
              dcls = (matchLocType pos loc tp')
          in
            case dcls of
              Nothing    -> do { fail "arity mismatch" }
              Just dcls' -> return dcls'

  ifc <- optionMaybe ((,) <$> (tk_key "where" *> tk_var) <*> (tk_key "implements" *> tk_class))

  void <- tk_key "do"
  imp  <- stmt
  void <- tk_key "end"

  ann  <- do { return annz{source=pos} }

  return $ (implements tp ifc,
            Seq ann
                dcls
                (Seq ann
                  (Set ann False loc (Arg ann))
                  imp))

implements :: Type -> Maybe (ID_Var,ID_Class) -> Type
implements tp Nothing = tp
implements tp (Just (var,cls)) = aux (var,cls) tp where
  aux :: (ID_Var,ID_Class) -> Type -> Type
  aux (var,cls) (TypeV var' []) | var==var' = TypeV var [cls]
  aux (var,cls) Type0           = Type0
  aux (var,cls) (TypeD hier)    = TypeD hier
  aux (var,cls) (TypeF inp out) = TypeF (aux (var,cls) inp) (aux (var,cls) out)
  aux (var,cls) (TypeN ts)      = TypeN $ map (aux (var,cls)) ts

stmt_funcs :: Parser Stmt
stmt_funcs = do
  pos    <- pos2src <$> getPosition
  void   <- tk_key "func"
  f      <- tk_op <|> tk_var
  tp_imp <- optionMaybe $ func pos
  ann  <- do { return annz{source=pos} }
  ret  <- case tp_imp of
            Nothing -> do
              void <- tk_sym ":"
              tp   <- pType
              return $ Var ann f tp
            Just (tp,imp) -> do
              return $ FuncS ann f tp imp
  return ret
