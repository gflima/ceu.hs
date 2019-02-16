module Ceu.Parser.Stmt where

import Debug.Trace
import Data.Maybe             (fromJust)

import Text.Parsec.Prim       ((<|>), try, getPosition, many)
import Text.Parsec.Char       (char, anyChar)
import Text.Parsec.String     (Parser)
import Text.Parsec.Combinator (notFollowedBy, many1, chainl, chainl1, chainr1, option, optionMaybe, optional)

import Ceu.Parser.Common
import Ceu.Parser.Token
import Ceu.Parser.Type        (pType, type_F, tk_types)

import Ceu.Grammar.Globals    (Source, ID_Var)
import Ceu.Grammar.Type       (Type(..))
import Ceu.Grammar.Ann        (annz, source, getAnn, Ann(..))
import Ceu.Grammar.Full.Full

-------------------------------------------------------------------------------

pSet :: Bool -> Loc -> Parser Stmt
pSet chk loc = do
  pos  <- pos2src <$> getPosition
  void <- tk_str "<-"
  exp  <- expr
  return $ Set annz{source=pos} chk loc exp

-- (x, (y,_))
pLoc :: Parser Loc
pLoc =  (try lany  <|> try lvar   <|> try lunit  <|> try lnumber <|>
         try lcons <|> try ltuple <|> try lexp) <|>
         try (tk_str "(" *> ((pLoc <* tk_str ")")))
  where
    lany    = do
                void <- tk_str "_"
                return LAny
    lvar    = do
                var <- tk_var
                return $ LVar var
    lunit   = do
                void <- tk_str "("
                void <- tk_str ")"
                return LUnit
    lnumber = do
                num <- tk_num
                return $ LNumber num
    lcons   = do
                cons <- tk_types
                loc  <- option LUnit pLoc
                return $ LCons cons loc
    ltuple  = do
                locs <- list pLoc
                return (LTuple $ locs)
    lexp    = do
                exp <- tk_str "`" *> expr <* tk_str "`"
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
  void <- tk_key "return"
  e  <- expr
  return $ Ret annz{source=pos} e

-------------------------------------------------------------------------------

stmt_class :: Parser Stmt
stmt_class = do
  pos  <- pos2src <$> getPosition
  void <- tk_key "typeclass"
  cls  <- tk_type
  void <- tk_key "for"
  var  <- try tk_var      -- TODO: list of vars
  void <- tk_key "with"
  ifc  <- stmt
  void <- tk_key "end"
  return $ Class annz{source=pos} cls [var] ifc

stmt_inst :: Parser Stmt
stmt_inst = do
  pos  <- pos2src <$> getPosition
  void <- tk_key "instance"
  void <- tk_key "of"
  cls  <- tk_type
  void <- tk_key "for"
  tp   <- try pType       -- TODO: list of types
  void <- tk_key "with"
  imp  <- stmt
  void <- tk_key "end"
  return $ Inst annz{source=pos} cls [tp] imp

stmt_data :: Parser Stmt
stmt_data = do
  pos  <- pos2src <$> getPosition
  void <- tk_key "type"
  id   <- tk_types
  with <- option Type0 (tk_key "with" *> pType)
  return $ Data annz{source=pos} id [] with False

stmt_var :: Parser Stmt
stmt_var = do
  pos  <- pos2src <$> getPosition
  void <- tk_key "var"
  loc  <- pLoc
  void <- tk_str ":"
  tp   <- pType
  s    <- option (Nop $ annz{source=pos})
                 (try $ pSet False loc)
  s'   <- case (matchLocType pos loc tp) of
            Nothing -> do { fail "arity mismatch" }
            Just v  -> return $ Seq annz{source=pos} v s
  return s'

stmt_attr :: Parser Stmt
stmt_attr = do
  --pos  <- pos2src <$> getPosition
  set  <- try (tk_str' "set!") <|> try (tk_str' "set")
  loc  <- pLoc
  s    <- pSet (set=="set!") loc
  return s

-------------------------------------------------------------------------------

stmt_do :: Parser Stmt
stmt_do = do
  pos  <- pos2src <$> getPosition
  void <- tk_key "do"
  s    <- stmt
  void <- tk_key "end"
  return $ Scope annz{source=pos} s

pMatch pos = option (LExp $ Read annz{source=pos} "_true") (try $ pLoc <* tk_str "<-")

stmt_match :: Parser Stmt
stmt_match = do
  pos1 <- pos2src <$> getPosition
  void <- tk_key "if"
  loc  <- pMatch pos1
  exp  <- expr
  void <- tk_key "then"
  s1   <- stmt
  ss   <- many $ (try $ (,,,) <$> pos2src <$> getPosition <*>
                 (tk_key "else/if" *> pMatch pos1) <*> expr <*> (tk_key "then" *> stmt))
  pos2 <- pos2src <$> getPosition
  s2   <- option (Nop annz{source=pos2}) (try $ tk_key "else" *> stmt)
  void <- tk_key "end"
  return $ foldr (\(p,l,e,s) acc -> Match annz{source=p} l e s acc) s2 ([(pos1,loc,exp,s1)] ++ ss)

stmt_loop :: Parser Stmt
stmt_loop = do
  pos1 <- pos2src <$> getPosition
  void <- tk_key "loop"
  void <- tk_key "do"
  s    <- stmt
  --pos2 <- pos2src <$> getPosition
  void <- tk_key "end"
  return $ Loop annz{source=pos1} s

-------------------------------------------------------------------------------

stmt1 :: Parser Stmt
stmt1 = do
  s <- try stmt_class   <|>
       try stmt_inst    <|>
       try stmt_data    <|>
       try stmt_var     <|>
       try stmt_funcs   <|>
       try stmt_attr    <|>
       try stmt_do      <|>
       try stmt_match   <|>
       try stmt_loop    <|>
       try stmt_ret
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
  cons <- tk_types
  pos2 <- pos2src <$> getPosition
  exp  <- option (Unit annz{source=pos2}) expr
  return $ Cons annz{source=pos1} cons exp

expr_read :: Parser Exp
expr_read = do
  pos <- pos2src <$> getPosition
  str <- try tk_var <|> try tk_op
  return $ Read annz{source=pos} str

expr_unit :: Parser Exp
expr_unit = do
  pos  <- pos2src <$> getPosition
  void <- tk_str "("
  void <- tk_str ")"
  return $ Unit annz{source=pos}

expr_parens :: Parser Exp
expr_parens = do
  void <- tk_str "("
  exp  <- expr
  void <- tk_str ")"
  return exp

expr_tuple :: Parser Exp
expr_tuple = do
  pos  <- pos2src <$> getPosition
  exps <- list expr
  return $ Tuple annz{source=pos} exps

expr_prim :: Parser Exp
expr_prim =
  try expr_number   <|>
  try expr_cons     <|>
  try expr_read     <|>
  try expr_unit     <|>
  try expr_parens   <|>
  try expr_tuple    <|>
  try expr_func

-------------------------------------------------------------------------------

expr_infix :: Parser Exp
expr_infix = do
  void <- notFollowedBy tk_op
  e1   <- expr_prim
  pos  <- pos2src <$> getPosition
  op   <- try tk_op <|> try tk_var
  void <- notFollowedBy tk_op
  e2   <- expr_prim
  return $ Call annz{source=pos} (Read annz{source=pos} op) (Tuple (getAnn e1) [e1,e2])

expr_prefix :: Parser Exp
expr_prefix = do
  op   <- expr_prim
  void <- notFollowedBy tk_op
  e    <- expr_prim
  return $ case op of
            (Read _ "-") -> Call (getAnn op) (Read (getAnn op) "negate") e
            otherwise    -> Call (getAnn op) op e

expr_posfix :: Parser Exp
expr_posfix = do
  void <- notFollowedBy tk_op
  e    <- expr_prim
  op   <- expr_prim
  return $ Call (getAnn e) op e

expr :: Parser Exp
expr = try expr_infix <|> try expr_prefix <|> try expr_posfix <|> try expr_prim

-------------------------------------------------------------------------------

func :: Source -> Parser (Type, Stmt)
func pos = do
  loc  <- pLoc
  void <- tk_str ":"
  tp   <- type_F

  dcls <- let (TypeF tp' _) = tp
              dcls = (matchLocType pos loc tp')
          in
            case dcls of
              Nothing  -> do { fail "arity mismatch" }
              Just dcls' -> return dcls'

  void <- tk_key "do"
  imp  <- stmt
  void <- tk_key "end"

  ann  <- do { return annz{source=pos} }

  return $ (tp, Seq ann
                  dcls
                  (Seq ann
                    (Set ann False loc (Arg ann))
                    imp))

expr_func :: Parser Exp
expr_func = do
  pos      <- pos2src <$> getPosition
  void     <- tk_key "func"
  (tp,imp) <- func pos
  return $ Func annz{source=pos} tp imp


stmt_funcs :: Parser Stmt
stmt_funcs = do
  pos    <- pos2src <$> getPosition
  void   <- tk_key "func"
  f      <- try tk_op <|> try tk_var
  tp_imp <- optionMaybe $ try (func pos)
  ann  <- do { return annz{source=pos} }
  ret  <- case tp_imp of
            Nothing -> do
                void <- tk_str ":"
                tp   <- pType
                return $ Var ann f tp
            Just (tp,imp) -> do
                return $ FuncS ann f tp imp
  return ret
