module Ceu.Parser.Stmt where

import Debug.Trace
import Data.Maybe                (fromJust)
import Control.Monad             (guard)

import Text.Parsec.Prim          ((<|>), try, getPosition, many)
import Text.Parsec.Char          (char, anyChar)
import Text.Parsec.String        (Parser)
import Text.Parsec.Combinator    (many1, chainl, chainl1, chainr1, option, optionMaybe, optional)

import Ceu.Parser.Common
import Ceu.Parser.Token
import Ceu.Parser.Type           (pType, type_F)

import Ceu.Grammar.Globals       (Source, Loc(..), ID_Var)
import Ceu.Grammar.Type          (Type(..))
import Ceu.Grammar.Ann           (annz, source, getAnn, Ann(..))
import Ceu.Grammar.Full.Full

-------------------------------------------------------------------------------

attr_exp :: Loc -> Parser a -> Parser Stmt
attr_exp loc op = do
    pos  <- pos2src <$> getPosition
    void <- op
    exp  <- expr
    return $ Write annz{source=pos} loc exp

-------------------------------------------------------------------------------

stmt_nop :: Parser Stmt
stmt_nop = do
    pos  <- pos2src <$> getPosition
    return $ Nop annz{source=pos}

stmt_ret :: Parser Stmt
stmt_ret = do
    pos  <- pos2src <$> getPosition
    void <- tk_key "return"
    e    <- expr
    return $ Ret annz{source=pos} e

-------------------------------------------------------------------------------

stmt_var :: Parser Stmt
stmt_var = do
    pos  <- pos2src <$> getPosition
    void <- tk_key "var"
    loc  <- loc_
    void <- tk_str ":"
    tp   <- pType
    s    <- option (Nop $ annz{source=pos})
                   (try (attr_exp loc (tk_str "<-")))
    s'   <- case (dcls pos loc tp) of
                Nothing -> do { fail "arity mismatch" }
                Just v  -> return $ Seq annz{source=pos} v s
    return s'

stmt_attr :: Parser Stmt
stmt_attr = do
    --pos  <- pos2src <$> getPosition
    void <- tk_str "set"
    loc  <- loc_
    s    <- try (attr_exp      loc (tk_str "<-"))
    return $ s

-- (x, (y,_))
loc_ :: Parser Loc
loc_ =  (try lany <|> try lvar <|> try ltuple)
    where
        lany   = do
                    void <- tk_str "_"
                    return LAny
        lvar   = do
                    var <- tk_var
                    return $ LVar var
        ltuple = do
                    locs <- list loc_
                    return (LTuple $ locs)

dcls :: Source -> Loc -> Type -> Maybe Stmt
dcls src loc tp = case (aux src loc tp) of
                        Nothing -> Nothing
                        Just v  -> Just $ foldr (Seq annz) (Nop annz) v
    where
        aux :: Source -> Loc -> Type -> Maybe [Stmt]
        aux pos LAny              _                = Just []
        aux pos (LVar var)        tp               = Just [Var annz{source=pos} var tp]
        aux pos (LTuple [])       (TypeN [])       = Just []
        aux pos (LTuple [])       _                = Nothing
        aux pos (LTuple _)        (TypeN [])       = Nothing
        aux pos (LTuple (v1:vs1)) (TypeN (v2:vs2)) = (fmap (++) (aux pos v1 v2)) <*>
                                                     (aux pos (LTuple vs1) (TypeN vs2))
        aux pos (LTuple _)        _                = Nothing

-------------------------------------------------------------------------------

stmt_do :: Parser Stmt
stmt_do = do
    pos  <- pos2src <$> getPosition
    void <- tk_key "do"
    s    <- stmt
    void <- tk_key "end"
    return $ Scope annz{source=pos} s

stmt_if :: Parser Stmt
stmt_if = do
    pos1 <- pos2src <$> getPosition
    void <- tk_key "if"
    cnd  <- expr
    void <- tk_key "then"
    s1   <- stmt
    ss   <- many $ (try $ (,,) <$> pos2src <$> getPosition <*> (tk_key "else/if" *> expr) <*> (tk_key "then" *> stmt))
    pos2 <- pos2src <$> getPosition
    s2   <- option (Nop annz{source=pos2}) (try $ tk_key "else" *> stmt)
    void <- tk_key "end"
    return $ foldr (\(p,c,s) acc -> If annz{source=p} c s acc) s2 ([(pos1,cnd,s1)] ++ ss)

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
    s <- try stmt_var <|> try stmt_attr <|> try stmt_do <|>
         try stmt_if  <|> try stmt_loop <|> try stmt_ret
    return s

stmt_seq :: Source -> Parser Stmt
stmt_seq src = option (Nop annz{source=src}) (chainr1 stmt1 (do return (\a b->Seq annz{source=src} a b)))

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

expr_read :: Parser Exp
expr_read = do
    pos <- pos2src <$> getPosition
    str <- tk_var
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
expr_prim = try expr_call_pre   <|>
            try expr_number     <|>
            try expr_read       <|>
            try expr_unit       <|>
            try expr_parens     <|>
            try expr_tuple      <|>
            try expr_func

-------------------------------------------------------------------------------

expr_func :: Parser Exp
expr_func = do
  pos  <- pos2src <$> getPosition
  void <- tk_key "func"
  loc  <- try loc_'
  void <- tk_str ":"
  tp   <- type_F
  imp  <- do
            void <- tk_key "do"
            s    <- stmt
            void <- tk_key "end"
            return s

  dcls' <- let (TypeF tp' _) = tp
               dcls' = (dcls pos loc tp') in
            case dcls' of
              Nothing -> do { fail "arity mismatch" }
              Just v' -> return $ Just v'

  ann   <- do { return annz{source=pos} }

  return $ Func ann tp
            (Seq ann
              (fromJust dcls')
              (Seq ann
                (Write ann loc (Arg ann))
                imp))

  where
    --loc_' :: Parser Loc
    loc_' = do
      void <- tk_str ":"
      loc  <- loc_
      return loc

-------------------------------------------------------------------------------

expr_call_pre :: Parser Exp
expr_call_pre = do
    pos  <- pos2src <$> getPosition
    f    <- try (char '\'' *> tk_op)                  <|>
            do { try (tk_str "-") ; return "negate" } <|> -- unary minus exception
            try tk_func
    exp  <- expr
    return $ Call annz{source=pos} (Read annz{source=pos} f) exp

expr_call_pos :: Parser Exp
expr_call_pos = do
    pos <- pos2src <$> getPosition
    e1  <- expr_call_mid
    ops <- many (try tk_op <|> try (char '\'' *> tk_func))
    return $ foldl (\e op -> Call annz{source=pos} (Read annz{source=pos} op) e)
                   e1 ops

expr_call_mid :: Parser Exp
expr_call_mid = expr_prim `chainl1` f where
    f = do
        pos <- pos2src <$> getPosition
        op  <- try tk_op <|> try (char '\'' *> (tk_func <* char '\''))
        return (\a b -> Call annz{source=pos} (Read annz{source=pos} op)
                                              (Tuple annz{source=pos} [a,b]))

-------------------------------------------------------------------------------

expr :: Parser Exp
expr = do
    e <- expr_call_pos
    return e
