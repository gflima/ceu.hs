module Ceu.Parser.Exp where

import Text.Parsec.Prim         ((<|>), getPosition, try, many)
import Text.Parsec.String       (Parser)
import Text.Parsec.Char         (char, anyChar)
import Text.Parsec.Combinator   (chainl1, option, notFollowedBy)

import Ceu.Parser.Common
import Ceu.Parser.Token         (tk_num, tk_var, tk_func, tk_str, tk_op, s)

import Ceu.Grammar.Ann          (annz, source)
import Ceu.Grammar.Basic        (Exp(..))

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
            try expr_tuple

-------------------------------------------------------------------------------

{-
expr_func :: Parser Exp
expr_func = do
    pos  <- pos2src <$> getPosition
    void <- tk_key "func"
    func <- tk_func
    loc  <- optionMaybe (try loc_')
    void <- tk_str ":"
    tp   <- type_F
    imp  <- optionMaybe $ do
                void <- tk_key "do"
                s    <- stmt
                void <- tk_key "end"
                return s

    dcls' <- case loc of
                Nothing -> return Nothing
                Just v  -> let (TypeF tp' _) = tp
                               dcls' = (dcls pos v tp') in
                            case dcls' of
                                Nothing -> do { fail "arity mismatch" }
                                Just v'  -> return $ Just v'
    ann   <- do { return annz{source=pos} }
    ret   <- do { return $ Func ann func tp }

    s     <- case imp of
                Nothing   -> return $ ret
                Just imp' ->
                    case loc of
                        Nothing   -> do { fail "missing arguments" }
                        Just loc' -> return $
                            (Seq ann
                                ret
                                (FuncI ann func tp
                                    (Seq ann
                                        (fromJust dcls')
                                        (Seq ann
                                            (Write ann loc' (RawE ann{type_=TypeT} [RawAtS "{_ceu_arg}"]))
                                            imp'))))
    return s

    where
        loc_' :: Parser Loc
        loc_' = do
            void <- tk_str ":"
            loc  <- loc_
            return loc
-}

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
