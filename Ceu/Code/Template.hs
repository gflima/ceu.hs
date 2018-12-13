import Text.Parsec              (parse)
import Text.Parsec.Error        (ParseError)
import Text.Parsec.Prim         (many, try, (<|>))
import Text.Parsec.Char         (char, string, anyChar)
import Text.Parsec.String       (Parser)
import Text.Parsec.Combinator   (manyTill, eof, lookAhead)

_key :: Parser String
_key = do
    key  <- manyTill anyChar (char ' ')
    void <- string ">>>"
    return key

_pair = (,) <$> (manyTill anyChar
                          (try (() <$ string "<<< ") <|> eof))
            <*> _key

split :: String -> Either String [(String,String)]
split str = case parse (many _pair) "" (str ++ "<<<  >>>") of
    Left  err   -> Left (show err)              -- NOTE-1: last key whole is empty
    Right pairs -> Right pairs

render :: [(String,String)] -> String -> Either String String
render keyvals src =
    let pairs = (split src) in
        case pairs of
            Left  err    -> Left err
            Right pairs' -> Right $ aux keyvals pairs'
    where
        aux :: [(String,String)] -> [(String,String)] -> String
        aux [] [(txt,_)] = txt                  -- NOTE-1: last key whole is empty
        aux ((key,val):l1) ((txt,key'):l2)
            | key==key' = txt ++ val ++ (aux l1 l2)

main = do
    src     <- return "aaa <<< k1 >>> bbb <<< k2 >>><<< k3 >>> ccc"
    keyvals <- return [("k1","K1"), ("k2","K2"), ("k3","K3")]
    print $ render keyvals src
        --Left  err -> print err
        --Right dst -> writeFile "Ceu/Code/env/_ceu_app.c.h" (concat $ map (\(a,b)->a++b) dst)
    return ()
