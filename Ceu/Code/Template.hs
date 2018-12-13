import Text.Parsec              (parse)
import Text.Parsec.Error        (ParseError)
import Text.Parsec.Prim         (many, try, (<|>))
import Text.Parsec.Char         (char, string, anyChar)
import Text.Parsec.String       (Parser)
import Text.Parsec.Combinator   (manyTill, eof, lookAhead)

key :: Parser String
key = do
    v    <- manyTill anyChar (char ' ')
    void <- string ">>>"
    return v

pair = (,) <$> (manyTill anyChar
                         (try (() <$ string "<<< ") <|> eof))
           <*> key

go :: String -> Either Text.Parsec.Error.ParseError [(String,String)]
go str = parse (many pair) "" (str ++ "<<<  >>>")

main = do
    src <- readFile "Ceu/Code/ceu.c"
    case go src of
        Left  err -> print err
        Right dst -> writeFile "Ceu/Code/env/_ceu_app.c.h" (concat $ map (\(a,b)->a++b) dst)
    return ()
