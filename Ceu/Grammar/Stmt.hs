{-# LANGUAGE CPP #-}

module Ceu.Grammar.Stmt where

import Ceu.Grammar.Globals
import Ceu.Grammar.Exp
import Text.Printf

-- Program (pg 5).
data Stmt' a
  = Var ID_Var a                -- variable declaration
  | Int ID_Int a                -- event declaration
  | Write ID_Var Exp            -- assignment statement
  | AwaitExt ID_Ext             -- await external event
  | EmitExt ID_Ext (Maybe Exp)  -- emit external event
  | AwaitInt ID_Int             -- await internal event
  | EmitInt ID_Int              -- emit internal event
  | If Exp a a                  -- conditional
  | Seq a a                     -- sequence
  | Loop a                      -- infinite loop
  | Every ID_Evt a              -- event iteration
  | Par a a                     -- par statement
  | Pause ID_Var a              -- pause/suspend statement
  | Fin a                       -- finalization statement
  | Trap a                      -- enclose escape
  | Escape Int                  -- escape N traps
  | Nop                         -- dummy statement (internal)
  | Error String                -- generate runtime error (for testing)
  deriving (Eq, Show)

infixr 1 `Seq`                  -- `Seq` associates to the right
infixr 0 `Par`                  -- `Par` associates to the right

-------------------------------------------------------------------------------

#ifndef SOURCE

newtype Stmt = Stmt (Stmt' Stmt)
  deriving (Eq, Show)

newStmt :: Stmt' Stmt -> Stmt
newStmt exp = Stmt exp

getStmt' :: Stmt -> Stmt' Stmt
getStmt' (Stmt e) = e

getSource :: Stmt -> (Maybe Source)
getSource _ = Nothing

#else

newtype Stmt = Stmt (Stmt' Stmt, Source)
  deriving (Eq, Show)

newStmt :: Stmt' Stmt -> Stmt
newStmt exp = Stmt (exp, ("",0,0))

getStmt' :: Stmt -> Stmt' Stmt
getStmt' (Stmt (e,_)) = e

getSource :: Stmt -> (Maybe Source)
getSource (Stmt (_,s)) = Just s

#endif

-------------------------------------------------------------------------------

-- Shows program.
showProg :: Stmt -> String
showProg stmt = case getStmt' stmt of
  Var id p             -> printf "{%s: %s}" id (sP p)
  Int id p             -> printf "{%s: %s}" id (sP p)
  Write id expr        -> printf "%s=%s" id (sE expr)
  AwaitExt ext         -> printf "?%s" ext
  EmitExt ext Nothing  -> printf "!%s" ext
  EmitExt ext (Just v) -> printf "!%s=%s" ext (sE v)
  AwaitInt int         -> printf "?%s" int
  EmitInt int          -> printf "!%s" int
  If expr p q          -> printf "(if %s then %s else %s)"
                            (sE expr) (sP p) (sP q)
  Seq p q              -> printf "%s; %s" (sP p) (sP q)
  Loop p               -> printf "(loop %s)" (sP p)
  Every evt p          -> printf "(every %s %s)" evt (sP p)
  Par p q              -> printf "(%s || %s)" (sP p) (sP q)
  Pause var p          -> printf "(pause %s %s)" var (sP p)
  Fin p                -> printf "(fin %s)" (sP p)
  Trap p               -> printf "(trap %s)" (sP p)
  Escape n             -> printf "(escape %d)" n
  Nop                  -> "nop"
  Error _              -> "err"
  where
    sE = showExp
    sP = showProg

stmt2word :: Stmt -> String
stmt2word stmt = case getStmt' stmt of
  Var _ _     -> "declaration"
  Int _ _     -> "declaration"
  Write _ _   -> "assignment"
  AwaitExt _  -> "await"
  EmitExt _ _ -> "emit"
  AwaitInt _  -> "await"
  EmitInt _   -> "emit"
  If _ _ _    -> "if"
  Seq _ _     -> "sequence"
  Loop _      -> "loop"
  Every _ _   -> "every"
  Par _ _     -> "parallel"
  Pause _ _   -> "pause/if"
  Fin _       -> "finalize"
  Trap _      -> "trap"
  Escape _    -> "escape"
  Nop         -> "nop"
  Error _     -> "error"

err_stmt_msg :: Stmt -> String -> String
err_stmt_msg stmt msg = (stmt2word stmt) ++ ": " ++ msg

errs_stmts_msg_map :: [Stmt] -> String -> Errors
errs_stmts_msg_map stmts msg = map (\s -> (stmt2word s) ++ ": " ++ msg) stmts
