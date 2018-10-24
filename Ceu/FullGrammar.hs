module Ceu.FullGrammar where

import Ceu.Globals
import qualified Ceu.Grammar as G
import qualified Ceu.Eval as E
--import Debug.Trace

-- Events:
-- -1: program can never await (used for boot reaction)
-- -2: system can never emit (used as "await FOREVER" input)
-- -3: program can never await (used as "async" input)
--inputBoot    :: ID_Evt
--inputForever :: ID_Evt
inputAsync   :: ID_Evt
--inputBoot    = -1
--inputForever = -2
inputAsync   = -3

-- Program (pg 5).
data Stmt
  = Var ID_Var Stmt             -- variable declaration
  | Write ID_Var Expr           -- assignment statement
  | AwaitExt ID_Evt             -- await external event
  | AwaitFor                    -- await forever
-- TODO: AwaitTmr
  | AwaitInt ID_Evt             -- await internal event
  | EmitInt ID_Evt              -- emit internal event
  | Break                       -- loop escape
  | If Expr Stmt Stmt           -- conditional
  | Seq Stmt Stmt               -- sequence
  | Loop Stmt                   -- infinite loop
  | Every ID_Evt Stmt           -- event iteration
  | And Stmt Stmt               -- par/and statement
  | Or Stmt Stmt                -- par/or statement
  | Spawn Stmt                  -- spawn statement
  | Fin (Maybe ID_Var) Stmt     -- finalize statement
  | Async Stmt                  -- async statement
  | Error String                -- generate runtime error (for testing purposes)
  | Fin' Stmt                   -- fin as in basic Grammar
  | Nop'                        -- nop as in basic Grammar
  deriving (Eq, Show)

--TODO: fazer um exemplo que o fin executa 2x por causa de um emit que mata um paror por fora.
--TODO: adicionar um @error Int nas duas semanticas

infixr 1 `Seq`                  -- `Seq` associates to the right
infixr 0 `Or`                   -- `Or` associates to the right
infixr 0 `And`                  -- `And` associates to the right

-- remFin: Converts (Fin _  p);A -> (or (Fin' p) A)
--                  (Fin id p);A -> A ||| (Var (Or [(Fin p)] X)

remFin :: Stmt -> Stmt
remFin p = p' where
  (_,p') = rF p

  rF :: Stmt -> ([(ID_Var,Stmt)], Stmt)
  rF (If exp p1 p2)      = ([], If exp (snd (rF p1)) (snd (rF p2)))

  rF (Seq (Fin Nothing p1) p2)   = (l2', Or (Fin' p1) p2')
                                     where (l2',p2') = (rF p2)
  rF (Seq (Fin (Just id) p1) p2) = (l2'++[(id,p1)], p2')        -- invert l2/l1
                                     where (l2',p2') = (rF p2)
  rF (Seq p1 p2)                 = (l2'++l1', Seq p1' p2')
                                     where (l1',p1') = (rF p1)
                                           (l2',p2') = (rF p2)

  rF (Loop p)            = ([], Loop (snd (rF p)))
  rF (Every e p)         = ([], Every e (snd (rF p)))
  rF (And p1 p2)         = ([], And (snd (rF p1)) (snd (rF p2)))
  rF (Or p1 p2)          = ([], Or (snd (rF p1)) (snd (rF p2)))
  rF (Spawn p)           = ([], Spawn (snd (rF p)))
  rF (Fin id p)          = error "remFin: unexpected statement (Fin)"
  rF (Async p)           = ([], Async (snd (rF p)))

  rF (Var id p)          = (l'', Var id p''') where
                            (l', p')  = (rF p)   -- results from nested p
                            (p'',l'') = f id l' -- matches l' with current local id
                            p''' | ((toSeq p'') == Nop') = p' -- nothing to finalize
                                 | otherwise             = (Or (Fin' (toSeq p'')) p')

                            -- recs: Var in Var, [pending finalize] (id->stmts)
                            -- rets: [stmts to fin] in block, [remaining finalize]
                            f :: ID_Var -> [(ID_Var,Stmt)] -> ([Stmt], [(ID_Var,Stmt)])
                            f _ [] = ([], [])
                            f id1 ((id2,stmt):fs) = (a++a', b++b') where
                              (a',b') = f id1 fs
                              (a, b ) | (id2==id1) = ([stmt], [])
                                      | otherwise  = ([], [(id2,stmt)])

                            toSeq :: [Stmt] -> Stmt
                            toSeq []     = Nop'
                            toSeq (s:ss) = Seq s (toSeq ss)

  rF p                   = ([], p)

-- remSpawn: Converts (spawn p1; ...) into (p1;AwaitFor or ...)

remSpawn :: Stmt -> Stmt
remSpawn (Var var p)         = Var var (remSpawn p)
remSpawn (If exp p1 p2)      = If exp (remSpawn p1) (remSpawn p2)
remSpawn (Seq (Spawn p1) p2) = Or (Seq (remSpawn p1) AwaitFor) (remSpawn p2)
remSpawn (Seq p1 p2)         = Seq (remSpawn p1) (remSpawn p2)
remSpawn (Loop p)            = Loop (remSpawn p)
remSpawn (Every e p)         = Every e (remSpawn p)
remSpawn (And p1 p2)         = And (remSpawn p1) (remSpawn p2)
remSpawn (Or p1 p2)          = Or (remSpawn p1) (remSpawn p2)
remSpawn (Spawn p)           = error "remSpawn: unexpected statement (Spawn)"
remSpawn (Fin id p)          = Fin id (remSpawn p)
remSpawn (Async p)           = Async (remSpawn p)
remSpawn (Fin' p)            = Fin' (remSpawn p)
remSpawn p                   = p

-- chkSpawn: `Spawn` can only appear as first item in `Seq`

chkSpawn :: Stmt -> Stmt
chkSpawn p = case p of
  (Spawn _) -> error "chkSpawn: unexpected statement (Spawn)"
  _ | (chkS p) -> p
    | otherwise -> error "chkSpawn: unexpected statement (Spawn)"
  where

  notS (Spawn _) = False
  notS p         = True

  chkS :: Stmt -> Bool
  chkS (Var _ p)    = (notS p) && (chkS p)
  chkS (If _ p1 p2) = (notS p1) && (notS p2) && (chkS p1) && (chkS p2)
  chkS (Seq p1 p2)  = (chkS p1) && (notS p2) && (chkS p2)
  chkS (Loop p)     = (notS p) && (chkS p)
  chkS (Every _ p)  = (notS p) && (chkS p)
  chkS (And p1 p2)  = (notS p1) && (notS p2) && (chkS p1) && (chkS p2)
  chkS (Or p1 p2)   = (notS p1) && (notS p2) && (chkS p1) && (chkS p2)
  chkS (Spawn p)    = (notS p) && (chkS p)
  chkS (Fin _ p)    = (notS p) && (chkS p)
  chkS (Async p)    = (notS p) && (chkS p)
  chkS (Fin' p)     = (notS p) && (chkS p)
  chkS _            = True

-- remSpawn: Adds AwaitFor in Loops inside Asyncs

remAsync :: Stmt -> Stmt
remAsync p = (rA False p) where
  rA :: Bool -> Stmt -> Stmt
  rA inA   (Var var p)    = Var var (rA inA p)
  rA inA   (If exp p1 p2) = If exp (rA inA p1) (rA inA p2)
  rA inA   (Seq p1 p2)    = Seq (rA inA p1) (rA inA p2)
  rA True  (Loop p)       = Loop (rA True (Seq p (AwaitExt inputAsync)))
  rA False (Loop p)       = Loop (rA False p)
  rA inA   (Every e p)    = Every e (rA inA p)
  rA inA   (And p1 p2)    = And (rA inA p1) (rA inA p2)
  rA inA   (Or p1 p2)     = Or (rA inA p1) (rA inA p2)
  rA inA   (Spawn p)      = Spawn (rA inA p)
  rA inA   (Fin id p)     = Fin id (rA inA p)
  rA inA   (Async p)      = (rA True p)
  rA inA   (Fin' p)       = Fin' (rA inA p)
  rA inA   p              = p

-- TODO: chkSpan: no sync statements

-- remAwaitFor: Converts AwaitFor into (AwaitExt inputForever)

remAwaitFor :: Stmt -> Stmt
remAwaitFor (Var var p)    = Var var (remAwaitFor p)
remAwaitFor (If exp p1 p2) = If exp (remAwaitFor p1) (remAwaitFor p2)
remAwaitFor (Seq p1 p2)    = Seq (remAwaitFor p1) (remAwaitFor p2)
remAwaitFor (Loop p)       = Loop (remAwaitFor p)
remAwaitFor (Every e p)    = Every e (remAwaitFor p)
remAwaitFor (And p1 p2)    = And (remAwaitFor p1) (remAwaitFor p2)
remAwaitFor (Or p1 p2)     = Or (remAwaitFor p1) (remAwaitFor p2)
remAwaitFor (Spawn p)      = Spawn (remAwaitFor p)
remAwaitFor (Fin id p)     = Fin id (remAwaitFor p)
remAwaitFor (Async p)      = error "remAwaitFor: unexpected statement (Async)"
remAwaitFor (Fin' p)       = Fin' (remAwaitFor p)
remAwaitFor AwaitFor       = AwaitExt inputForever
remAwaitFor p              = p

-- toGrammar: Converts full -> basic

toGrammar :: Stmt -> G.Stmt
toGrammar p = toG $ remAwaitFor $ remAsync
                  $ remSpawn $ chkSpawn
                  $ remFin p where
  toG :: Stmt -> G.Stmt
  toG (Var id p)     = G.Var id (toG p)
  toG (Write id exp) = G.Write id exp
  toG (AwaitExt e)   = G.AwaitExt e
  toG (AwaitInt e)   = G.AwaitInt e
  toG (EmitInt e)    = G.EmitInt e
  toG Break          = G.Break
  toG (If exp p1 p2) = G.If exp (toG p1) (toG p2)
  toG (Seq p1 p2)    = G.Seq (toG p1) (toG p2)
  toG (Loop p)       = G.Loop (toG p)
  toG (Every e p)    = G.Every e (toG p)
  toG (And p1 p2)    = G.And (toG p1) (toG p2)
  toG (Or p1 p2)     = G.Or (toG p1) (toG p2)
  toG (Error msg)    = G.Error msg
  toG (Fin' p)       = G.Fin (toG p)
  toG Nop'           = G.Nop
  toG _              = error "toG: unexpected statement (AwaitFor,Fin,Spawn,Async)"

evalFullProg :: Stmt -> [ID_Evt] -> Val
evalFullProg prog hist = E.evalProg (toGrammar prog) []
