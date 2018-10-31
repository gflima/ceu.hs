module Ceu.FullGrammar where

import Ceu.Globals
import qualified Ceu.Grammar as G
import qualified Ceu.Eval as E
import Debug.Trace

-- Special events:
-- "BOOT"
-- "FOREVER"
-- "ASYNC"

type In = (ID_Ext, Maybe Val)

-- Program (pg 5).
data Stmt
  = Var ID_Var Stmt                     -- variable declaration
  | Int ID_Int Bool Stmt                -- event declaration
  | Write ID_Var Exp                    -- assignment statement
  | AwaitExt ID_Ext (Maybe ID_Var)      -- await external event
  | EmitExt ID_Ext (Maybe Exp)          -- emit external event
  | AwaitFor                            -- await forever
  | AwaitTmr Exp                        -- await timer
  | AwaitInt ID_Int (Maybe ID_Var)      -- await internal event
  | EmitInt ID_Int (Maybe Exp)          -- emit internal event
  | Break                               -- loop escape
  | If Exp Stmt Stmt                    -- conditional
  | Seq Stmt Stmt                       -- sequence
  | Loop Stmt                           -- infinite loop
  | Every ID_Evt (Maybe ID_Var) Stmt    -- event iteration
  | And Stmt Stmt                       -- par/and statement
  | Or Stmt Stmt                        -- par/or statement
  | Spawn Stmt                          -- spawn statement
  | Pause ID_Var Stmt                   -- pause/suspend statement
  | Fin (Maybe ID_Var) Stmt             -- finalize statement
  | Async Stmt                          -- async statement
  | Error String                        -- generate runtime error (for testing purposes)
  | Fin' Stmt                           -- fin as in basic Grammar
  | Nop                                 -- nop as in basic Grammar
  deriving (Eq, Show)

infixr 1 `Seq`                  -- `Seq` associates to the right
infixr 0 `Or`                   -- `Or` associates to the right
infixr 0 `And`                  -- `And` associates to the right

-- remPay:
-- (Int e True ...)  -> (Var e_ (Int e False) ...)
-- (AwaitEvt e var)  -> (AwaitEvt e Nothing) ; (Write var e_)
-- (EmitInt e v)     -> (Write e_ v) ; (EmitInt e Nothing)
-- (Every e var ...) -> (Every e Nothing ((Write var e_) ; ...)
remPay :: Stmt -> Stmt
remPay (Var id p)                = Var id (remPay p)
remPay (Int int True p)          = Var ("_"++int) (Int int False (remPay p))
remPay (Int int False p)         = Int int False (remPay p)
remPay (AwaitExt ext (Just var)) = (AwaitExt ext Nothing) `Seq` (Write var (Read ("_"++ext)))
remPay (AwaitInt int (Just var)) = (AwaitInt int Nothing) `Seq` (Write var (Read ("_"++int)))
remPay (EmitInt  int (Just exp)) = (Write ("_"++int) exp) `Seq` (EmitInt int Nothing)
remPay (If cnd p1 p2)            = If cnd (remPay p1) (remPay p2)
remPay (Seq p1 p2)               = Seq (remPay p1) (remPay p2)
remPay (Loop p)                  = Loop (remPay p)
remPay (Every evt (Just var) p)  = Every evt Nothing
                                     ((Write var (Read ("_"++evt))) `Seq` (remPay p))
remPay (And p1 p2)               = And (remPay p1) (remPay p2)
remPay (Or p1 p2)                = Or (remPay p1) (remPay p2)
remPay (Spawn p)                 = Spawn (remPay p)
remPay (Fin var p)               = Fin var (remPay p)
remPay (Async p)                 = Async (remPay p)
remPay p                         = p

-- remFin:
-- (Fin _  p);A -> (or (Fin' p) A)
-- (Fin id p);A -> A ||| (Var (Or [(Fin p)] X)

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
  rF (Every evt exp p)   = ([], Every evt exp (snd (rF p)))
  rF (And p1 p2)         = ([], And (snd (rF p1)) (snd (rF p2)))
  rF (Or p1 p2)          = ([], Or (snd (rF p1)) (snd (rF p2)))
  rF (Spawn p)           = ([], Spawn (snd (rF p)))
  rF (Fin id p)          = error "remFin: unexpected statement (Fin)"
  rF (Async p)           = ([], Async (snd (rF p)))
  rF (Int id b p)        = ([], Int id b (snd (rF p)))

  rF (Var id p)          = (l'', Var id p''') where
                            (l', p')  = (rF p)   -- results from nested p
                            (p'',l'') = f id l' -- matches l' with current local id
                            p''' | ((toSeq p'') == Nop) = p' -- nothing to finalize
                                 | otherwise            = (Or (Fin' (toSeq p'')) p')

                            -- recs: Var in Var, [pending finalize] (id->stmts)
                            -- rets: [stmts to fin] in block, [remaining finalize]
                            f :: ID_Var -> [(ID_Var,Stmt)] -> ([Stmt], [(ID_Var,Stmt)])
                            f _ [] = ([], [])
                            f id1 ((id2,stmt):fs) = (a++a', b++b') where
                              (a',b') = f id1 fs
                              (a, b ) | (id2==id1) = ([stmt], [])
                                      | otherwise  = ([], [(id2,stmt)])

                            toSeq :: [Stmt] -> Stmt
                            toSeq []     = Nop
                            toSeq (s:ss) = Seq s (toSeq ss)

  rF p                   = ([], p)

-- remSpawn: Converts (spawn p1; ...) into (p1;AwaitFor or ...)

remSpawn :: Stmt -> Stmt
remSpawn (Var id p)          = Var id (remSpawn p)
remSpawn (Int id b p)        = Int id b (remSpawn p)
remSpawn (If exp p1 p2)      = If exp (remSpawn p1) (remSpawn p2)
remSpawn (Seq (Spawn p1) p2) = Or (Seq (remSpawn p1) AwaitFor) (remSpawn p2)
remSpawn (Seq p1 p2)         = Seq (remSpawn p1) (remSpawn p2)
remSpawn (Loop p)            = Loop (remSpawn p)
remSpawn (Every evt var p)   = Every evt var (remSpawn p)
remSpawn (And p1 p2)         = And (remSpawn p1) (remSpawn p2)
remSpawn (Or p1 p2)          = Or (remSpawn p1) (remSpawn p2)
remSpawn (Spawn p)           = error "remSpawn: unexpected statement (Spawn)"
remSpawn (Fin id p)          = Fin id (remSpawn p)
remSpawn (Async p)           = Async (remSpawn p)
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
  chkS (Var _ p)     = (notS p) && (chkS p)
  chkS (Int _ _ p)   = (notS p) && (chkS p)
  chkS (If _ p1 p2)  = (notS p1) && (notS p2) && (chkS p1) && (chkS p2)
  chkS (Seq p1 p2)   = (chkS p1) && (notS p2) && (chkS p2)
  chkS (Loop p)      = (notS p) && (chkS p)
  chkS (Every _ _ p) = (notS p) && (chkS p)
  chkS (And p1 p2)   = (notS p1) && (notS p2) && (chkS p1) && (chkS p2)
  chkS (Or p1 p2)    = (notS p1) && (notS p2) && (chkS p1) && (chkS p2)
  chkS (Spawn p)     = (notS p) && (chkS p)
  chkS (Fin _ p)     = (notS p) && (chkS p)
  chkS (Async p)     = (notS p) && (chkS p)
  chkS _             = True

-- remAsync: Adds AwaitFor in Loops inside Asyncs

remAsync :: Stmt -> Stmt
remAsync p = (rA False p) where
  rA :: Bool -> Stmt -> Stmt
  rA inA   (Var id p)        = Var id (rA inA p)
  rA inA   (Int id b p)      = Int id b (rA inA p)
  rA inA   (If exp p1 p2)    = If exp (rA inA p1) (rA inA p2)
  rA inA   (Seq p1 p2)       = Seq (rA inA p1) (rA inA p2)
  rA True  (Loop p)          = Loop (rA True (Seq p (AwaitExt "ASYNC" Nothing)))
  rA False (Loop p)          = Loop (rA False p)
  rA inA   (Every evt var p) = Every evt var (rA inA p)
  rA inA   (And p1 p2)       = And (rA inA p1) (rA inA p2)
  rA inA   (Or p1 p2)        = Or (rA inA p1) (rA inA p2)
  rA inA   (Spawn p)         = Spawn (rA inA p)
  rA inA   (Fin id p)        = Fin id (rA inA p)
  rA inA   (Async p)         = (rA True p)
  rA inA   p                 = p

-- TODO: chkAsync: no sync statements

-- remAwaitFor: Converts AwaitFor into (AwaitExt "FOREVER")

remAwaitFor :: Stmt -> Stmt
remAwaitFor (Var id p)        = Var id (remAwaitFor p)
remAwaitFor (Int id b p)      = Int id b (remAwaitFor p)
remAwaitFor (If exp p1 p2)    = If exp (remAwaitFor p1) (remAwaitFor p2)
remAwaitFor (Seq p1 p2)       = Seq (remAwaitFor p1) (remAwaitFor p2)
remAwaitFor (Loop p)          = Loop (remAwaitFor p)
remAwaitFor (Every evt var p) = Every evt var (remAwaitFor p)
remAwaitFor (And p1 p2)       = And (remAwaitFor p1) (remAwaitFor p2)
remAwaitFor (Or p1 p2)        = Or (remAwaitFor p1) (remAwaitFor p2)
remAwaitFor (Spawn p)         = Spawn (remAwaitFor p)
remAwaitFor (Fin id p)        = Fin id (remAwaitFor p)
remAwaitFor (Async p)         = error "remAwaitFor: unexpected statement (Async)"
remAwaitFor AwaitFor          = AwaitExt "FOREVER" Nothing
remAwaitFor p                 = p

-- remAwaitTmr:
--  var int tot_ = <DT>;
--  loop do
--      await TIMER;
--      tot_ = tot_ - 1;
--      if tot_ == 0 then
--          break;
--      end
--  end

remAwaitTmr :: Stmt -> Stmt
remAwaitTmr (Var id p)        = Var id (remAwaitTmr p)
remAwaitTmr (Int id b p)      = Int id b (remAwaitTmr p)
remAwaitTmr (If exp p1 p2)    = If exp (remAwaitTmr p1) (remAwaitTmr p2)
remAwaitTmr (Seq p1 p2)       = Seq (remAwaitTmr p1) (remAwaitTmr p2)
remAwaitTmr (Loop p)          = Loop (remAwaitTmr p)
remAwaitTmr (Every evt var p) = Every evt var (remAwaitTmr p)
remAwaitTmr (And p1 p2)       = And (remAwaitTmr p1) (remAwaitTmr p2)
remAwaitTmr (Or p1 p2)        = Or (remAwaitTmr p1) (remAwaitTmr p2)
remAwaitTmr (Spawn p)         = Spawn (remAwaitTmr p)
remAwaitTmr (Fin id p)        = Fin id (remAwaitTmr p)
remAwaitTmr (Async p)         = error "remAwaitTmr: unexpected statement (Async)"
remAwaitTmr (AwaitTmr exp)    = Var "__timer_await"
                                  (Seq
                                    (Write "__timer_await" exp)
                                    (Loop (
                                      (AwaitExt "TIMER" Nothing)                `Seq`
                                      (Write "__timer_await"
                                        (Sub (Read "__timer_await") (Const 1))) `Seq`
                                      (If (Equ (Read "__timer_await") (Const 0))
                                        Break)
                                        Nop
                                      )))
remAwaitTmr p                 = p

-- expdAwaitTmr:
-- expands ("TIMER",v) -> ("TIMER",Nothing) x v
expdAwaitTmr :: [In] -> [In]
expdAwaitTmr []                      = []
expdAwaitTmr (("TIMER", Just 0):ins) = (expdAwaitTmr ins)
expdAwaitTmr (("TIMER", Just v):ins) = ("TIMER",Nothing) : (expdAwaitTmr $ ("TIMER",Just(v-1)) : ins)
expdAwaitTmr (x:ins)                 = x : (expdAwaitTmr ins)

-- joinAwaitTmr:
-- joins --N outs w/ X out-- from TIMER into --1 outs w/ N*X out--
-- Boot, Timer,2
-- [a]   [b] [c] -> [ [a], [b], [c] ] => [ [a],[b,c] ]
joinAwaitTmr :: [In] -> [E.Outs] -> [E.Outs]
joinAwaitTmr [] []                                       = []
joinAwaitTmr (("TIMER", Just 1):ins) (outs:outss)        = outs : (joinAwaitTmr ins outss)
joinAwaitTmr (("TIMER", Just v):ins) (outs1:outs2:outss) = joinAwaitTmr (("TIMER",Just(v-1)):ins) ((outs1++outs2):outss)
joinAwaitTmr (x:ins) (outs:outss)                        = outs : (joinAwaitTmr ins outss)

-- toGrammar: Converts full -> basic

toGrammar :: Stmt -> G.Stmt
toGrammar p = toG $ remFin $ remAwaitFor $ remAwaitTmr $ remAsync
                  $ remSpawn $ chkSpawn $ remPay $ p where
  toG :: Stmt -> G.Stmt
  toG (Var id p)         = G.Var id (toG p)
  toG (Int id b p)       = G.Int id (toG p)
  toG (Write id exp)     = G.Write id exp
  toG (AwaitExt ext var) = G.AwaitExt ext
  toG (EmitExt ext exp)  = G.EmitExt ext exp
  toG (AwaitInt int var) = G.AwaitInt int
  toG (EmitInt int val)  = G.EmitInt int
  toG Break              = G.Break
  toG (If exp p1 p2)     = G.If exp (toG p1) (toG p2)
  toG (Seq p1 p2)        = G.Seq (toG p1) (toG p2)
  toG (Loop p)           = G.Loop (toG p)
  toG (Every evt var p)  = G.Every evt (toG p)
  toG (And p1 p2)        = G.And (toG p1) (toG p2)
  toG (Or p1 p2)         = G.Or (toG p1) (toG p2)
  toG (Error msg)        = G.Error msg
  toG (Pause var p)      = G.Pause var (toG p)
  toG (Fin' p)           = G.Fin (toG p)
  toG Nop                = G.Nop
  toG _                  = error "toG: unexpected statement (AwaitFor,Fin,Spawn,Async)"

reaction :: E.Stmt -> In -> (E.Stmt,E.Outs)
reaction p (ext,val) = (p''',outs) where
  (p'',_,_,_,outs) = E.steps (E.bcast ext [] p', 0, [], [], [])
  p' = E.Var (("_"++ext), val) p
  (E.Var _ p''') = p''

evalFullProg :: Stmt -> [In] -> (Val,[E.Outs])
evalFullProg prog ins = (val,outss')
  where
    (val,outss) = E.evalProg_Reaction (toGrammar prog) ins'' reaction
    ins'   = ("BOOT",Nothing):ins
    ins''  = expdAwaitTmr ins'
    outss' = joinAwaitTmr ins' outss
