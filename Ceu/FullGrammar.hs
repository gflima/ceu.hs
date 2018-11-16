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

type Fin = (Stmt, Stmt, Stmt)

-- Program (pg 5).
data Stmt
  = Var ID_Var (Maybe Fin) Stmt         -- variable declaration
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
  | Pause ID_Evt Stmt                   -- pause/suspend statement
  | Fin Stmt Stmt Stmt                  -- finalize/pause/resume statement
  | Async Stmt                          -- async statement
  | Error String                        -- generate runtime error (for testing purposes)
  | Par' Stmt Stmt                      -- par as in basic Grammar
  | Pause' ID_Var Stmt                  -- pause as in basic Grammar
  | Fin' Stmt                           -- fin as in basic Grammar
  | Trap' Stmt                          -- trap as in basic Grammar
  | Escape' Int                         -- escape as in basic Grammar
  | Nop                                 -- nop as in basic Grammar
  deriving (Eq, Show)

infixr 1 `Seq`                  -- `Seq` associates to the right
infixr 0 `Or`                   -- `Or` associates to the right
infixr 0 `And`                  -- `And` associates to the right

-- remAwaitFor: Converts AwaitFor into (AwaitExt "FOREVER")

remAwaitFor :: Stmt -> Stmt
remAwaitFor (Var id Nothing p) = Var id Nothing (remAwaitFor p)
remAwaitFor (Int id b p)       = Int id b (remAwaitFor p)
remAwaitFor (If exp p1 p2)     = If exp (remAwaitFor p1) (remAwaitFor p2)
remAwaitFor (Seq p1 p2)        = Seq (remAwaitFor p1) (remAwaitFor p2)
remAwaitFor (Loop p)           = Loop (remAwaitFor p)
remAwaitFor (Par' p1 p2)       = Par' (remAwaitFor p1) (remAwaitFor p2)
remAwaitFor (Pause' var p)     = Pause' var (remAwaitFor p)
remAwaitFor (Trap' p)          = Trap' (remAwaitFor p)
remAwaitFor AwaitFor           = AwaitExt "FOREVER" Nothing
remAwaitFor p                  = p

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
remAwaitTmr (Var id Nothing p) = Var id Nothing (remAwaitTmr p)
remAwaitTmr (Int id b p)      = Int id b (remAwaitTmr p)
remAwaitTmr (If exp p1 p2)    = If exp (remAwaitTmr p1) (remAwaitTmr p2)
remAwaitTmr (Seq p1 p2)       = Seq (remAwaitTmr p1) (remAwaitTmr p2)
remAwaitTmr (Loop p)          = Loop (remAwaitTmr p)
remAwaitTmr (Par' p1 p2)      = Par' (remAwaitTmr p1) (remAwaitTmr p2)
remAwaitTmr (Pause' var p)    = Pause' var (remAwaitTmr p)
remAwaitTmr (Trap' p)         = Trap' (remAwaitTmr p)
remAwaitTmr (AwaitTmr exp)    = Var "__timer_await" Nothing
                                  (Seq
                                    (Write "__timer_await" exp)
                                    (Trap'
                                      (Loop (
                                        (AwaitExt "TIMER" Nothing)                `Seq`
                                        (Write "__timer_await"
                                          (Sub (Read "__timer_await") (Const 1))) `Seq`
                                        (If (Equ (Read "__timer_await") (Const 0))
                                          (Escape' 0))
                                          Nop
                                        ))))
remAwaitTmr p                 = p

-- expdAwaitTmr:
-- expands ("TIMER",v) -> ("TIMER",Nothing) * v
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

-- remPay:
-- (Int e True ...)  -> (Var e_ (Int e False) ...)
-- (AwaitEvt e var)  -> (AwaitEvt e Nothing) ; (Write var e_)
-- (EmitInt e v)     -> (Write e_ v) ; (EmitInt e Nothing)
-- (Every e var ...) -> (Every e Nothing ((Write var e_) ; ...)
remPay :: Stmt -> Stmt
remPay (Var id Nothing p)        = Var id Nothing (remPay p)
remPay (Int int True p)          = Var ("_"++int) Nothing (Int int False (remPay p))
remPay (Int int False p)         = Int int False (remPay p)
remPay (AwaitExt ext (Just var)) = (AwaitExt ext Nothing) `Seq` (Write var (Read ("_"++ext)))
remPay (AwaitInt int (Just var)) = (AwaitInt int Nothing) `Seq` (Write var (Read ("_"++int)))
remPay (EmitInt  int (Just exp)) = (Write ("_"++int) exp) `Seq` (EmitInt int Nothing)
remPay (If cnd p1 p2)            = If cnd (remPay p1) (remPay p2)
remPay (Seq p1 p2)               = Seq (remPay p1) (remPay p2)
remPay (Loop p)                  = Loop (remPay p)
remPay (Every evt (Just var) p)  = Every evt Nothing
                                     ((Write var (Read ("_"++evt))) `Seq` (remPay p))
remPay (Par' p1 p2)              = Par' (remPay p1) (remPay p2)
remPay (Pause' var p)            = Pause' var (remPay p)
remPay (Fin' p)                  = Fin' (remPay p)
remPay (Trap' p)                 = Trap' (remPay p)
remPay p                         = p

-- remBreak

remBreak :: Stmt -> Stmt
remBreak p = rB (-1) p where
  rB :: Int -> Stmt -> Stmt
  rB n (Var var Nothing p) = Var var Nothing (rB n p)
  rB n (Int int b p)       = Int int b (rB n p)
  rB n (If exp p1 p2)      = If exp (rB n p1) (rB n p2)
  rB n (Seq p1 p2)         = Seq (rB n p1) (rB n p2)
  rB n (Loop p)            = Trap' (Loop (rB (n+1) p))
  rB (-1) Break            = error "remBreak: `break` without `loop`"
  rB n Break               = Escape' n
  rB n (Every evt var p)   = Every evt var (rB n p)
  rB n (Par' p1 p2)        = Par' (rB n p1) (rB n p2)
  rB n (Pause' var p)      = Pause' var (rB n p)
  rB n (Fin' p)            = Fin' (rB n p)
  rB n (Trap' p)           = Trap' (rB (n+1) p)
  rB n p                   = p

-- remAndOr

remAndOr :: Stmt -> Stmt
remAndOr (Var var Nothing p) = Var var Nothing (remAndOr p)
remAndOr (Int int b p)       = Int int b (remAndOr p)
remAndOr (If exp p1 p2)      = If exp (remAndOr p1) (remAndOr p2)
remAndOr (Seq p1 p2)         = Seq (remAndOr p1) (remAndOr p2)
remAndOr (Loop p)            = Loop (remAndOr p)
remAndOr (And p1 p2)         = Par' (remAndOr p1) (remAndOr p2)
remAndOr (Or p1 p2)          = Trap' (Par' (Seq (remAndOr p1) (Escape' 0)) (Seq (remAndOr p2) (Escape' 0)))
remAndOr (Pause' var p)      = Pause' var (remAndOr p)
remAndOr (Trap' p)           = Trap' (remAndOr p)
remAndOr p                   = p

-- remSpawn: Converts (spawn p1; ...) into (p1;AwaitFor or ...)

remSpawn :: Stmt -> Stmt
remSpawn (Var id Nothing p)  = Var id Nothing (remSpawn p)
remSpawn (Int id b p)        = Int id b (remSpawn p)
remSpawn (If exp p1 p2)      = If exp (remSpawn p1) (remSpawn p2)
remSpawn (Seq (Spawn p1) p2) = Or (Seq (remSpawn p1) AwaitFor) (remSpawn p2)
remSpawn (Seq p1 p2)         = Seq (remSpawn p1) (remSpawn p2)
remSpawn (Loop p)            = Loop (remSpawn p)
remSpawn (And p1 p2)         = And (remSpawn p1) (remSpawn p2)
remSpawn (Or p1 p2)          = Or (remSpawn p1) (remSpawn p2)
remSpawn (Spawn p)           = error "remSpawn: unexpected statement (Spawn)"
remSpawn (Pause' var p)      = Pause' var (remSpawn p)
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
  chkS (Var _ _ p)   = (notS p) && (chkS p)
  chkS (Int _ _ p)   = (notS p) && (chkS p)
  chkS (If _ p1 p2)  = (notS p1) && (notS p2) && (chkS p1) && (chkS p2)
  chkS (Seq p1 p2)   = (chkS p1) && (notS p2) && (chkS p2)
  chkS (Loop p)      = (notS p) && (chkS p)
  chkS (Every _ _ p) = (notS p) && (chkS p)
  chkS (And p1 p2)   = (notS p1) && (notS p2) && (chkS p1) && (chkS p2)
  chkS (Or p1 p2)    = (notS p1) && (notS p2) && (chkS p1) && (chkS p2)
  chkS (Spawn p)     = (notS p) && (chkS p)
  chkS (Pause' _ p)  = (notS p)
  chkS (Fin' p)      = (notS p) && (chkS p)
  chkS (Async p)     = (notS p) && (chkS p)
  chkS _             = True

-- remPause:
--  pause e do
--      <...>
--  end
--
--  var __e = 0;
--  pause __e do
--      par/or do
--          every __e in e do
--          end
--      with
--          <...>
--      end
--  end
remPause :: Stmt -> Stmt
remPause (Var id Nothing p)  = Var id Nothing (remPause p)
remPause (Int id b p)        = Int id b (remPause p)
remPause (If exp p1 p2)      = If exp (remPause p1) (remPause p2)
remPause (Seq p1 p2)         = Seq (remPause p1) (remPause p2)
remPause (Loop p)            = Loop (remPause p)
remPause (And p1 p2)         = And (remPause p1) (remPause p2)
remPause (Or p1 p2)          = Or (remPause p1) (remPause p2)
remPause (Spawn p)           = Spawn (remPause p)
remPause (Pause evt p)       =
  Var ("__pause_var_"++evt) Nothing
    (Int ("__pause_int_"++evt) False
      (Seq
        (Write ("__pause_var_"++evt) (Const 0))
        (Or
          (Var "__tmp" Nothing
            (Every evt (Just "__tmp")
              (If (Equ (Read "__tmp") (Const 0))
                  (Seq (Write ("__pause_var_"++evt) (Const 0))
                       (EmitInt ("__pause_int_"++evt) Nothing))
                  Nop)))
        (Or
          (Pause' ("__pause_var_"++evt) p)
          (Var "__tmp" Nothing
            (Every evt (Just "__tmp")
              (If (Equ (Read "__tmp") (Const 1))
                  (Write ("__pause_var_"++evt) (Const 1))
                  Nop)))))))
remPause p                   = p

-- remAsync: Adds AwaitFor in Loops inside Asyncs

remAsync :: Stmt -> Stmt
remAsync p = (rA False p) where
  rA :: Bool -> Stmt -> Stmt
  rA inA   (Var id Nothing p) = Var id Nothing (rA inA p)
  rA inA   (Int id b p)       = Int id b (rA inA p)
  rA inA   (If exp p1 p2)     = If exp (rA inA p1) (rA inA p2)
  rA inA   (Seq p1 p2)        = Seq (rA inA p1) (rA inA p2)
  rA True  (Loop p)           = Loop (rA True (Seq p (AwaitExt "ASYNC" Nothing)))
  rA False (Loop p)           = Loop (rA False p)
  rA inA   (And p1 p2)        = And (rA inA p1) (rA inA p2)
  rA inA   (Or p1 p2)         = Or (rA inA p1) (rA inA p2)
  rA inA   (Spawn p)          = Spawn (rA inA p)
  rA inA   (Pause evt p)      = Pause evt (rA inA p)
  rA inA   (Async p)          = (rA True p)
  rA inA   p                  = p

-- remFin:
-- (Fin x y z);A -> (or (Fin' p) A)
-- (Fin id p);A -> A ||| (Var (Or [(Fin p)] X)

remFin :: Stmt -> Stmt
remFin p = rF Nothing p where
  rF :: (Maybe ID_Evt) -> Stmt -> Stmt
  rF pse (Var var (Just (x,y,z)) p) = rF pse (Var var Nothing (Seq (Fin x y z) p))
  rF pse (Var var Nothing p)       = Var var Nothing (rF pse p)
  rF pse (Int id b p)              = Int id b (rF pse p)
  rF pse (If exp p1 p2)            = If exp (rF pse p1) (rF pse p2)

  rF pse (Seq (Fin x y z) p)       = Or (rF pse p) (And (rF pse yz) (Fin' (rF pse x)))
    where
      yz = case (pse,y,z) of
        (Nothing,  Nop, Nop) -> Nop
        (Nothing,  _,   _)   -> error "remFin: unexpected pause/resume statement"
        (Just evt, y,   z)   -> And
                                  (Every evt Nothing y)
                                  (Every ("__pause_int_"++evt) Nothing z)

  rF pse (Seq p1 p2)               = Seq (rF pse p1) (rF pse p2)
  rF pse (Loop p)                  = Loop (rF pse p)
  rF pse (Every evt exp p)         = Every evt exp (rF pse p)
  rF pse (And p1 p2)               = And (rF pse p1) (rF pse p2)
  rF pse (Or p1 p2)                = Or (rF pse p1) (rF pse p2)
  rF pse (Spawn p)                 = Spawn (rF pse p)
  rF pse (Pause evt p)             = Pause evt (rF (Just evt) p)
  rF pse (Fin _ _ _)               = error "remFin: unexpected statement (Fin)"
  rF pse (Async p)                 = Async (rF pse p)
  rF pse p                         = p

-- toGrammar: Converts full -> basic

toGrammar :: Stmt -> G.Stmt
toGrammar p = toG $ remAwaitFor $ remAwaitTmr $ remPay
                  $ remBreak $ remAndOr $ remSpawn $ chkSpawn
                  $ remPause $ remAsync $ remFin
                  $ p where
  toG :: Stmt -> G.Stmt
  toG (Var id Nothing p) = G.Var id (toG p)
  toG (Int id b p)       = G.Int id (toG p)
  toG (Write id exp)     = G.Write id exp
  toG (AwaitExt ext var) = G.AwaitExt ext
  toG (EmitExt ext exp)  = G.EmitExt ext exp
  toG (AwaitInt int var) = G.AwaitInt int
  toG (EmitInt int val)  = G.EmitInt int
  toG (If exp p1 p2)     = G.If exp (toG p1) (toG p2)
  toG (Seq p1 p2)        = G.Seq (toG p1) (toG p2)
  toG (Loop p)           = G.Loop (toG p)
  toG (Every evt var p)  = G.Every evt (toG p)
  toG (Error msg)        = G.Error msg
  toG (Par' p1 p2)       = G.Par (toG p1) (toG p2)
  toG (Pause' var p)     = G.Pause var (toG p)
  toG (Fin' p)           = G.Fin (toG p)
  toG (Trap' p)          = G.Trap (toG p)
  toG (Escape' n)        = G.Escape n
  toG Nop                = G.Nop
  toG p                  = error $ "toG: unexpected statement: "++(show p)

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
