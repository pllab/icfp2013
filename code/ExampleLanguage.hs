--
-- This file has syntax, the CPS transform and interpreter. These
-- details are not as relevant to our work and are less polished. The
-- abstract interpreter is in another file.
--
-- Author: Berkeley Churchill
--

module ExampleLanguage where
import qualified Data.Map as M
import Data.List

{-----------------------------------------------}
{-----------------------------------------------}
{- Direct Style Syntax (See 4.1 and Figure 1b) -}
{-----------------------------------------------}
{-----------------------------------------------}

type Variable = String
data Binop = Plus | Minus | Times deriving (Show, Eq, Ord)

data Exp = ENum Integer |
           EVar Variable |
           EBinop Binop Exp Exp |
           EAssign Variable Exp |
           ESeq Exp Exp |
           ELambda [Variable] Exp |
           ECall Exp [Exp] |
           ELet Variable Exp Exp |
           EIf Exp Exp Exp
           deriving (Eq, Show)

{-------------------------------------------------------------}
{-------------------------------------------------------------}
{- Continuation Passing Style Syntax (See 4.1 and Figure 1b) -}
{-------------------------------------------------------------}
{-------------------------------------------------------------}

type Label = Int

data Trivial = TNum Integer Label | 
               TVar Variable Label | 
               TLam Lambda Label | 
               TBinop Binop Trivial Trivial Label
               deriving (Eq, Ord)

instance Show Trivial where
  show (TNum n _) = (show n)
  show (TVar x _) = x
  show (TLam l _) = "<lambda>"
  show (TBinop op x y _) = (show x) ++ " " ++ (show op) ++ " " ++ (show y)

data Serious = SLet Variable Trivial Serious Label | 
               SSet Variable Trivial Serious Label | 
               SIf Trivial Serious Serious Label | 
               SCall Trivial [Trivial] Label |
               SHalt Label
               deriving (Eq, Ord)

instance Show Serious where
  show (SLet x t s _) = "let " ++ x ++ " = " ++ (show t) ++ " in { " ++ (show s) ++ " }"
  show (SSet x t s _) = "set " ++ x ++ " = " ++ (show t) ++ " in { " ++ (show s) ++ " }"
  show (SIf c t f _) = "if ( " ++ (show c) ++ " ) then { " ++ (show t) ++ " } else { " ++ (show f) ++ "}"
  show (SCall t xs _) = "(" ++ (show t) ++ ")" ++ "(" ++ (intercalate "," (map show xs)) ++ ")"
  show (SHalt _) = "HALT"

data Lambda = UserFun [Variable] Serious |
              CPSFun [Variable] Serious |
              ReturnContinuation Variable Serious |
              LockContinuation Serious |
              UnlockContinuation Serious |
              HaltContinuation
              deriving (Eq, Ord)

instance Show Lambda where
  show _ = "<lambda>"

-- these extract the set of variables and targets of a function
variables :: Lambda -> [Variable]
variables (UserFun vs _) = vs
variables (CPSFun vs _) = vs
variables (ReturnContinuation v _) = [v]
variables (LockContinuation _) = []
variables (UnlockContinuation _) = []
variables HaltContinuation = []

serious :: Lambda -> Serious
serious (UserFun _ s) = s
serious (CPSFun _ s) = s
serious (ReturnContinuation _ s) = s
serious (LockContinuation s) = s
serious (UnlockContinuation s) = s
serious HaltContinuation = SHalt (-1)



-- This typeclass provides a way of extracting a label
-- from trivial, serious and lambdas.
class Labeled a where
  label :: a -> Label

instance Labeled Trivial where
  label (TNum _ l) = l
  label (TVar _ l) = l
  label (TLam _ l) = l
  label (TBinop _ _ _ l) = l

instance Labeled Serious where
  label (SLet _ _ _ l) = l
  label (SSet _ _ _ l) = l
  label (SIf _ _ _ l) = l
  label (SCall _ _ l) = l
  label (SHalt l) = l

instance Labeled Lambda where
  label λ = label $ serious λ

{-----------------}
{-----------------}
{- CPS Transform -}
{-----------------}
{-----------------}

-- These rules were adapted from those on page 4 of "Compiling with
-- Continuations Continued" by Andrew Kennedy.

-- Unfortunately, this is a huge mess.

tmp :: Int -> Variable
tmp i = "$" ++ (show i)

cps :: Int -> Lambda -> Exp -> (Serious, Int)

cps st κ (ENum n) = (( SCall (TLam κ st) [TNum n (st+1)] (st+2) ), st + 3)
cps st κ (EVar x) = (( SCall (TLam κ st) [TVar x (st+1)] (st+2) ), st + 3)

cps st κ (EBinop op e1 e2) =
  let x1 = tmp st
      x2 = tmp (st+1)
      κ' = CPSFun [x1] (lhs)
      κ'' = CPSFun [x2] ( SCall
              (TLam κ st)
              [TBinop op (TVar x1 (st+1)) (TVar x2 (st+2)) (st+3)]
              (st + 4)
            )
      (lhs, st') = cps (st+5) κ'' e2
    in
      cps st' κ' e1
      
cps st κ (ELambda xs e) =
  let x1 = tmp st
      x2 = tmp (st+1)
      x3 = tmp (st+2)
      (inner, st') = (cps (st + 8) (CPSFun [x3] (SCall (TVar x2 st) [TVar x3 (st+1)] (st+2))) e)
  in
    (SLet x1 
      (TLam (CPSFun (x2:xs) inner) (st+3))
      (SCall (TLam κ (st+4)) [TVar x1 (st+5)] 
      (st+6)) (st+7), st')

-- e1 ; e2
-- [[ e1 ]] (\x -> [[ e2 ]] κ)
cps st κ (ESeq e1 e2) = 
  let x = tmp st
      (e2cps, st') = cps (st + 1) κ e2
      κ' = CPSFun [x] e2cps
  in
    cps st' κ' e1

--  x := e    ~>
--  [[e]] (\v -> set x = v in κ(v))
cps st κ (EAssign x e) =
  let y = tmp st
      κ' = CPSFun [y] (SSet x (TVar y st) (SCall (TLam κ (st+1)) [TVar y (st+2)]  (st+3)) (st+4))
  in
    cps (st+5) κ' e

--  let x := e1 in e2
--  [[ e1 ]] (\v -> let x = v in [[ e2 ]] κ)
cps st κ (ELet x e1 e2) =
  let y = tmp st
      (e2cps, st') = cps (st + 2) κ e2
      κ' = CPSFun [y] (SLet x (TVar y st) e2cps (st+1))
  in
    cps st' κ' e1

-- f(e1,e2,...,en)
--
-- [[ f ]] (\clo ->
--   [[ e1 ]] -> (\x1 ->
--   [[ e2 ]] -> (\x2 ->
--    . . .
--   [[ en ]] -> (\xn ->
--     f(x1,...,xn)


{-------------------------------------}
{-------------------------------------}
{- Concrete Semantics (See Figure 2) -}
{-------------------------------------}
{-------------------------------------}

type Address = Int
type Value = Either Integer Closure
type State = (Serious, Env, Store, Address) -- the last Int is used to track the size of the heap
type Env = M.Map Variable Address
type Store = M.Map Address Value
type Closure = (Env, Lambda)

-- Trivial evaluation (see 2b)
η :: Trivial -> Env -> Store -> Value
η (TNum n _) _ _ = Left n
η (TVar x _) ρ σ = M.findWithDefault (error ("bad address for: " ++ x))
                   (M.findWithDefault (error ("variable not found: " ++ x)) x ρ)
                   σ 

η (TLam lambda _) ρ σ = Right (ρ, lambda )
η (TBinop op t1 t2 _ ) ρ σ = let Left lhs = η t1 ρ σ
                                 Left rhs = η t2 ρ σ
                             in
                                 Left ((getop op) lhs rhs)

-- Trivial evaluation (see 2c)
f :: State -> Either State Value
f (SLet x t s _, ρ, σ, m) = Left (s, M.insert x m ρ, M.insert m (η t ρ σ) σ, m+1)

f (SSet x t s _, ρ, σ, m) = let a = M.lookup x ρ in
                            case a of
                              Nothing -> Left (s, M.insert x m ρ, M.insert m (η t ρ σ) σ, m + 1)
                              Just a -> Left (s, ρ, M.insert a (η t ρ σ) σ, m)

f (SCall target args _, ρ, σ, m) = 
  let Right (ρc, lam) = η target ρ σ
      names = variables lam
      vals = map (\x -> η x ρ σ) args
      addrs = [m..(m+(length vals)-1)]
      ρ' = foldl (\env -> \name_addr -> M.insert (fst name_addr) (snd name_addr) env) ρc (zip names addrs)
      σ' = foldl (\sto -> \addr_val -> M.insert (fst addr_val) (snd addr_val) sto) σ (zip addrs vals)
  in
      case lam of
        HaltContinuation -> Right (head vals)
        _ -> Left (serious lam, ρ', σ', m+(length vals))
    
{-----------}
{-----------}
{- Helpers -}
{-----------}
{-----------}

getop :: Binop -> (Integer -> Integer -> Integer)
getop Plus = (+)
getop Minus = (-)
getop Times = (*)


