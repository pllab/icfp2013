--
-- Implementation for "Tunable Control-Flow Sensitivity for Program Analysis"
--
-- Author: Berkeley Churchill
--

module ExampleTunableAI where

-- import System.IO.Unsafe (only used for debugging)

import ExampleLanguage
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List


{-------------------------------------------}
{-------------------------------------------}
{- Abstract Domains (See 4.3 and Figure 3) -}
{-------------------------------------------}
{-------------------------------------------}


-- Abstract Integers
data Z' = ZT | ZB | ZCon Integer deriving (Eq, Ord)

instance Show Z' where
  show (ZCon n) = show n
  show ZT = "ℤ⊤"
  show ZB = "ℤ⊥"

-- Abstract State
type State' θ = (S.Set Serious, Env' θ, (Store' θ), θ)

show_state :: (Trace θ) => State' θ -> String
show_state (ss, ρ, σ, θ) = "Expression: " ++ (show ss) ++ "\nEnv: " ++ (pretty_print ρ) ++ "\nStore: " ++ (pretty_print σ) ++ "\nTrace: " ++ (show θ)

-- Abstract Store
type Store' θ = M.Map (Address' θ) (Value' θ)

-- Abstract Closures (sets of closures)
type Closure' θ = (θ, Env' θ, Lambda)
type Closure'' θ = S.Set (Closure' θ)

-- Abstract Values
type Value' θ = (Z', Closure'' θ)

-- Abstract Environments
type Env' θ = M.Map Variable (S.Set (Address' θ))

-- Abstract Addresses 
-- (the last int is used to disambiguate the location of the arguments
-- in different positions in a function call)
type Address' θ = (Label, θ, Int)


{--------------------------------}
{--------------------------------}
{- Definitions of Join Operator -}
{--------------------------------}
{--------------------------------}

class Eq t => Joinable t where
  (⊔) :: t -> t -> t
  (⊏) :: t -> t -> Bool

  a ⊏ b = (a ⊔ b == b)

-- for abstract integers
instance Joinable Z' where
  ZT ⊔ _ = ZT
  _ ⊔ ZT = ZT
  ZB ⊔ x = x
  x ⊔ ZB = x
  x ⊔ y    = if (x == y) then x else ZT

-- for joining lists of things (addresses, serious,...)
instance (Ord t) => Joinable (S.Set t) where
  as ⊔ bs = S.union as bs

-- for joining values
instance (Joinable a, Joinable b) => Joinable (a,b) where
  (a1,b1) ⊔ (a2,b2) = (a1 ⊔ a2, b1 ⊔ b2)

-- For joining environments / stores
instance (Ord a, Joinable b) => Joinable (M.Map a b) where
  (⊔) = M.unionWith (⊔)

-- This is for joining states together.
instance (Joinable a, Joinable b, Joinable c, Eq d) => Joinable (a,b,c,d) where
  (s, ρ, σ, τ) ⊔ (s', ρ', σ', τ') = 
    if (τ /= τ') 
    then error "cannot join different traces"
    else (s ⊔ s', ρ ⊔ ρ', σ ⊔ σ', τ)

{----------------------}
{----------------------}
{- Abstract Semantics -}
{----------------------}
{----------------------}

{- Evaluation of Trivial Expressions (See Figure 3b) -}
eval_trivial :: (Trace θ) => Trivial -> Env' θ -> Store' θ -> θ -> Value' θ 
eval_trivial (TNum n _) _ _ _ = (ZCon n, S.empty)
eval_trivial (TVar x _) ρ σ _ = foldl1 (⊔) [ M.findWithDefault bot a σ | a <- S.toList (M.findWithDefault S.empty x ρ) ]
eval_trivial (TLam λ _) ρ σ τ = (ZB, S.singleton (τ, ρ, λ))
eval_trivial (TBinop op t1 t2 _) ρ σ τ = αop op (eval_trivial t1 ρ σ τ) (eval_trivial t2 ρ σ τ)

{- Evaluation of Serious Expressions (See Figure 3c) -}
eval_serious :: (Trace θ) => State' θ -> S.Set (State' θ)
eval_serious ζ = 
  let (ss, ρ, σ, τ) = ζ in
  flatMap ss (\s ->
  case s of
    (SLet x trivial s' _) -> let v = eval_trivial trivial ρ σ τ
                                 a = alloc s τ 0
                                 ρ' = M.insert x (S.singleton a) ρ
                                 σ' = M.insertWith (⊔) a v σ --weak update
                                 τ' = τ_stmt (s, τ) s'
                             in S.singleton ((S.singleton s'), ρ', σ', τ')

    (SSet x trivial s' _) -> let v = eval_trivial trivial ρ σ τ
                                 as = M.findWithDefault S.empty x ρ
                                 σ' = S.fold (\address -> \store -> M.insertWith (⊔) address v store) σ as
                                 τ' = τ_stmt (s, τ) s'
                             in S.singleton ((S.singleton s'), ρ, σ', τ')

    (SIf trivial st sf _) -> let v = eval_trivial trivial ρ σ τ
                                 true_branch = if (not $ elem (fst v) [ZB, ZCon 0]) 
                                               then (S.singleton st) 
                                               else S.empty
                                 false_branch = if ((ZCon 0) ⊏ (fst v)) 
                                                then (S.singleton sf) 
                                                else S.empty
                             in
                                 S.map (\s' -> ((S.singleton s'), ρ, σ, τ_stmt (s,τ) s')) 
                                       (S.union true_branch false_branch)

    (SCall f ts _) -> let vs = map (\t -> eval_trivial t ρ σ τ) ts
                          clos = snd $ eval_trivial f ρ σ τ
                      in S.map (\clo -> 
                        let
                          (τ', ρ, λ) = clo
                          ys = variables λ
                          as = map (alloc s τ) [1..(length ys)]
                          ρ' = foldl (\env -> \pair -> M.insert (fst pair) (S.singleton (snd pair)) env) ρ (zip ys as)
                          σ' = foldl (\sto -> \pair -> M.insertWith (⊔) (fst pair) (snd pair) sto) σ (zip as vs)
                          τ'' = τ_call (s, τ) clo
                        in
                          ((S.singleton (serious λ)), ρ', σ', τ'')) clos
    (SHalt _) -> S.empty
  )

{-----------------------------------------------------------}
{-----------------------------------------------------------}
{- Worklist algorithm: partitioning and widening (See 3.2) -}
{-----------------------------------------------------------}
{-----------------------------------------------------------}

eval :: (Trace θ) => ControlFlowSensitivity θ -> Serious -> M.Map θ (State' θ) 
eval cfs s = step M.empty (S.singleton ((S.singleton s), M.empty, M.empty, τ_init cfs))
  where
    step :: (Trace θ) => (M.Map θ (State' θ)) -> S.Set (State' θ) -> (M.Map θ (State' θ))
    step memo states =
      let 
--        for debugging
--        eval_states = unsafePerformIO ((mapM (putStrLn . show_state) states) >> putStrLn "" >> return (states >>= eval_serious))
        eval_states = flatMap states eval_serious
        (next_memo, next_states) = S.fold (
                                    \ζ ->
                                    \acc_memo_state ->
                                    let τ = trace ζ
                                        memo = fst acc_memo_state
                                        memo' = M.insertWith (⊔) τ ζ memo
                                        states = snd acc_memo_state 
                                        Just new_state = M.lookup τ memo'
                                    in
                                    if (memo == memo') then
                                      (memo, states)
                                    else
                                      (memo', S.insert new_state states)
                                 ) (memo, S.empty) eval_states
      in
        if S.size next_states == 0 
        then next_memo
        else step next_memo next_states

pretty_print :: (Show a, Show b) => M.Map a b -> String
pretty_print m = M.foldWithKey 
                 (\key -> \value -> \acc -> (acc ++ "\n    " ++ (show key) ++ "\t\t" ++ (show value))) "" m

runAI :: (Trace θ) => ControlFlowSensitivity θ -> Serious -> IO ()
runAI cfs s = let
                memo_table = eval cfs s

                
                showit [] = return ()
                showit ((θ, (_, ρ, σ, _)):xs) = 
                  do 
                    putStrLn ("Context: " ++ (show θ))
                    putStrLn ("\n  Abstract Environment: ")
                    putStrLn $ pretty_print ρ
                    putStrLn ("\n  Abstract Store: ")
                    putStrLn $ pretty_print σ
                    putStrLn ""
                    showit xs

              in putStrLn "\n\n" >> showit (M.toList memo_table)
{---------------------------------------------}
{---------------------------------------------}
{- Control Flow Sensitivities from Section 4 -}
{---------------------------------------------}
{---------------------------------------------}

-- Each control flow sensitivity is implemented in two parts: an
-- abstract datatype that represents the traces which implements
-- the Trace typeclass, and a member of the ControlFlowSensitivity
-- abstract datatype which sets a starting trace. The Trace typeclass
-- requires implementations of the update functions τ_call and
-- τ_stmt.

data ControlFlowSensitivity a = ControlFlowSensitivity {
                                  cfs_name :: String,
                                  τ_init :: a
                                }

instance Show (ControlFlowSensitivity θ) where
  show = cfs_name

-- this requires update functions for traces
class (Eq θ, Ord θ, Show θ) => Trace θ where
  -- 'Show' is used to display traces to the user
  -- 'Eq' is used to compare traces when memoizing
  -- 'Ord' is only for storing traces in a map. It can be totally
  --  arbitrary.

  -- note that (Serious, θ) is just the part of an abstract state
  -- that we care about for the examples we have; it could more
  -- generally also include an environment and store. We also restrict
  -- to a single serious expression (rather than a set) so that we can
  -- get a unique label.
  τ_stmt :: (Serious, θ) -> Serious -> θ 
  τ_call :: (Serious, θ) -> Closure' θ -> θ




-- Analysis 1 (4.4.1)
-- Flow and Context Insensitive

data FlowInsensitiveTrace = FlowInsensitiveTrace deriving (Eq, Ord)
instance Trace FlowInsensitiveTrace where
  τ_stmt _ _ = FlowInsensitiveTrace
  τ_call _ _ = FlowInsensitiveTrace

flow_insensitive = ControlFlowSensitivity "Flow Insensitive" FlowInsensitiveTrace

instance Show FlowInsensitiveTrace where
  show _ = "FI"




-- Analysis 2 (4.4.2) 
-- Flow Sensitive, Context Insensitive

data FlowSensitiveTrace = FlowSensitiveTrace (Maybe Label) deriving (Eq, Ord)
instance Trace FlowSensitiveTrace where
  τ_stmt _ s = FlowSensitiveTrace $ Just $ label s
  τ_call _ (_,_,λ) = FlowSensitiveTrace $ Just $ label λ

flow_sensitive = ControlFlowSensitivity "Flow Sensitive" (FlowSensitiveTrace Nothing)

instance Show FlowSensitiveTrace where
  show (FlowSensitiveTrace Nothing) = "FS / start"
  show (FlowSensitiveTrace (Just a)) = "FS / " ++ (show a)




-- Analysis 3 (4.4.3)
-- Flow-sensitive, traditional k-CFA

data TraditionalKCFATrace = TraditionalKCFATrace Int (Maybe Label) [Label] deriving (Eq, Ord)

instance Trace (TraditionalKCFATrace) where
  τ_stmt (_, (TraditionalKCFATrace k _ tr)) s = 
    TraditionalKCFATrace k (Just (label s)) tr

  τ_call (s, (TraditionalKCFATrace k _ tr)) (_,_,λ) = case λ of
      UserFun _ _ -> TraditionalKCFATrace k (Just (label λ)) (take k ((label s):tr))
      _ ->           TraditionalKCFATrace k (Just (label λ)) tr

traditional_k_cfa k = ControlFlowSensitivity ("traditional " ++ (show k) ++ "-CFA") (TraditionalKCFATrace k Nothing [])

instance Show TraditionalKCFATrace where
   show (TraditionalKCFATrace k Nothing cs) = (show k) ++ "-CFA / start / " ++ (show cs)
   show (TraditionalKCFATrace k (Just a) cs) = (show k) ++ "-CFA / " ++ (show a) ++ " / " ++ (show cs)


-- Analysis 4 (4.4.4)
-- Flow-sensitive, stack-based k-CFA

data StackKCFATrace = StackKCFATrace Int (Maybe Label) [Label] deriving (Eq, Show, Ord)
stack_kcfa_callstring (StackKCFATrace _ _ xs) = xs

instance Trace (StackKCFATrace) where
  τ_stmt (_, (StackKCFATrace k _ tr)) s = 
    StackKCFATrace k (Just (label s)) tr

  τ_call (s, (StackKCFATrace k _ tr)) (τ_clo, _, λ) = case λ of
      UserFun _ _ ->            StackKCFATrace k (Just (label λ)) (take k ((label s):tr))
      ReturnContinuation _ _ -> StackKCFATrace k (Just (label λ)) (stack_kcfa_callstring τ_clo)
      _ ->                      StackKCFATrace k (Just (label λ)) tr

stack_kcfa k = ControlFlowSensitivity ("stack " ++ (show k) ++ "-CFA") (StackKCFATrace k Nothing [])






-- Analysis 5 (4.4.5)
-- Flow-sensitive, k-allocation site sensitive

data KAllocationSiteTrace = KAllocationSiteTrace Int (Maybe Label) [Label] deriving (Eq, Show, Ord)
k_alloc_callstring (KAllocationSiteTrace _ _ xs) = xs

instance Trace (KAllocationSiteTrace) where
  τ_stmt (_, (KAllocationSiteTrace k _ tr)) s = 
    KAllocationSiteTrace k (Just (label s)) tr

  τ_call (s, (KAllocationSiteTrace k _ tr)) (τ_clo, _, λ) = case λ of
      UserFun _ _ ->            KAllocationSiteTrace k (Just (label λ)) (take k ((label s):tr))
      ReturnContinuation _ _ -> KAllocationSiteTrace k (Just (label λ)) (k_alloc_callstring τ_clo)
      _ ->                      KAllocationSiteTrace k (Just (label λ)) tr

k_alloc k = ControlFlowSensitivity (show k ++ "-allocation site") (KAllocationSiteTrace k Nothing [])






-- Analysis 6
-- Flow-sensitive, property sensitive

-- Here we provide a simple state machine that tracks if a lock is in
-- a locked/unlocked/error state. One could implement a more general
-- control flow sensitivity parameterized over any arbitrary finite
-- automaton.
data FSM = Locked | Unlocked | Error deriving (Eq, Show, Ord)

δ :: FSM -> Lambda -> FSM
δ Locked (UnlockContinuation _) = Unlocked
δ Locked (LockContinuation _) = Error
δ Unlocked (UnlockContinuation _) = Error
δ Unlocked (LockContinuation _) = Locked
δ start _ = start

data PropertySimulationTrace = PropertySimulationTrace (Maybe Label) FSM deriving (Eq, Show, Ord)

instance Trace (PropertySimulationTrace) where
  τ_stmt (_, (PropertySimulationTrace _ σ)) s =
    PropertySimulationTrace (Just (label s)) σ

  τ_call (_, (PropertySimulationTrace _ σ)) (_, _, λ) =
    PropertySimulationTrace (Just (label λ)) (δ σ λ)

property_simulation = ControlFlowSensitivity "property simulation" (PropertySimulationTrace Nothing Unlocked)




{----------------------------------------------------------}
{----------------------------------------------------------}
{- Products and Sums of Trace Abstractions from Section 5 -}
{----------------------------------------------------------}
{----------------------------------------------------------}

-- Products
-- Given control flow sensitivities A, B, a trace of the sensitivity A
-- x B is just a pair (a,b) with a in A and b in B

instance (Trace a, Trace b) => Trace (a, b) where
  τ_stmt (s, τ) y = ((τ_stmt (s, fst τ) y), (τ_stmt (s, snd τ) y))
  τ_call (s, τ) (τ_ret, ρ, lam) = 
    let
      τ_1 = fst τ
      τ_2 = snd τ
      τ_ret_1 = fst τ_ret
      τ_ret_2 = snd τ_ret

      addr_fst :: Address' (a, b) -> Address' a
      addr_fst (a, x, b) = (a, fst x, b)

      addr_snd :: Address' (a, b) -> Address' b
      addr_snd (a, x, b) = (a, snd x, b)

      ρ1 = M.map (S.map addr_fst) ρ
      ρ2 = M.map (S.map addr_snd) ρ
    in
    ((τ_call (s, τ_1) (τ_ret_1, ρ1, lam)), (τ_call (s, τ_2) (τ_ret_2, ρ2, lam)))

product_cfs :: (Trace θ1, Trace θ2) => 
               ControlFlowSensitivity θ1 -> ControlFlowSensitivity θ2 -> ControlFlowSensitivity (θ1, θ2)
product_cfs x y = ControlFlowSensitivity (show (x,y)) ((τ_init x), (τ_init y))







{--------------------}
{--------------------}
{- Helper Functions -}
{--------------------}
{--------------------}

flatMap :: (Ord a, Ord b) => S.Set a -> (a -> (S.Set b)) -> S.Set b
flatMap s f = S.unions $ S.toList $ S.map f s

-- Given a concrete operator on integers, this yields the abstract
-- operator on our domain. Note that this fails for partial functions,
-- like division.
αop :: Binop -> Value' θ -> Value' θ -> Value' θ
αop op (a,_) (b,_) = let f = getop op in
                     case (a,b) of
                      (ZB, _) -> (ZB, S.empty)
                      (_, ZB) -> (ZB, S.empty)
                      (ZT, _) -> (ZT, S.empty)
                      (_, ZT) -> (ZT, S.empty)
                      (ZCon a, ZCon b) -> (ZCon (f a b), S.empty)


-- alloc determines the address of the nth variable allocated in ζ
alloc :: (Trace θ) => Serious -> θ -> Int -> Address' θ
alloc s τ n = (label s, τ, n)

-- Given an abstract state, this extracts the abstract trace
trace :: State' θ -> θ
trace (_,_,_,x) = x

-- This is the bottom value in the lattice
bot :: Value' t
bot = (ZB, S.empty)


