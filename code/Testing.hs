
import ExampleLanguage
import ExampleTunableAI
import System.Console.ANSI
import System.Environment
import qualified Data.Map as M
import qualified Data.Set as S

import Data.IORef

data Test = Test {
              name :: String, test :: [Int] -> IO (Bool, [Int])
            }

instance Show Test where
  show = name

tests :: [Test]
tests = [trivial_1, trivial_2] ++ 
        [factorial (flow_insensitive) (ZT, S.empty),
         factorial (flow_sensitive) (ZT, S.empty),
         factorial (traditional_k_cfa 4) (ZT, S.empty),
         factorial (traditional_k_cfa 5) (ZCon 120, S.empty),
         factorial (stack_kcfa 4) (ZT, S.empty),
         factorial (stack_kcfa 5) (ZCon 120, S.empty),
         factorial (property_simulation) (ZT, S.empty),
         factorial (k_alloc 4) (ZT, S.empty),
         factorial (k_alloc 5) (ZCon 120, S.empty),
         factorial (product_cfs (stack_kcfa 4) (k_alloc 4)) (ZT, S.empty),
         factorial (product_cfs (stack_kcfa 4) (k_alloc 5)) (ZCon 120, S.empty),
         factorial (product_cfs (stack_kcfa 5) (k_alloc 4)) (ZCon 120, S.empty),
         factorial (product_cfs (traditional_k_cfa 5) (property_simulation)) (ZCon 120, S.empty),
         factorial (product_cfs flow_insensitive property_simulation) (ZT, S.empty)
       ]


-- A few (somewhat silly) unit tests:
--
-- Trivial expressions:
--

-- 3 + 5 == 8
trivial_1 = Test "Trivial 1" $
            \labels -> let l1:l2:l3:labels' = labels in
            return
            (
               eval_trivial 
               ((TBinop Plus (TNum 3 l1) (TNum 5 l2)) l3) 
               (M.empty) (M.empty) FlowInsensitiveTrace
               == 
               (ZCon 8, S.empty)
            ,
               labels'
            )

-- variables: 3 * x / x = 5
trivial_2 = Test "Trivial 2" $
            \labels -> let l1:l2:l3:labels' = labels in
            return
            (
              eval_trivial
              (TBinop Times (TNum 3 l1) (TVar "x" l2) l3) 
              (M.insert "x" (S.singleton (2, FlowInsensitiveTrace, 4)) M.empty) 
              (M.insert (2, FlowInsensitiveTrace, 4) (ZCon 5,S.empty) M.empty) 
              FlowInsensitiveTrace
              == 
              (ZCon 15, S.empty)
            ,
              labels'
            )

--
-- Serious expressions:
--

fact k = let [l1,l2,l3,l4,l5,l6,l7,l8,l9,l10,l11,l12,l13,l14,l15,l16] = [10001..10016] in
         SLet "fact" (TLam (UserFun ["k", "self", "n", "acc"]
                             (SIf (TVar "n" l1) 
                                  (SCall (TVar "self" l2) [TVar "k" l3, 
                                                           TVar "self" l16,
                                                           TBinop Minus (TVar "n" l4) (TNum 1 l5) l6,
                                                           TBinop Times (TVar "acc" l7) (TVar "n" l8) l9] l10)
                                  (SCall (TVar "k" l11) [TVar "acc" l12] l13) l14))
                              l15) k

-- variables: 3 * x / x = 5
factorial :: (Trace θ) => ControlFlowSensitivity θ -> Value' θ -> Test
factorial cfs expected = 
            Test ("Factorial(5) / " ++ (show cfs)) $
            \labels -> let 
              l1:l2:l3:labels' = labels 
              myprog' n = fact ( SCall (TVar "fact" 2) 
                                   [TLam HaltContinuation 3, TVar "fact" 4, TNum n 5, TNum 1 6] 7 ) 8
              myprog = myprog' 5 --input to factorial function
              output = eval (cfs) myprog
              (_, ρ, σ, _) = ((snd . last) (M.toList output))
              Just as = M.lookup "acc" ρ
              v = foldl (⊔) bot [ M.findWithDefault (error "oops") a σ | a <- S.toList as ] 
            in
              if v == expected
              then return (True, labels')
              else yellow >>
                   putStrLn ("got " ++ (show v) ++ " expected " ++ (show expected)) >> 
                   normal >>
                   return (False, labels')



-- Run the tests:

green = setSGR [SetColor Foreground Vivid Green]
yellow = setSGR [SetColor Foreground Vivid Yellow]
red = setSGR [SetColor Foreground Vivid Red]
normal = setSGR [Reset]

dotest :: IO ()
dotest = let ids = [1..]
             go [] ids = normal >> return ()
             go (x:xs) ids = 
                          test x ids >>= (\oc_ids ->
                             if (fst oc_ids)
                               then green >> putStrLn ((name x) ++ ": passed!") >> go xs (snd oc_ids) >> normal
                               else red >> putStrLn ((name x) ++ ": failed! :(") >> go xs (snd oc_ids)) >> normal
        in
          go tests ids


factorial_example :: IO ()
factorial_example = 
  let
     -- "fact" is a binding that sets the variable "fact" to an appropriate lambda
     -- myprog provides it with a continuation that calls this function.
     --
     -- in the output you will see variables
     -- acc, the accumulated value of the factorial so far
     -- n, the rest of the factorial to compute
     -- k, the current continuation
     -- self, a reference to the function for the recursive call
     myprog' n = fact ( SCall (TVar "fact" 2) 
                 [TLam HaltContinuation 3, TVar "fact" 4, TNum n 5, TNum 1 6] 7 ) 8
     myprog = myprog' 5 --input to factorial function

     -- choice of control flow sensitivity
     -- you can also try:
     --   flow_sensitive
     --   flow_insensitive
     --   traditional_k_cfa n
     --   stack_kcfa n
     --   k_alloc n
     --   property_sensitive
     --   or any product of those, e.g. (product (k_alloc 3) (property_sensitive))
     cfs = traditional_k_cfa 5 

  in
    runAI cfs myprog

main = do
         args <- getArgs
         if length args > 0 && last args == "factorial"
         then factorial_example
         else dotest

{------------------------------------------------------}
{------------------------------------------------------}
{- The rest of the things in this file don't work yet -}
{------------------------------------------------------}
{------------------------------------------------------}

{-
run :: String -> IO ()
run input =  let 
               go :: State -> IO (Value)
               go x =
                case f x of
                  Left ζ -> print ζ >> putStrLn "" >> go ζ
                  Right v -> return v

               ast = run_parser exp_parser input
               cps_ast = fst $ cps 0 HaltContinuation ast
            in
               putStrLn "AST: " >> print ast >>
               putStrLn "" >>
               putStrLn "CPS: " >> print cps_ast >>
               putStrLn "" >>
               go (cps_ast, M.empty, M.empty, 0) >>= print
-}
{-
parse_and_runAI :: (Trace θ) => String -> ControlFlowSensitivity θ -> IO ()
parse_and_runAI s cfs = let
                          ast = run_parser exp_parser s
                          cps_ast = fst $ cps 0 HaltContinuation ast
                        in
                          runAI cfs cps_ast

-}

