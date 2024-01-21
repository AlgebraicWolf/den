module Main

import Control.Monad.Either
import Data.Fuel
import Data.Fin
import Data.List
import Data.List.Lazy
import Data.String

import Debug.Trace

import Text.PrettyPrint.Prettyprinter

import Test.DepTyCheck.Gen

import System
import System.Random.Pure.StdGen

import Spec
import DerivedGens

import Data.Nat.Pos

%default total

------------------------------------------------------------
-- Handwritten generators
------------------------------------------------------------

public export
leftDepth : Fuel -> PosNat
leftDepth = go 1 where
  go : PosNat -> Fuel -> PosNat
  go n Dry      = n
  go n (More x) = go (succ n) x

toList : Context -> List Name
toList [] = []
toList (x :: xs) = x :: toList xs

Show Name where
  show (MkName k) = "x" ++ show k

||| Generator of programs -- first ordering: Expression[] + Lang[0].
genLang1 : Fuel ->
           Gen MaybeEmpty (ctx : Context ** Lang ctx)
genLang1 Dry = empty
genLang1 (More fl) = frequency [(1, genEmpty (More fl)), (leftDepth (More fl), genAssign (More fl))] where

  genEmpty : Fuel -> Gen MaybeEmpty (ctx : Context ** Lang ctx)
  genEmpty _ = pure ([] ** Empty)
  
  genAssign : Fuel -> Gen MaybeEmpty (ctx : Context ** Lang ctx)
  genAssign fl = do
    (ctx ** e) <- genExpression @{genInt} @{genExpressionGiven'} fl
    rest <- genLangGiven' fl ctx
    nm <- genName fl
    pure (nm::ctx ** Assign nm e rest)

||| Generator of programs -- second ordering: Expression[0] + Lang[].
genLang2 : Fuel ->
           Gen MaybeEmpty (ctx : Context ** Lang ctx)
genLang2 Dry = empty
genLang2 (More fl) = frequency [(1, genEmpty (More fl)), (leftDepth (More fl), genAssign (More fl))] where
  
  genEmpty : Fuel -> Gen MaybeEmpty (ctx : Context ** Lang ctx)
  genEmpty _ = pure ([] ** Empty)

  genAssign : Fuel -> Gen MaybeEmpty (ctx : Context ** Lang ctx)
  genAssign Dry = empty
  genAssign (More fl) = do
    (ctx ** rest) <- genLang2 fl
    (nm, expr) <- (,) <$> genName (More fl) <*> genExpressionGiven' (More fl) ctx
    pure (nm::ctx ** Assign nm expr rest)

length : Lang ctx -> Nat
length Empty = 0
length (Assign _ _ xs) = S $ length xs

avgExprSize : Lang ctx -> Double
avgExprSize prog = let l = length prog
                       in if l > 0 then cast (totalExprSize prog) / cast l else 0 where
  exprSize : Expression ctx' -> Nat
  exprSize (Literal i) = 1
  exprSize (Variable x) = 1
  exprSize (BinOp _ e e') = 1 + exprSize e + exprSize e'

  totalExprSize : Lang ctx' -> Nat
  totalExprSize Empty = 0
  totalExprSize (Assign nm e prog) = exprSize e + totalExprSize prog

||| Generator with pretty-printing applied.
genLang : Fuel ->
          Gen MaybeEmpty (String, Nat, Double)
genLang fl = genLang1 fl <&> \(_ ** prog) => (show $ pretty {ann=Void} prog, length prog, avgExprSize prog)

------------------------------------------------------------
-- Running
------------------------------------------------------------

-- unzip : Functor f => f (a, b) -> (f a, f b)


printOnce : HasIO io => MonadError String io => (seed : Maybe Bits64) -> (n : Nat) -> Gen MaybeEmpty (String, Nat, Double) -> io Unit
printOnce seed n gen = do
  randomGen <- maybe initStdGen (pure . mkStdGen) seed

  lengthsAndSizes <- Lazy.for (unGenTryN n randomGen gen) $ \(test, l, e) => do
    -- putStrLn "Generated program:"
    -- putStrLn test
    -- putStrLn ""
    pure (l, e)

  let (lengths, sizes) = unzip lengthsAndSizes

  putStr $ show {ty=Double} $ cast (foldr (+) (the Nat 0) lengths) / cast n
  putStr ","
  putStr $ show $ foldr (+) 0.0 sizes / cast {to=Double} n

  pure ()

run : HasIO io => MonadError String io => io ()
run = do
  [_, fuel] <- getArgs
    | _ => throwError "Please, specify fuel"
  printOnce Nothing 10 (genLang $ limit $ stringToNatOrZ fuel)

main : IO ()
main = runEitherT {m=IO} run >>= either (die . (++) "Error: ") pure
