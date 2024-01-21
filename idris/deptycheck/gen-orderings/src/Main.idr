module Main

import Control.Monad.Either
import Data.Fuel
import Data.Fin
import Data.List
import Data.List.Lazy
import Data.String

import Text.PrettyPrint.Prettyprinter

import Test.DepTyCheck.Gen

import System
import System.Random.Pure.StdGen

import Spec
import DerivedGens

%default total

------------------------------------------------------------
-- Handwritten generators
------------------------------------------------------------

||| Generator of programs for given context.
genLangGiven : Fuel ->
               (ctx : Context) ->
               Gen MaybeEmpty (Lang ctx)
genLangGiven fl [] = pure Empty
genLangGiven fl (nm :: ctx) = (Assign nm) <$> (genExpressionGiven' fl ctx) <*> (genLangGiven fl ctx)

||| Generator of programs -- first ordering: Expression[] + Statement[0].
genLang1 : Fuel ->
           Gen MaybeEmpty (ctx : Context ** Lang ctx)
genLang1 fl = oneOf [pure ([] ** Empty), do
  (ctx ** e) <- genExpression @{genInt} @{genExpressionGiven'} fl
  rest <- genLangGiven fl ctx
  nm <- genName fl
  pure (nm::ctx ** Assign nm e rest)]

||| Generator of programs -- second ordering: Expression[0] + Statement[].
genLang2 : Fuel ->
           Gen MaybeEmpty (ctx : Context ** Lang ctx)
genLang2 Dry = pure ([] ** Empty)
genLang2 (More fl) = oneOf [pure ([] ** Empty), do
  ((ctx ** rest), nm) <- (,) <$> genLang2 fl <*> genName fl
  expr <- genExpressionGiven' fl ctx
  pure (nm::ctx ** Assign nm expr rest)]

||| Generator with pretty-printing applied.
genLang : Fuel ->
          Gen MaybeEmpty String
genLang fl = genLang1 fl <&> \(_ ** prog) => show $ pretty {ann=Void} prog

------------------------------------------------------------
-- Running
------------------------------------------------------------

printOnce : HasIO io => MonadError String io => (seed : Maybe Bits64) -> String -> (n : Nat) -> Gen MaybeEmpty String -> io Unit
printOnce seed dir n gen = do
  randomGen <- maybe initStdGen (pure . mkStdGen) seed

  Lazy.for_ (unGenTryN n randomGen gen) $ \test => do
    putStrLn "Generated program:"
    putStrLn test
    putStrLn ""

  pure ()

run : HasIO io => MonadError String io => io ()
run = printOnce (Just 42) "out" 100 (genLang $ limit 10)

main : IO ()
main = runEitherT {m=IO} run >>= either (die . (++) "Error: ") pure
