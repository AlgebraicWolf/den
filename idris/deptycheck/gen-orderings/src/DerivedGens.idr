module DerivedGens

import Test.DepTyCheck.Gen
import Deriving.DepTyCheck.Gen

import Spec

%default total
%language ElabReflection

------------------------------------------------------------
-- Generator derivation set-up
------------------------------------------------------------

%hint
UsedConstructorDerivator : ConstructorDerivator
UsedConstructorDerivator = LeastEffort {simplificationHack = True}

%logging "deptycheck.derive" 5

%hide Language.Reflection.TT.Name

------------------------------------------------------------
-- Derived generators
------------------------------------------------------------

-- We shall try to derive as much as possible to get close
-- to what would've been derived as easily as possible.

||| Generator of integer literals.
public export
genInt : Fuel -> Gen MaybeEmpty Int
genInt _ = elements [-10..10]

genExpressionGiven : Fuel ->
                     (Fuel -> Gen MaybeEmpty Int) =>
                     (ctx : Context) ->
                     Gen MaybeEmpty (Expression ctx)
genExpressionGiven = deriveGen


||| Generator of expressions with given context.
public export
genExpressionGiven' : Fuel ->
                      (ctx : Context) ->
                      Gen MaybeEmpty (Expression ctx)
genExpressionGiven' fl ctx = genExpressionGiven fl ctx @{genInt}

||| Generator of a name.
public export
genName : Fuel -> Gen MaybeEmpty Name
genName = deriveGen

||| Generator of expressions with generated context.
public export
genExpression : Fuel ->
                (Fuel -> Gen MaybeEmpty Int) =>
                (Fuel -> (ctx : Context) -> Gen MaybeEmpty (Expression ctx)) =>
                Gen MaybeEmpty (ctx : Context ** Expression ctx)
genExpression = deriveGen

