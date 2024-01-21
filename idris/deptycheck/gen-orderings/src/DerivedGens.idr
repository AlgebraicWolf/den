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

genLangGiven : Fuel ->
               (Fuel -> (ctx : Context) -> Gen MaybeEmpty (Expression ctx)) =>
               (ctx : Context) ->
               Gen MaybeEmpty (Lang ctx)
genLangGiven = deriveGen


||| Generator of programs for given context.
public export
genLangGiven' : Fuel ->
                (ctx : Context) ->
                Gen MaybeEmpty (Lang ctx)
genLangGiven' fl ctx = genLangGiven fl ctx @{genExpressionGiven'}
-- genLangGiven fl [] = pure Empty
-- genLangGiven fl (nm :: ctx) = (Assign nm) <$> (genExpressionGiven' fl ctx) <*> (genLangGiven fl ctx)

genLangDerived : Fuel ->
                 (Fuel -> Gen MaybeEmpty Int) =>
                 Gen MaybeEmpty (ctx : Context ** Lang ctx)
genLangDerived = deriveGen

||| Derived generator of programs in some context.
public export
genLangDerived' : Fuel ->
                  Gen MaybeEmpty (ctx : Context ** Lang ctx)
genLangDerived' fl = genLangDerived fl @{genInt}
