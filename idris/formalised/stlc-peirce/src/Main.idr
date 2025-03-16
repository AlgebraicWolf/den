module Main

import Data.List.Elem
import Data.List.Quantifiers

%default total

--------------------------------------------------------------------------------
--      Part 1: Propositional logic and intuitionistic natural deduction      --
--------------------------------------------------------------------------------

-- We will start by specifying formulas of implication fragment of propositional
-- logic and defining intuitionistic natural deduction for it.

-- Formulae of implication fragment of propositional logic
data Prop : Type where
  -- Atomic proposition
  Atom : Nat -> Prop
  -- Implication
  Imp : Prop -> Prop -> Prop

infixr 6 ~>

(~>) : Prop -> Prop -> Prop
(~>) = Imp

-- In particular, here is a formulation of Peirce's law
Peirce : Prop
Peirce = ((Atom 0 ~> Atom 1) ~> Atom 0) ~> Atom 0

-- Natural deduction for implication fragment of intuitionistic propositional logic
data Proof : (ctx : List Prop) -> Prop -> Type where
  Ax : Elem a ctx -> Proof ctx a
  ImpIntro : Proof (a::ctx) b -> Proof ctx (a ~> b)
  ImpElim : Proof ctx a -> Proof ctx (a ~> b) -> Proof ctx b

infixr 5 |-
(|-) : List Prop -> Prop -> Type
(|-) = Proof

-- Therefore, our ultimate goal is to construct `Not ([] |- Peirce)`

-- Some proof examples
A : Prop
A = Atom 0

B : Prop
B = Atom 1

C : Prop
C = Atom 2

ex1 : [] |- A ~> B ~> A
ex1 = ImpIntro (ImpIntro (Ax (There Here)))

ex2 : [] |- (A ~> B ~> C) ~> (A ~> B) ~> A ~> C
ex2 = ImpIntro
        (ImpIntro
          (ImpIntro
            (ImpElim
              (ImpElim (Ax Here) (Ax (There Here)))
              (ImpElim (Ax Here) (Ax $ There $ There $ Here)))))

--------------------------------------------------------------------------------
--               Part 2: Kripke models for intuitionistic logic               --
--------------------------------------------------------------------------------

-- Next, we want to build the notion of Kripke models for our logic.
-- For the sake of simplicity, we shall represent finite models only,
-- as we are interested in showing that there are models such that
-- Peirce's law does not hold, and each formula that does not hold
-- does so in some finite model.

-- We will start by constructing useful machinery.

-- Relation is a type indexed by pairs of elements. We say that
-- relation between elements is satisfied iff the corresponding type
-- is inhabited.
Relation : Type -> Type
Relation ty = ty -> ty -> Type

-- Reflexivity means that each element has an identity arrow
0 Reflexive : Relation ty -> Type
Reflexive rel = (el : ty) -> rel el el

-- Transitivity means that arrows are composable
0 Transitive : Relation ty -> Type
Transitive rel = {a, b, c : ty} -> rel a b -> rel b c -> rel a c

-- Valuation asserts which values are true in some world
Valuation : Type -> Type
Valuation worlds = worlds -> List Nat

-- Monotonicity means that something is true in some world, it is true for any accessible world
0 Monotonic : Valuation ty -> Relation ty -> Type
Monotonic val rel = {a, b : ty} -> rel a b -> All (\x => Elem x (val b)) (val a)

-- If we know that the property is true for all elements, it is true for a specific element
getFromAll : Elem x xs -> All p xs -> p x
getFromAll Here (x :: _) = x
getFromAll (There prf) (_ :: xs) = getFromAll prf xs

-- Preorder is a reflexive transitive relation
record Preorder (rel : Relation ty) where
  constructor MkPreorder
  refl : Reflexive rel
  trans : Transitive rel

-- Here comes the model definition!
record KripkeModel where
  constructor MkKripke
  -- Kripke model consists of a world, which is a set of nodes...
  worlds : Type
  -- ... together with a preorder binary relation...
  rel : Relation worlds
  preorder : Preorder rel

  -- ... and a valuation for atomic variables...
  val : Valuation worlds
  -- ... that is monotonic.
  mono : Monotonic val rel

-- We need to define when something is true in the world of a model
data TrueInWorld : (m : KripkeModel) -> (w : m.worlds) -> Prop -> Type where
  -- Atom is true if it is evaluated as true
  AxTrue : Elem n (m.val w) -> TrueInWorld m w (Atom n)
  -- Implication `A -> B` is true if, for all accessible worlds, if A holds, then B holds
  ImpTrue : ((w' : m.worlds) ->
            m.rel w w' ->
            assert_total (TrueInWorld m w' a) ->  -- It doesn't look like I've abused this in any way,
                                                  -- but it's worth looking for a better formalisation
            TrueInWorld m w' b) ->
            TrueInWorld m w (a ~> b)

-- We say that a formula is true in model if it is true in all of its worlds
TrueInModel : (m : KripkeModel) -> Prop -> Type
TrueInModel m p = (w : m.worlds) -> TrueInWorld m w p

-- We say that a formula is an intuitionistic tautology if it is true in any model
IntuitionisticTautology : Prop -> Type
IntuitionisticTautology p = (m : KripkeModel) -> TrueInModel m p

-- We say that a formula in context is true if, in every model where all of the context
-- expressions are true, it is true as well
TrueWithContext : List Prop -> Prop -> Type
TrueWithContext ctx a = (m : KripkeModel) -> (w : m.worlds) -> All (TrueInWorld m w) ctx -> TrueInWorld m w a

-- If something is true in some world, then it must be true in any other accessible world
accessiblePreservesTrue : (m : KripkeModel) -> (w, w' : m.worlds) -> m.rel w w' -> TrueInWorld m w a -> TrueInWorld m w' a

infixr 5 ||-
(||-) : List Prop -> Prop -> Type
(||-) = TrueWithContext

-- Example: `A -> A` is an intuitionistic tautology
-- Essentially, we need to show that in any world where `A` holds, `A` holds
ex3 : [] ||- A ~> A
ex3 m _ w = ImpTrue $ \_, _, x => x

-- Example: `A -> B -> A` is an intuitionistic tautology
-- Here we need to use monotonicity of valuations
ex4 : [] ||- A ~> B ~> A
ex4 m _ w = ImpTrue $ \w', _, (AxTrue x) => ImpTrue $ \w'', p'', _ => AxTrue $ getFromAll x (m.mono p'')

-- If something is provable, then it is true in every model
0 provIsTrue : (ctx |- c) -> (ctx ||- c)
provIsTrue (Ax x) m w ctxTrue = getFromAll x ctxTrue
provIsTrue (ImpIntro x) m w ctxTrue
  = ImpTrue $ \w', acs, aTrue =>
      let ctxTrue = mapProperty (accessiblePreservesTrue m w w' acs) ctxTrue
          in provIsTrue x m w' (aTrue :: ctxTrue)
provIsTrue (ImpElim x y) m w ctxTrue
  = let ImpTrue impTrue = provIsTrue y m w ctxTrue
        in impTrue w (m.preorder.refl w) (provIsTrue x m w ctxTrue)


--------------------------------------------------------------------------------
--             Part 3: Building model that disproves Peirce's law             --
--------------------------------------------------------------------------------

-- Finally, we can build a model in which Peirce's law does not hold.
-- The model looks like the following:
--            t [A]
--            ^
--            |
--            f []
-- The idea behind the model is that, for implication `((A -> B) -> A) -> A` to
-- not hold, there should be a world where `(A -> B) -> A` holds,
-- but `A` does not. Here, `(A -> B) -> A` holds in both worlds: in `t`, there
-- is `A`, so any implication resulting in `A` would hold, and in `f` the
-- implication holds because `A -> B` does not. `A -> B` is not true because
-- there is an accessible world `t` in which `A` holds and `B` does not.
-- Therefore, `(A -> B) -> A` holds in every world, and `A` does not hold in `f`,
-- so Peirce's law does not hold in the model, making it a counterexample.

data Rel : Bool -> Bool -> Type where
  ReflexiveRel : Rel a a
  FalseTrue : Rel False True

0 monotonic : Monotonic (\t => if t then [0] else []) Rel
monotonic ReflexiveRel = case b of
                              False => []
                              True => [Here]
monotonic FalseTrue = []

0 noPeirceModel : KripkeModel
noPeirceModel = MkKripke Bool
                         Rel
                         (MkPreorder (\_ => ReflexiveRel)
                                     (\x, y => case x of
                                                    ReflexiveRel => y
                                                    FalseTrue => case y of
                                                                      ReflexiveRel => FalseTrue))
                         (\x => if x then [0] else [])
                         monotonic

0 peirceNotTrueInModel : Not (TrueInModel Main.noPeirceModel Peirce)
-- We know that implication is true in world `False`. That is bad, because there is a proof of
-- `(A -> B) -> A`, but no proof of `A`. We will use this to construct `_|_`.
peirceNotTrueInModel prf
  = let ImpTrue f = prf False in
        case f False (noPeirceModel.preorder.refl False) impLeftTrue of
             (AxTrue x) => uninhabited x where
  -- We need to show that `(A -> B) -> A` holds, i. e. that in every world where `A -> B` holds, `A` holds.
  impLeftTrue : TrueInWorld Main.noPeirceModel False ((A ~> B) ~> A)
  impLeftTrue = ImpTrue $ \w', acs, (ImpTrue ltrue) =>
                case w' of
                     -- `A -> B` shouldn't actually hold in this world, because in True `A` holds, but `B` does not.
                     -- We will use that to construct absurdity.
                     False => case ltrue True FalseTrue (AxTrue Here) of
                                   AxTrue (There x) impossible
                     -- World `True` is easy: `A` holds here by definition
                     True => AxTrue Here

-- Since there is a model that disproves Peirce's law, it is not intuitionistically true
0 peirceNotTrue : Not ([] ||- Peirce)
peirceNotTrue peirceTrue = peirceNotTrueInModel $ \w => peirceTrue noPeirceModel w []

-- Since it does not hold in every model, it must not be provable
0 peirceNotProvable : Not ([] |- Peirce)
peirceNotProvable peirceProof = peirceNotTrue (provIsTrue peirceProof)
-- quod erat demonstrandum ^^

