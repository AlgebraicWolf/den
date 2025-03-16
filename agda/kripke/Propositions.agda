module Propositions where

infix 20 _⊢_
infixl 21 _,_
infixl 23 _∧_
infixl 22 _∨_
infixr 21 _⇒_

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

-- Propositions of intuitionistic logic
data Prop : Set where
  atom : ℕ → Prop
  _⇒_ : Prop → Prop → Prop
  _∧_ : Prop → Prop → Prop
  _∨_ : Prop → Prop → Prop

-- A context is a list of propositions
data Ctx : Set where
  emp : Ctx
  _,_ : Ctx → Prop → Ctx

-- Proof that a predicate holds for all propositions in context
data All (p : Prop → Set) : Ctx → Set where
  emp : All p emp
  _,_ : ∀ {Γ x} → All p Γ → p x → All p (Γ , x)

-- Proof transformation
mapProperty : ∀{ctx p q} → (f : ∀{x} → p x → q x) → All p ctx → All q ctx
mapProperty f emp = emp
mapProperty f (ctx , x) = mapProperty f ctx , f x

-- De Bruijn index of a proposition in context
data _∈_ : Prop → Ctx → Set where
  here : ∀{Γ x} → x ∈ Γ , x
  there : ∀{Γ x y} → x ∈ Γ → x ∈ Γ , y

-- Fetch a proof by de Bruijn index
getFromAll : ∀{Γ p x} → All p Γ → x ∈ Γ → p x
getFromAll (prfs , prf) here = prf
getFromAll (prfs , _) (there idx) = getFromAll prfs idx

-- Natural deduction proofs of propositions
data _⊢_ : Ctx → Prop → Set where
  ax : ∀{Γ p} 
    → p ∈ Γ 
      -------
    → Γ ⊢ p
  
  ⇒-intro : ∀{Γ p q} 
    → Γ , p ⊢ q
      ------------
    → Γ ⊢ p ⇒ q
  
  ⇒-elim : ∀{Γ p q} 
    → Γ ⊢ p ⇒ q → Γ ⊢ p 
      ---------------------
            → Γ ⊢ q

  ∧-intro : ∀{Γ p q}
    → Γ ⊢ p → Γ ⊢ q
      ----------------
    →   Γ ⊢ p ∧ q

  ∧-elimₗ : ∀{Γ p q}
    → Γ ⊢ p ∧ q
      -----------
    →   Γ ⊢ p

  ∧-elimᵣ : ∀{Γ p q}
    → Γ ⊢ p ∧ q
      -----------
    →   Γ ⊢ q

  ∨-introₗ : ∀{Γ p q}
    →   Γ ⊢ p
      -----------
    → Γ ⊢ p ∨ q
  
  ∨-introᵣ : ∀{Γ p q}
    →   Γ ⊢ q
      -----------
    → Γ ⊢ p ∨ q 

  ∨-elim : ∀{Γ p q r}
    → Γ ⊢ p ∨ q → Γ , p ⊢ r → Γ , q ⊢ r
      -------------------------------------
    →              Γ ⊢ r

module ⊢-examples where
  A : Prop
  A = atom zero

  B : Prop
  B = atom (suc zero)

  C : Prop
  C = atom (suc (suc zero))

  ex1 : emp ⊢ A ∨ B ⇒ B ∨ A
  ex1 = ⇒-intro (∨-elim (ax here) (∨-introᵣ (ax here)) (∨-introₗ (ax here)))

  ex2 : emp ⊢ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
  ex2 = ⇒-intro
          (⇒-intro
            (⇒-intro 
              (⇒-elim 
                (⇒-elim (ax (there (there here))) (ax here))
                (⇒-elim (ax (there here)) (ax here)))))