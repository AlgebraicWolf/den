module Kripke where

open import Propositions

data 𝔹 : Set where
  true : 𝔹
  false : 𝔹

data _⊎_ (a : Set) (b : Set) : Set where
  inj₁ : a → a ⊎ b
  inj₂ : b → a ⊎ b

data _×_ (a : Set) (b : Set) : Set where
  _⨾_ : a → b → a × b

projₗ : ∀{a b} → a × b → a
projₗ (x ⨾ _) = x

projᵣ : ∀{a b} → a × b → b
projᵣ (_ ⨾ y) = y

-- Boolean truthfullness, reflected as a proposition
data So : 𝔹 → Set where
  Oh : So true 

-- Behold! Kripke model is...
record Kripke : Set₁ where
  field
    -- ...a type of worlds...
    world : Set
    -- ...equipped with a reflexive and transitive accessibility relation...
    _↝_ : world → world → Set
    reflexive : ∀ el → el ↝ el
    transitive : ∀ a b c → a ↝ b → b ↝ c → a ↝ c
    -- ...and a valuation function, 
    -- assigning boolean variables to atomic propositions
    -- in each world in the type... 
    val : world → ℕ → 𝔹
    -- and monotonically increasing w.r.t. the accessibility relation
    monotonic : ∀ w₁ w₂ p → w₁ ↝ w₂ → So (val w₁ p) → So (val w₂ p)

[_]_↝_ : (m : Kripke) → Kripke.world m → Kripke.world m → Set
[ m ] p ↝ q = Kripke._↝_ m p q

-- A proposition is true in some world of a Kripke model when
[_,_]⊩_ : (m : Kripke) → Kripke.world m → Prop → Set
-- For an atomic proposition, it should be truthfully valuated
[ m , w ]⊩ (atom x) = So (Kripke.val m w x)
-- For implication, the conclusion should be true in any accessbile world,
-- shall the premise be true as wellm
[ m , w ]⊩ (p ⇒ q) = ∀{w'} → [ m ] w ↝ w' → [ m , w' ]⊩ p → [ m , w' ]⊩ q
-- For conjunction, both sides should be true
[ m , w ]⊩ (p ∧ q) = ([ m , w ]⊩ p) × ([ m , w ]⊩ q)
-- For disjunction, either side should be true
[ m , w ]⊩ (p ∨ q) = ([ m , w ]⊩ p) ⊎ ([ m , w ]⊩ q)

-- Truthfullness in some world is preserved under accessibility relation
⊩↝⊩ : ∀{m w₁ w₂ p} → [ m ] w₁ ↝ w₂ → [ m , w₁ ]⊩ p → [ m , w₂ ]⊩ p
⊩↝⊩ {m} {w₁} {w₂} {atom x} w₁↝w₂ w₁⊩p =
  Kripke.monotonic m w₁ w₂ x w₁↝w₂ w₁⊩p
⊩↝⊩ {m} {w₁} {w₂} {p ⇒ q} w₁↝w₂ w₁⊩p {w₃} w₂↝w₃ =
  w₁⊩p (Kripke.transitive m w₁ w₂ w₃ w₁↝w₂ w₂↝w₃)
⊩↝⊩ {m} {w₁} {w₂} {p ∧ q} w₁↝w₂ w₁⊩p∧q =
  (⊩↝⊩ w₁↝w₂ (projₗ w₁⊩p∧q)) ⨾ (⊩↝⊩ w₁↝w₂ (projᵣ w₁⊩p∧q))
⊩↝⊩ {m} {w₁} {w₂} {p ∨ q} w₁↝w₂ (inj₁ w₁⊩p) = inj₁ (⊩↝⊩ w₁↝w₂ w₁⊩p)
⊩↝⊩ {m} {w₁} {w₂} {p ∨ q} w₁↝w₂ (inj₂ w₁⊩q) = inj₂ (⊩↝⊩ w₁↝w₂ w₁⊩q)

-- A formula is said to be validated in some world under some context
-- if it is true when the premise is true
[_,_]_⊩_ : (m : Kripke) → Kripke.world m → Ctx → Prop → Set
[ m , w ] Γ ⊩ p = All ([ m , w ]⊩_) Γ → [ m , w ]⊩ p

-- A formula is validated in a model if it is true in every world of the model
⟨_⟩_⊩_ : (m : Kripke) → Ctx → Prop → Set
⟨ m ⟩ Γ ⊩ p = (w : Kripke.world m) → [ m , w ] Γ ⊩ p

-- At last, there is validity in every model
_⊩_ : Ctx -> Prop -> Set₁
Γ ⊩ p = (m : Kripke) → ⟨ m ⟩ Γ ⊩ p

-- Every provable formula should be validated in any model
⊢-imp-⊩ : ∀{Γ p} → Γ ⊢ p → Γ ⊩ p
⊢-imp-⊩ {Γ} {p} (ax x) m w ctxTrue = getFromAll ctxTrue x
⊢-imp-⊩ {Γ} {.(_ ⇒ _)} (⇒-intro Γ,p⊢q) m w ctxTrue {w'} w↝w' ⊩p =
  ⊢-imp-⊩ Γ,p⊢q m w' (mapProperty (⊩↝⊩ w↝w') ctxTrue , ⊩p)
⊢-imp-⊩ {Γ} {q} (⇒-elim Γ⊢p⇒q Γ⊢p) m w ctxTrue = 
  ⊢-imp-⊩ Γ⊢p⇒q m w ctxTrue (Kripke.reflexive m w) (⊢-imp-⊩ Γ⊢p m w ctxTrue)
⊢-imp-⊩ {Γ} {.(_ ∧ _)} (∧-intro Γ⊢p Γ⊢p₁) m w ctxTrue =
  ⊢-imp-⊩ Γ⊢p m w ctxTrue ⨾ ⊢-imp-⊩ Γ⊢p₁ m w ctxTrue
⊢-imp-⊩ {Γ} {p} (∧-elimₗ Γ⊢p) m w ctxTrue = projₗ (⊢-imp-⊩ Γ⊢p m w ctxTrue)
⊢-imp-⊩ {Γ} {p} (∧-elimᵣ Γ⊢p) m w ctxTrue = projᵣ (⊢-imp-⊩ Γ⊢p m w ctxTrue)
⊢-imp-⊩ {Γ} {.(_ ∨ _)} (∨-introₗ Γ⊢p) m w ctxTrue = inj₁ (⊢-imp-⊩ Γ⊢p m w ctxTrue)
⊢-imp-⊩ {Γ} {.(_ ∨ _)} (∨-introᵣ Γ⊢p) m w ctxTrue = inj₂ (⊢-imp-⊩ Γ⊢p m w ctxTrue)
⊢-imp-⊩ {Γ} {r} (∨-elim Γ⊢p∨q Γ,p⊢r Γ,q⊢r) m w ctxTrue with (⊢-imp-⊩ Γ⊢p∨q m w ctxTrue)
... | inj₁ ⊩p = ⊢-imp-⊩ Γ,p⊢r m w (ctxTrue , ⊩p)  
... | inj₂ ⊩q = ⊢-imp-⊩ Γ,q⊢r m w (ctxTrue , ⊩q)  