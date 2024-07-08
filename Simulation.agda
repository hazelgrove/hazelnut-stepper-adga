open import Base
open import Dynamics
open import Match
open import Statics
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃-syntax; _,_; _×_)
open import Data.Nat using (ℕ; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; subst₂; sym)
open import Relation.Nullary.Negation using (¬_)
open import Data.Empty using (⊥-elim)

module Simulation where

data _∼_ : Exp → Exp → Set where
  ∼` : ∀ {x}
    → (` x) ∼ (` x)

  ∼ƛ : ∀ {e e†}
    → e ∼ e†
    → (ƛ e) ∼ (ƛ e†)

  _∼·_ : ∀ {eₗ eᵣ eₗ† eᵣ†}
    → (Rₗ : eₗ ∼ eₗ†)
    → (Rᵣ : eᵣ ∼ eᵣ†)
    → (eₗ `· eᵣ) ∼ (eₗ† `· eᵣ†)

  ∼# : ∀ {n}
    → (# n) ∼ (# n)

  _∼+_ : ∀ {eₗ eᵣ eₗ† eᵣ†}
    → eₗ ∼ eₗ†
    → eᵣ ∼ eᵣ†
    → (eₗ `+ eᵣ) ∼ (eₗ† `+ eᵣ†)

  ∼φ : ∀ {f e e†}
    → e ∼ e†
    → (φ f e) ∼ e†

  ∼δ : ∀ {r e e†}
    → e ∼ e†
    → (δ r e) ∼ e†

-- ⇝-⇒ : ∀ {p a g l} {e : Exp} {c o}
--   → (p , a , g , l) ⊢ e ⇝ eᵢ
--   → eᵢ ⇒ c ⟨ o ⟩
--   → e ⇒ c ⟨ o ⟩
-- ⇝-⇒

strip-∼ : ∀ e
  → e ∼ strip e
strip-∼ (` i) = ∼`
strip-∼ (ƛ e) = ∼ƛ (strip-∼ e)
strip-∼ (eₗ `· eᵣ) = strip-∼ eₗ ∼· strip-∼ eᵣ
strip-∼ (# n) = ∼#
strip-∼ (eₗ `+ eᵣ) = strip-∼ eₗ ∼+ strip-∼ eᵣ
strip-∼ (φ f e) = ∼φ (strip-∼ e)
strip-∼ (δ r e) = ∼δ (strip-∼ e)

∼-functional : ∀ {e e† e†′}
  → e ∼ e†
  → e ∼ e†′
  → e† ≡ e†′
∼-functional ∼` ∼` = refl
∼-functional (∼ƛ R) (∼ƛ R′) rewrite ∼-functional R R′ = refl
∼-functional (Rₗ ∼· Rᵣ) (Rₗ′ ∼· Rᵣ′) rewrite ∼-functional Rₗ Rₗ′ rewrite ∼-functional Rᵣ Rᵣ′ = refl
∼-functional ∼# ∼# = refl
∼-functional (Rₗ ∼+ Rᵣ) (Rₗ′ ∼+ Rᵣ′) rewrite ∼-functional Rₗ Rₗ′ rewrite ∼-functional Rᵣ Rᵣ′ = refl
∼-functional (∼φ R) (∼φ R′) rewrite ∼-functional R R′ = refl
∼-functional (∼δ R) (∼δ R′) rewrite ∼-functional R R′ = refl

∼-strip : ∀ {e e†}
  → e ∼ e†
  → e† ≡ strip e
∼-strip ∼` = refl
∼-strip (∼ƛ R) = cong ƛ_ (∼-strip R)
∼-strip (Rₗ ∼· Rᵣ) = cong₂ _`·_ (∼-strip Rₗ) (∼-strip Rᵣ)
∼-strip ∼# = refl
∼-strip (Rₗ ∼+ Rᵣ) = cong₂ _`+_ (∼-strip Rₗ) (∼-strip Rᵣ)
∼-strip (∼φ R) = ∼-strip R
∼-strip (∼δ R) = ∼-strip R

∼-trans : ∀ {a b c}
  → a ∼ b
  → b ∼ c
  → a ∼ c
∼-trans ∼` ∼` = ∼`
∼-trans (∼ƛ R₀) (∼ƛ R₁) = (∼ƛ (∼-trans R₀ R₁))
∼-trans (a∼bₗ ∼· a∼bᵣ) (b∼cₗ ∼· b∼cᵣ) = ∼-trans a∼bₗ b∼cₗ ∼· ∼-trans a∼bᵣ b∼cᵣ
∼-trans ∼# ∼# = ∼#
∼-trans (a∼bₗ ∼+ a∼bᵣ) (b∼cₗ ∼+ b∼cᵣ) = ∼-trans a∼bₗ b∼cₗ ∼+ ∼-trans a∼bᵣ b∼cᵣ
∼-trans (∼φ a∼b) b∼c = ∼φ (∼-trans a∼b b∼c)
∼-trans (∼δ a∼b) b∼c = ∼δ (∼-trans a∼b b∼c)

⇝-∼ : ∀ {p a g l e eᵢ eₛ}
  → (p , a , g , l) ⊢ e ⇝ eᵢ
  → eᵢ ∼ eₛ
  → e ∼ eₛ
⇝-∼ (I-V V-ƛ) (∼ƛ R) = ∼ƛ R
⇝-∼ (I-V V-#) ∼# = ∼#
⇝-∼ I-` ∼` = ∼`
⇝-∼ (I-·-⊤ M Iₗ Iᵣ) (∼δ (Rₗ ∼· Rᵣ)) = (⇝-∼ Iₗ Rₗ) ∼· ⇝-∼ Iᵣ Rᵣ
⇝-∼ (I-·-⊥ ¬M Iₗ Iᵣ) (Rₗ ∼· Rᵣ) = (⇝-∼ Iₗ Rₗ) ∼· (⇝-∼ Iᵣ Rᵣ)
⇝-∼ (I-+-⊤ M Iₗ Iᵣ) (∼δ (Rₗ ∼+ Rᵣ)) = (⇝-∼ Iₗ Rₗ) ∼+ ⇝-∼ Iᵣ Rᵣ
⇝-∼ (I-+-⊥ ¬M Iₗ Iᵣ) (Rₗ ∼+ Rᵣ) = (⇝-∼ Iₗ Rₗ) ∼+ (⇝-∼ Iᵣ Rᵣ)
⇝-∼ (I-φ I₀ I₁) (∼φ R) = ∼φ (⇝-∼ I₀ (⇝-∼ I₁ R))
⇝-∼ (I-δ I) (∼δ R) = ∼δ (⇝-∼ I R)

⇜-∼ : ∀ {p a g l e eᵢ eₛ}
  → (p , a , g , l) ⊢ e ⇝ eᵢ
  → e ∼ eₛ
  → eᵢ ∼ eₛ
⇜-∼ (I-V V-ƛ) (∼ƛ R) = ∼ƛ R
⇜-∼ (I-V V-#) ∼# = ∼#
⇜-∼ I-` ∼` = ∼`
⇜-∼ (I-·-⊤ M Iₗ Iᵣ) (Rₗ ∼· Rᵣ) = ∼δ ((⇜-∼ Iₗ Rₗ) ∼· (⇜-∼ Iᵣ Rᵣ))
⇜-∼ (I-·-⊥ ¬M Iₗ Iᵣ) (Rₗ ∼· Rᵣ) = (⇜-∼ Iₗ Rₗ) ∼· (⇜-∼ Iᵣ Rᵣ)
⇜-∼ (I-+-⊤ M Iₗ Iᵣ) (Rₗ ∼+ Rᵣ) = ∼δ ((⇜-∼ Iₗ Rₗ) ∼+ (⇜-∼ Iᵣ Rᵣ))
⇜-∼ (I-+-⊥ ¬M Iₗ Iᵣ) (Rₗ ∼+ Rᵣ) = (⇜-∼ Iₗ Rₗ) ∼+ (⇜-∼ Iᵣ Rᵣ)
⇜-∼ (I-φ I₀ I₁) (∼φ R) = ∼φ (⇜-∼ I₁ (⇜-∼ I₀ R))
⇜-∼ (I-δ I) (∼δ R) = ∼δ (⇜-∼ I R)


data Leg (e′ : Exp) (e† : Exp) : Set where
  leg : ∀ {e′†}
    → e′ ∼ e′†
    → e† ↦* e′†
    → Leg e′ e†

step-step : ∀ {e e′ e₀ e₀′ ε₀}
  → (D : e ⇒ ε₀ ⟨ e₀ ⟩)
  → (T : e₀ —→ e₀′)
  → (C : e′ ⇐ (decay ε₀) ⟨ e₀′ ⟩)
  → (strip e) ↦* (strip e′)
step-step (D-ξ-·ₗ D) T (C-·ₗ C) with step-step D T C
step-step (D-ξ-·ₗ D) T (C-·ₗ C) | eₗ↦*eₗ′ = ↦*-cong-·ᵣ eₗ↦*eₗ′
step-step (D-ξ-·ᵣ V D) T (C-·ᵣ C) with step-step D T C
step-step (D-ξ-·ᵣ V D) T (C-·ᵣ C) | eᵣ↦*eᵣ′ = ↦*-cong-·ₗ (strip-value V) eᵣ↦*eᵣ′
step-step
  (D-β-· V-ƛ Vᵣ)
  (T-β-· {v = v} {e = e} V)
  C-∘
  rewrite sym (applyₑ-strip e 0 v)
  = next (step (D-β-· V-ƛ (strip-value V)) (T-β-· (strip-value V)) C-∘) init
step-step (D-ξ-+ₗ D) T (C-+ₗ C) = ↦*-cong-+ᵣ (step-step D T C)
step-step (D-ξ-+ᵣ V D) T (C-+ᵣ C) = ↦*-cong-+ₗ (strip-value V) (step-step D T C)
step-step (D-β-+ V-# V-#) T-β-+ C-∘ = next (step (D-β-+ V-# V-#) T-β-+ C-∘) init
step-step (D-ξ-φ D) T (C-φ C) = step-step D T C
step-step (D-β-φ V) (T-β-φ V₁) C-∘ = init
step-step (D-ξ-δ {a , 𝟙 , l} D) T C = step-step D T C
step-step (D-ξ-δ {a , ⋆ , l} D) T (C-δ C) = step-step D T C
step-step (D-β-δ V) (T-β-δ V₁) C-∘ = init

instr-step : ∀ {p a g l e e′ eᵢ}
  → (I : (p , a , g , l) ⊢ e ⇝ eᵢ)
  → (strip eᵢ) ↦* (strip e′)
  → (strip e) ↦* (strip e′)
instr-step (I-V V) S = S
instr-step I-` S = S
instr-step (I-·-⊤ {eₗ = eₗ} {eᵣ = eᵣ} M Iₗ Iᵣ) S
  rewrite ∼-strip (⇜-∼ Iₗ (strip-∼ eₗ))
  rewrite ∼-strip (⇜-∼ Iᵣ (strip-∼ eᵣ))
  = S
instr-step (I-·-⊥ {eₗ = eₗ} {eᵣ = eᵣ} ¬M Iₗ Iᵣ) S
  rewrite ∼-strip (⇜-∼ Iₗ (strip-∼ eₗ))
  rewrite ∼-strip (⇜-∼ Iᵣ (strip-∼ eᵣ))
  = S
instr-step (I-+-⊤ {eₗ = eₗ} {eᵣ = eᵣ} M Iₗ Iᵣ) S
  rewrite ∼-strip (⇜-∼ Iₗ (strip-∼ eₗ))
  rewrite ∼-strip (⇜-∼ Iᵣ (strip-∼ eᵣ))
  = S
instr-step (I-+-⊥ {eₗ = eₗ} {eᵣ = eᵣ} ¬M Iₗ Iᵣ) S
  rewrite ∼-strip (⇜-∼ Iₗ (strip-∼ eₗ))
  rewrite ∼-strip (⇜-∼ Iᵣ (strip-∼ eᵣ))
  = S
instr-step (I-φ {e = e} {e′ = e′} I₀ I₁) S
  rewrite ∼-strip (⇜-∼ I₀ (strip-∼ e))
  rewrite ∼-strip (⇜-∼ I₁ (strip-∼ e′))
  = S
instr-step (I-δ {e = e} I) S
  rewrite ∼-strip (⇜-∼ I (strip-∼ e))
  = S

step-trans : ∀ {e e′ e″}
  → e ↦* e′
  → e′ ↦* e″
  → e ↦* e″
step-trans init K′ = K′
step-trans (next S K) K′ = next S (step-trans K K′)

sim : ∀ {p a g l} {e e† e′ : Exp}
  → e ∼ e†
  → (p , a , g , l) ⊢ e ⇥ e′
  → Leg e′ e†
sim ∼` (step I-` () A T C)
sim ∼` (skip I-` () A T C S)
sim (∼ƛ R) (step (I-V V) () A T C)
sim (∼ƛ R) (skip (I-V V) () A T C S)
sim (∼ƛ R) (done V-ƛ) = leg (∼ƛ R) init
sim (_∼·_ Rₗ Rᵣ) (step {e′ = e′} I D A T C)
    rewrite ∼-strip Rₗ
    rewrite ∼-strip Rᵣ
    = leg (strip-∼ e′) (instr-step {e′ = e′} I (step-step D T C))
sim (Rₗ ∼· Rᵣ) (skip {e′ = e′} {e″ = e″} I D A T C K)
    rewrite ∼-strip Rₗ
    rewrite ∼-strip Rᵣ
    with sim (strip-∼ e′) K
... | leg R′ S′
    rewrite ∼-strip R′
    = leg (strip-∼ e″) (step-trans (instr-step {e′ = e′} I (step-step D T C)) S′)
sim ∼# (step (I-V V) () A T C)
sim ∼# (skip (I-V V) () A T C S)
sim ∼# (done V-#) = leg ∼# init
sim (_∼+_ Rₗ Rᵣ) (step {e′ = e′} I D A T C)
    rewrite ∼-strip Rₗ
    rewrite ∼-strip Rᵣ
    = leg (strip-∼ e′) (instr-step {e′ = e′} I (step-step D T C))
sim (Rₗ ∼+ Rᵣ) (skip {e′ = e′} {e″ = e″} I D A T C K)
    rewrite ∼-strip Rₗ
    rewrite ∼-strip Rᵣ
    with sim (strip-∼ e′) K
... | leg R′ S′
    rewrite ∼-strip R′
    = leg (strip-∼ e″) (step-trans (instr-step {e′ = e′} I (step-step D T C)) S′)
sim (∼φ R) (step {e′ = e′} I D A T C)
    rewrite ∼-strip R
    = leg (strip-∼ e′) (instr-step {e′ = e′} I (step-step D T C))
sim (∼φ R) (skip {e′ = e′} {e″ = e″} I D A T C K)
    rewrite ∼-strip R
    with sim (strip-∼ e′) K
... | leg R′ S′
    rewrite ∼-strip R′
    = leg (strip-∼ e″) (step-trans (instr-step {e′ = e′} I (step-step D T C)) S′)
sim (∼δ R) (step {e′ = e′} I D A T C)
    rewrite ∼-strip R
    = leg (strip-∼ e′) (instr-step {e′ = e′} I (step-step D T C))
sim (∼δ R) (skip {e′ = e′} {e″ = e″} I D A T C K)
    rewrite ∼-strip R
    with sim (strip-∼ e′) K
... | leg R′ S′
    rewrite ∼-strip R′
    = leg (strip-∼ e″) (step-trans (instr-step {e′ = e′} I (step-step D T C)) S′)
