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

  ∼μ : ∀ {e e†}
    → e ∼ e†
    → (μ e) ∼ (μ e†)

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
strip-∼ (μ e) = ∼μ (strip-∼ e)

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
∼-functional (∼μ R) (∼μ R′) rewrite ∼-functional R R′ = refl

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
∼-strip (∼μ R) = cong μ (∼-strip R)

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
∼-trans (∼μ a∼b) (∼μ b∼c) = ∼μ (∼-trans a∼b b∼c)

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
⇝-∼ (I-μ) (∼μ R) = ∼μ R
-- ⇝-∼ (I-μ-⊤ M I) (∼δ (∼μ R)) = ∼μ (⇝-∼ I R)
-- ⇝-∼ (I-μ-⊥ ¬M I) (∼μ R) = ∼μ (⇝-∼ I R)

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
⇜-∼ (I-μ) (∼μ R) = ∼μ R
-- ⇜-∼ (I-μ-⊤ M I) (∼μ R) = ∼δ (∼μ (⇜-∼ I R))
-- ⇜-∼ (I-μ-⊥ ¬M I) (∼μ R) = (∼μ (⇜-∼ I R))

⇴-∼ : ∀ {eᵢ eₒ eₛ}
  → eᵢ ⇴ eₒ
  → eᵢ ∼ eₛ
  → eₒ ∼ eₛ
⇴-∼ O-` ∼` = ∼`
⇴-∼ (O-V V) ∼ = ∼
⇴-∼ (O-· Oₗ Oᵣ) (∼ₗ ∼· ∼ᵣ) = (⇴-∼ Oₗ ∼ₗ) ∼· (⇴-∼ Oᵣ ∼ᵣ)
⇴-∼ (O-+ Oₗ Oᵣ) (∼ₗ ∼+ ∼ᵣ) = (⇴-∼ Oₗ ∼ₗ) ∼+ (⇴-∼ Oᵣ ∼ᵣ)
⇴-∼ (O-φ O) (∼φ ∼) = ∼φ (⇴-∼ O ∼)
⇴-∼ (O-δᵢ _ O) (∼δ ∼) = ⇴-∼ O ∼
⇴-∼ (O-δₒ _ O) (∼δ (∼δ ∼)) = ⇴-∼ O (∼δ ∼)
⇴-∼ (O-δ _ O) (∼δ ∼) = ∼δ (⇴-∼ O ∼)
⇴-∼ (O-μ) (∼μ ∼) = ∼μ ∼

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
step-step
  (D-β-μ {e = e})
  (T-β-μ)
  C-∘
  rewrite sym (applyₑ-strip e 0 (μ e))
  = next (step D-β-μ T-β-μ C-∘) init

instr-step : ∀ {p a g l e e′ eᵢ eₒ}
  → (I : (p , a , g , l) ⊢ e ⇝ eᵢ)
  → (O : eᵢ ⇴ eₒ)
  → (strip eₒ) ↦* (strip e′)
  → (strip e) ↦* (strip e′)
instr-step (I-V V) (O-V V₁) S = S
instr-step I-` O-` S = S
instr-step (I-·-⊤ {eₗ = eₗ} {eᵣ = eᵣ} {eₗ′ = eₗ′} {eᵣ′ = eᵣ′} M Iₗ Iᵣ) (O-δ _ O) S
  rewrite ∼-strip (⇜-∼ Iₗ (strip-∼ eₗ))
  rewrite ∼-strip (⇜-∼ Iᵣ (strip-∼ eᵣ))
  rewrite ∼-strip (⇴-∼ O (strip-∼ (eₗ′ `· eᵣ′)))
  = S
instr-step (I-·-⊥ {eₗ = eₗ} {eᵣ = eᵣ} {eₗ′ = eₗ′} {eᵣ′ = eᵣ′} ¬M Iₗ Iᵣ) O S
  rewrite ∼-strip (⇜-∼ Iₗ (strip-∼ eₗ))
  rewrite ∼-strip (⇜-∼ Iᵣ (strip-∼ eᵣ))
  rewrite ∼-strip (⇴-∼ O (strip-∼ (eₗ′ `· eᵣ′)))
  = S
instr-step (I-+-⊤ {p} {a} {g} {l} {eₗ = eₗ} {eᵣ = eᵣ} {eₗ′ = eₗ′} {eᵣ′ = eᵣ′} M Iₗ Iᵣ) O S
  rewrite ∼-strip (⇜-∼ Iₗ (strip-∼ eₗ))
  rewrite ∼-strip (⇜-∼ Iᵣ (strip-∼ eᵣ))
  rewrite ∼-strip (⇴-∼ O (strip-∼ (δ (a , g , l) (eₗ′ `+ eᵣ′))))
  = S
instr-step (I-+-⊥ {eₗ = eₗ} {eᵣ = eᵣ} {eₗ′ = eₗ′} {eᵣ′ = eᵣ′} ¬M Iₗ Iᵣ) O S
  rewrite ∼-strip (⇜-∼ Iₗ (strip-∼ eₗ))
  rewrite ∼-strip (⇜-∼ Iᵣ (strip-∼ eᵣ))
  rewrite ∼-strip (⇴-∼ O (strip-∼ (eₗ′ `+ eᵣ′)))
  = S
instr-step (I-φ {p = p} {a} {g} {e = e} {e′ = e′} {e″ = e″} I₀ I₁) O S
  rewrite ∼-strip (⇜-∼ I₀ (strip-∼ e))
  rewrite ∼-strip (⇜-∼ I₁ (strip-∼ e′))
  rewrite ∼-strip (⇴-∼ O (strip-∼ (φ (p , a , g) e″)))
  = S
instr-step (I-δ {a = a} {g} {l} {e = e} {e′ = e′} I) O S
  rewrite ∼-strip (⇜-∼ I (strip-∼ e))
  rewrite ∼-strip (⇴-∼ O (strip-∼ (δ (a , g , l) e′)))
  = S
-- instr-step (I-μ-⊤ {a = a} {g} {l} {e = e} {e′ = e′} M I) O S
--   rewrite ∼-strip (⇜-∼ I (strip-∼ e))
--   rewrite ∼-strip (⇴-∼ O (strip-∼ (δ (a , g , l) (μ e′))))
--   = S
-- instr-step (I-μ-⊥ {e = e} {e′ = e′} ¬M I) O S
--   rewrite ∼-strip (⇜-∼ I (strip-∼ e))
--   rewrite ∼-strip (⇴-∼ O (strip-∼ (μ e′)))
--   = S
instr-step (I-μ) (O-μ) S = S

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
sim ∼` (step I-` O-` () A T C)
sim ∼` (step I-` (O-V V) () A T C)
sim ∼` (skip I-` O-` () A T C S)
sim ∼` (skip I-` (O-V V) () A T C S)
sim (∼ƛ R) (step (I-V V-ƛ) (O-V V-ƛ) () A T C)
sim (∼ƛ R) (skip (I-V V-ƛ) (O-V V-ƛ) () A T C S)
sim (∼ƛ R) (done V-ƛ) = leg (∼ƛ R) init
sim (_∼·_ Rₗ Rᵣ) (step {e′ = e′} I O D A T C)
    rewrite ∼-strip Rₗ
    rewrite ∼-strip Rᵣ
    = leg (strip-∼ e′) (instr-step {e′ = e′} I O (step-step D T C))
sim (Rₗ ∼· Rᵣ) (skip {e′ = e′} {e″ = e″} I O D A T C K)
    rewrite ∼-strip Rₗ
    rewrite ∼-strip Rᵣ
    with sim (strip-∼ e′) K
... | leg R′ S′
    rewrite ∼-strip R′
    = leg (strip-∼ e″) (step-trans (instr-step {e′ = e′} I O (step-step D T C)) S′)
sim ∼# (step (I-V V-#) (O-V V-#) () A T C)
sim ∼# (skip (I-V V-#) (O-V V-#) () A T C S)
sim ∼# (done V-#) = leg ∼# init
sim (_∼+_ Rₗ Rᵣ) (step {e′ = e′} I O D A T C)
    rewrite ∼-strip Rₗ
    rewrite ∼-strip Rᵣ
    = leg (strip-∼ e′) (instr-step {e′ = e′} I O (step-step D T C))
sim (Rₗ ∼+ Rᵣ) (skip {e′ = e′} {e″ = e″} I O D A T C K)
    rewrite ∼-strip Rₗ
    rewrite ∼-strip Rᵣ
    with sim (strip-∼ e′) K
... | leg R′ S′
    rewrite ∼-strip R′
    = leg (strip-∼ e″) (step-trans (instr-step {e′ = e′} I O (step-step D T C)) S′)
sim (∼φ R) (step {e′ = e′} I O D A T C)
    rewrite ∼-strip R
    = leg (strip-∼ e′) (instr-step {e′ = e′} I O (step-step D T C))
sim (∼φ R) (skip {e′ = e′} {e″ = e″} I O D A T C K)
    rewrite ∼-strip R
    with sim (strip-∼ e′) K
... | leg R′ S′
    rewrite ∼-strip R′
    = leg (strip-∼ e″) (step-trans (instr-step {e′ = e′} I O (step-step D T C)) S′)
sim (∼δ R) (step {e′ = e′} I O D A T C)
    rewrite ∼-strip R
    = leg (strip-∼ e′) (instr-step {e′ = e′} I O (step-step D T C))
sim (∼δ R) (skip {e′ = e′} {e″ = e″} I O D A T C K)
    rewrite ∼-strip R
    with sim (strip-∼ e′) K
... | leg R′ S′
    rewrite ∼-strip R′
    = leg (strip-∼ e″) (step-trans (instr-step {e′ = e′} I O (step-step D T C)) S′)
sim (∼μ R) (step {e′ = e′} I O D A T C)
    rewrite ∼-strip R
    = leg (strip-∼ e′) (instr-step {e′ = e′} I O (step-step D T C))
sim (∼μ R) (skip {e′ = e′} {e″ = e″} I O D A T C K)
    rewrite ∼-strip R
    with sim (strip-∼ e′) K
... | leg R′ S′
    rewrite ∼-strip R′
    = leg (strip-∼ e″) (step-trans (instr-step {e′ = e′} I O (step-step D T C)) S′)
