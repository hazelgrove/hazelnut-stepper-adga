open import Base
open import Dynamics
open import Match
open import Statics
open import Data.Product using (∃-syntax; _,_; _×_)
open import Data.Nat using (ℕ; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; subst₂; sym)
open import Relation.Nullary.Negation using (¬_)

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

strip-value : ∀ {v : Exp}
  → v value
  → strip v value
strip-value V-ƛ = V-ƛ
strip-value V-# = V-#

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


data Arm (p : Pat) (a : Act) (g : Gas) (l : ℕ) (e : Exp) (e† : Exp) (e′ : Exp) : Set where
  arm : (e ∼ e†)
    → (p , a , g , l) ⊢ e ⇥ e′
    → Arm p a g l e e† e′

data Leg (e′ : Exp) (e† : Exp) : Set where
  leg : ∀ {e′†}
    → e′ ∼ e′†
    → e† ↦* e′†
    → Leg e′ e† 


sim : ∀ {p a g l} {e e† e′ : Exp} {τ : Typ}
  → ((e ∼ e†) × ((p , a , g , l) ⊢ e ⇥ e′))
  → ∃[ e′† ](e′ ∼ e′† × e† ↦* e′†)
sim (∼ƛ R , step (I-V V-ƛ) () A T C)
sim (∼ƛ R , skip (I-V V-ƛ) () A T C S)
sim (∼ƛ {e} {e†} R , done V-ƛ) = ƛ e† , ∼ƛ R , init
-- sim {g = 𝟙}
--   ( _∼·_ {eₗ} {eᵣ} {eₗ†} {eᵣ†} eₗ∼eₗ† eᵣ∼eᵣ†
--   , step
--     (I-·-⊤ {eᵣ′ = eᵣ′} M Iₗ Iᵣ)
--     (D-ξ-δ (D-ξ-·ₗ D))
--     (¬F , A-Δ-> lₑ>l (A-·-l A))
--     T
--     (C-·ₗ C)
--   ) with sim (eₗ∼eₗ† , step Iₗ D (¬F , A) T C)
-- ... | eₗ′† , eₗ′∼eₗ′† , eₗ†↦*eₗ′†
--     rewrite ∼-strip eᵣ∼eᵣ†
--     = eₗ′† `· strip eᵣ
--     , (eₗ′∼eₗ′† ∼· ⇜-∼ Iᵣ (strip-∼ eᵣ))
--     , ↦*-cong-·ᵣ (strip eᵣ) eₗ†↦*eₗ′†
-- sim {g = ⋆}
--   ( _∼·_ {eₗ} {eᵣ} {eₗ†} {eᵣ†} eₗ∼eₗ† eᵣ∼eᵣ†
--   , step
--     (I-·-⊤ M Iₗ Iᵣ)
--     (D-ξ-δ (D-ξ-·ₗ D))
--     (¬F , A-Δ-> lₑ>l (A-·-l A))
--     T
--     (C-δ (C-·ₗ C))
--   ) with sim (eₗ∼eₗ† , step Iₗ D (¬F , A) T C)
-- ... | eₗ′† , eₗ′∼eₗ′† , eₗ†↦*eₗ′†
--     rewrite ∼-strip eᵣ∼eᵣ†
--     = eₗ′† `· strip eᵣ
--     , ∼δ ((eₗ′∼eₗ′† ∼· ⇜-∼ Iᵣ (strip-∼ eᵣ)))
--     , ↦*-cong-·ᵣ (strip eᵣ) eₗ†↦*eₗ′†
-- sim {g = 𝟙} (_∼·_ {eₗ} {eᵣ} {eₗ†} {eᵣ†} eₗ∼eₗ† eᵣ∼eᵣ† , step (I-·-⊤ M Iₗ Iᵣ) (D-ξ-δ (D-ξ-·ₗ D)) (¬F , A-Δ-≤ x (A-·-l A)) T (C-·ₗ C)) with sim (eₗ∼eₗ† , step Iₗ D (¬F , A) T C)
-- ... | eₗ′† , eₗ′∼eₗ′† , eₗ†↦*eₗ′† rewrite ∼-strip eᵣ∼eᵣ† = eₗ′† `· strip eᵣ , ((eₗ′∼eₗ′† ∼· ⇜-∼ Iᵣ (strip-∼ eᵣ))) , ↦*-cong-·ᵣ (strip eᵣ) eₗ†↦*eₗ′†
-- sim {g = ⋆} (_∼·_ {eₗ} {eᵣ} {eₗ†} {eᵣ†} eₗ∼eₗ† eᵣ∼eᵣ† , step (I-·-⊤ M Iₗ Iᵣ) (D-ξ-δ (D-ξ-·ₗ D)) (¬F , A-Δ-≤ x (A-·-l A)) T (C-δ (C-·ₗ C))) with sim (eₗ∼eₗ† , step Iₗ D (¬F , A) T C)
-- ... | eₗ′† , eₗ′∼eₗ′† , eₗ†↦*eₗ′† rewrite ∼-strip eᵣ∼eᵣ† = eₗ′† `· strip eᵣ , ∼δ ((eₗ′∼eₗ′† ∼· ⇜-∼ Iᵣ (strip-∼ eᵣ))) , ↦*-cong-·ᵣ (strip eᵣ) eₗ†↦*eₗ′†
-- sim {g = 𝟙} (_∼·_ {eₗ} {eᵣ} {eₗ†} {eᵣ†} eₗ∼eₗ† eᵣ∼eᵣ† , step (I-·-⊤ M Iₗ Iᵣ) (D-ξ-δ (D-ξ-·ᵣ V D)) (¬F , A-Δ-> x (A-·-r A)) T (C-·ᵣ C)) with sim (eᵣ∼eᵣ† , step Iᵣ D (¬F , A) T C)
-- ... | eᵣ′† , eᵣ′∼eᵣ′† , eᵣ†↦*eᵣ′† rewrite ∼-strip eₗ∼eₗ† with Iₗ
-- ... | I-V Vₗ = strip eₗ `· eᵣ′† , (⇜-∼ Iₗ (strip-∼ eₗ) ∼· eᵣ′∼eᵣ′†) , ↦*-cong-·ₗ (strip-value V) eᵣ†↦*eᵣ′†
-- sim {g = ⋆} (_∼·_ {eₗ} {eᵣ} {eₗ†} {eᵣ†} eₗ∼eₗ† eᵣ∼eᵣ† , step (I-·-⊤ M Iₗ Iᵣ) (D-ξ-δ (D-ξ-·ᵣ V D)) (¬F , A-Δ-> x (A-·-r A)) T (C-δ (C-·ᵣ C))) with sim (eᵣ∼eᵣ† , step Iᵣ D (¬F , A) T C)
-- ... | eᵣ′† , eᵣ′∼eᵣ′† , eᵣ†↦*eᵣ′† rewrite ∼-strip eₗ∼eₗ† with Iₗ
-- ... | I-V Vₗ = strip eₗ `· eᵣ′† , ∼δ (⇜-∼ Iₗ (strip-∼ eₗ) ∼· eᵣ′∼eᵣ′†) , ↦*-cong-·ₗ (strip-value V) eᵣ†↦*eᵣ′†
-- sim {g = 𝟙} (_∼·_ {eₗ} {eᵣ} {eₗ†} {eᵣ†} eₗ∼eₗ† eᵣ∼eᵣ† , step (I-·-⊤ M Iₗ Iᵣ) (D-ξ-δ (D-ξ-·ᵣ V D)) (¬F , A-Δ-≤ x (A-·-r A)) T (C-·ᵣ C)) with sim (eᵣ∼eᵣ† , step Iᵣ D (¬F , A) T C)
-- ... | eᵣ′† , eᵣ′∼eᵣ′† , eᵣ†↦*eᵣ′† rewrite ∼-strip eₗ∼eₗ† with Iₗ
-- ... | I-V Vₗ = strip eₗ `· eᵣ′† , (⇜-∼ Iₗ (strip-∼ eₗ) ∼· eᵣ′∼eᵣ′†) , ↦*-cong-·ₗ (strip-value V) eᵣ†↦*eᵣ′†
-- sim {g = ⋆} (_∼·_ {eₗ} {eᵣ} {eₗ†} {eᵣ†} eₗ∼eₗ† eᵣ∼eᵣ† , step (I-·-⊤ M Iₗ Iᵣ) (D-ξ-δ (D-ξ-·ᵣ V D)) (¬F , A-Δ-≤ x (A-·-r A)) T (C-δ (C-·ᵣ C))) with sim (eᵣ∼eᵣ† , step Iᵣ D (¬F , A) T C)
-- ... | eᵣ′† , eᵣ′∼eᵣ′† , eᵣ†↦*eᵣ′† rewrite ∼-strip eₗ∼eₗ† with Iₗ
-- ... | I-V Vₗ = strip eₗ `· eᵣ′† , ∼δ (⇜-∼ Iₗ (strip-∼ eₗ) ∼· eᵣ′∼eᵣ′†) , ↦*-cong-·ₗ (strip-value V) eᵣ†↦*eᵣ′†
-- sim {g = 𝟙}
--   ( _∼·_ {eₗ} {eᵣ} {eₗ†} {eᵣ†} eₗ∼eₗ† eᵣ∼eᵣ†
--   , step
--     (I-·-⊤ M (I-V (V-ƛ {e = e})) (I-V Vᵢ))
--     (D-ξ-δ (D-β-· V-ƛ Vᵣ))
--     (¬F , A-Δ-> x A-∘)
--     (T-β-· V)
--     (C-∘)
--   )
--   rewrite ∼-strip eₗ∼eₗ†
--   rewrite ∼-strip eᵣ∼eᵣ†
--   = (applyₑ (strip e) 0 (strip eᵣ))
--   , subst₂ _∼_ refl (sym (applyₑ-strip e 0 eᵣ)) (strip-∼ (applyₑ e 0 eᵣ))
--   , next (step (D-β-· V-ƛ (strip-value V)) (T-β-· (strip-value Vᵣ)) C-∘) init
-- sim {g = 𝟙}
--   ( _∼·_ {eₗ} {eᵣ} {eₗ†} {eᵣ†} eₗ∼eₗ† eᵣ∼eᵣ†
--   , step
--     (I-·-⊤ M (I-V (V-ƛ {e = e})) (I-V Vᵢ))
--     (D-ξ-δ (D-β-· V-ƛ Vᵣ))
--     (¬F , A-Δ-≤ x A-∘)
--     (T-β-· V)
--     C-∘
--   )
--   rewrite ∼-strip eₗ∼eₗ†
--   rewrite ∼-strip eᵣ∼eᵣ†
--   = (applyₑ (strip e) 0 (strip eᵣ))
--   , subst₂ _∼_ refl (sym (applyₑ-strip e 0 eᵣ)) (strip-∼ (applyₑ e 0 eᵣ))
--   , next (step (D-β-· V-ƛ (strip-value V)) (T-β-· (strip-value Vᵣ)) C-∘) init
-- sim {g = ⋆}
--   ( _∼·_ {eₗ} {eᵣ} {eₗ†} {eᵣ†} eₗ∼eₗ† eᵣ∼eᵣ†
--   , step (I-·-⊤ M (I-V (V-ƛ {e = e})) (I-V Vᵢ)) (D-ξ-δ (D-β-· V-ƛ Vᵣ)) (¬F , A-Δ-> x A-∘) (T-β-· V) (C-δ C-∘)
--   )
--   rewrite ∼-strip eₗ∼eₗ†
--   rewrite ∼-strip eᵣ∼eᵣ†
--   = (applyₑ (strip e) 0 (strip eᵣ))
--   , (∼δ (subst₂ _∼_ refl (sym (applyₑ-strip e 0 eᵣ)) (strip-∼ (applyₑ e 0 eᵣ))))
--   , next (step (D-β-· V-ƛ (strip-value V)) (T-β-· (strip-value V)) C-∘) init
-- sim {g = ⋆} (_∼·_ {eₗ} {eᵣ} {eₗ†} {eᵣ†} eₗ∼eₗ† eᵣ∼eᵣ† , step (I-·-⊤ M (I-V (V-ƛ {e = e})) (I-V Vᵢ)) (D-ξ-δ (D-β-· V-ƛ Vᵣ)) (¬F , A-Δ-≤ x A-∘) (T-β-· V) (C-δ C-∘))
--   rewrite ∼-strip eₗ∼eₗ†
--   rewrite ∼-strip eᵣ∼eᵣ†
--   = (applyₑ (strip e) 0 (strip eᵣ))
--   , (∼δ (subst₂ _∼_ refl (sym (applyₑ-strip e 0 eᵣ)) (strip-∼ (applyₑ e 0 eᵣ))))
--   , next (step (D-β-· V-ƛ (strip-value V)) (T-β-· (strip-value V)) C-∘) init
sim {g = g} (_∼·_ {eₗ} {eᵣ} {eₗ†} {eᵣ†} eₗ∼eₗ† eᵣ∼eᵣ† , step (I-·-⊤ ¬M Iₗ Iᵣ) D (¬F , A) T C) = {!!}
sim {g = g} (_∼·_ {eₗ} {eᵣ} {eₗ†} {eᵣ†} eₗ∼eₗ† eᵣ∼eᵣ† , step (I-·-⊥ ¬M Iₗ Iᵣ) D (¬F , A) T C) = {!!}
sim {g = g} (_∼·_ {eₗ} {eᵣ} {eₗ†} {eᵣ†} eₗ∼eₗ† eᵣ∼eᵣ† , skip (I-·-⊤ M I I₁) D A T C S) = {!!}
sim {g = g} (_∼·_ {eₗ} {eᵣ} {eₗ†} {eᵣ†} eₗ∼eₗ† eᵣ∼eᵣ† , skip (I-·-⊥ ¬M I I₁) D A T C S) = {!!}
sim {g = g} (∼# , S) = {!!}
sim {g = g} ((R ∼+ R₁) , S) = {!!}
sim {g = g} (∼φ R , S) = {!!}
sim {g = g} (∼δ R , S) = {!!}
