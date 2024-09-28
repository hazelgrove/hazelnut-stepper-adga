module Progress where

open import Base
open import Match
open import Statics
open import Dynamics
open import Preservation
open import Data.Nat using (ℕ; _+_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Nullary using (Dec; yes; no; ¬_; _×-dec_)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≡_; cong; cong₂; subst; subst₂; sym; trans)
open import Function.Bundles using (_↔_; Inverse)
open import Data.Empty using (⊥-elim)


data _⊢_⇥′_ : Pat × Act × Gas × ℕ → Exp → Exp → Set where
  step : ∀ {p a g l e eᵢ e′ e₀ e₀′ ε₀}
    → (I : (p , a , g , l) ⊢ e ⇝ eᵢ)
    → (D : eᵢ ⇒ ε₀ ⟨ e₀ ⟩)
    → (A : (a , l) ⊢ ε₀ ⊣ ∥)
    → (T : e₀ —→ e₀′)
    → (C : e′ ⇐ (decay ε₀) ⟨ e₀′ ⟩)
    → (p , a , g , l) ⊢ e ⇥′ e′

  skip : ∀ {p a g l e eᵢ e′ e″ e₀ e₀′ ε₀}
    → (R : (p , a , g , l) ⊢ e ⇥′ e′)
    → (I : (p , a , g , l) ⊢ e′ ⇝ eᵢ)
    → (D : eᵢ ⇒ ε₀ ⟨ e₀ ⟩)
    → (A : e₀ filter ⊎ (a , l) ⊢ ε₀ ⊣ ⊳)
    → (T : e₀ —→ e₀′)
    → (C : e″ ⇐ (decay ε₀) ⟨ e₀′ ⟩)
    → (p , a , g , l) ⊢ e ⇥′ e″

  done : ∀ {p a g l v}
    → v value
    → (p , a , g , l) ⊢ v ⇥′ v

data Progress_under_ : Exp → Pat × Act × Gas × ℕ → Set where
  P : ∀ {p a g l e e′}
    → e ⇥ e′
    → Progress e under (p , a , g , l)

data ⇒-Progress : Exp → Set where
  ⇒-V : ∀ {v}
    → (V : v value)
    → ⇒-Progress v

  ⇒-D : ∀ {e c o}
    → (D : e ⇒ c ⟨ o ⟩)
    → ⇒-Progress e

⇝-progress : ∀ p a g l {e τ}
  → ∅ ⊢ e ∶ τ
  → ∃[ e′ ]((p , a , g , l) ⊢ e ⇝ e′ × ∅ ⊢ e′ ∶ τ)
⇝-progress p a g l {e} ⊢ = instr p a g l e , ⇝-instr p a g l e , ⇝-preserve ⊢ (⇝-instr p a g l e)

value-⇝-value : ∀ {p a g l v v′}
  → v value
  → (p , a , g , l) ⊢ v ⇝ v′
  → v′ value
value-⇝-value V-ƛ (I-V V-ƛ) = V-ƛ
value-⇝-value V-# (I-V V-#) = V-#

¬value-⇝-¬value : ∀ {p a g l v v′}
  → ¬ (v value)
  → (p , a , g , l) ⊢ v ⇝ v′
  → ¬ (v′ value)
¬value-⇝-¬value ¬V (I-V V) = λ V → ¬V V
¬value-⇝-¬value ¬V (I-`) ()
¬value-⇝-¬value ¬V (I-·-⊤ _ _ _) ()
¬value-⇝-¬value ¬V (I-·-⊥ _ _ _) ()
¬value-⇝-¬value ¬V (I-+-⊤ _ _ _) ()
¬value-⇝-¬value ¬V (I-+-⊥ _ _ _) ()
¬value-⇝-¬value ¬V (I-φ _ _) ()
¬value-⇝-¬value ¬V (I-δ _) ()

value-⇜-value : ∀ {p a g l v v′}
  → v′ value
  → (p , a , g , l) ⊢ v ⇝ v′
  → v value
value-⇜-value V-ƛ (I-V V-ƛ) = V-ƛ
value-⇜-value V-# (I-V V-#) = V-#

⇒-progress : ∀ {e τ}
  → ∅ ⊢ e ∶ τ
  → ⇒-Progress e
⇒-progress (⊢-ƛ ⊢) = ⇒-V V-ƛ
⇒-progress (⊢-· ⊢ₗ ⊢ᵣ) with ⇒-progress ⊢ₗ with ⇒-progress ⊢ᵣ
⇒-progress (⊢-· {eₗ = eₗ} {eᵣ = eᵣ} ⊢ₗ ⊢ᵣ) | ⇒-V Vₗ | ⇒-V Vᵣ = ⇒-D (D-β-· Vₗ Vᵣ)
⇒-progress (⊢-· {eₗ = eₗ} {eᵣ = eᵣ} ⊢ₗ ⊢ᵣ) | ⇒-V Vₗ | ⇒-D Dᵣ = ⇒-D (D-ξ-·ᵣ Vₗ Dᵣ)
⇒-progress (⊢-· {eₗ = eₗ} {eᵣ = eᵣ} ⊢ₗ ⊢ᵣ) | ⇒-D Dₗ | ⇒-V Vᵣ = ⇒-D (D-ξ-·ₗ Dₗ)
⇒-progress (⊢-· {eₗ = eₗ} {eᵣ = eᵣ} ⊢ₗ ⊢ᵣ) | ⇒-D Dₗ | ⇒-D Dᵣ = ⇒-D (D-ξ-·ₗ Dₗ)
⇒-progress (⊢-+ ⊢ₗ ⊢ᵣ) with ⇒-progress ⊢ₗ with ⇒-progress ⊢ᵣ
⇒-progress (⊢-+ {eₗ = eₗ} {eᵣ = eᵣ} ⊢ₗ ⊢ᵣ) | ⇒-V Vₗ | ⇒-V Vᵣ = ⇒-D (D-β-+ Vₗ Vᵣ)
⇒-progress (⊢-+ {eₗ = eₗ} {eᵣ = eᵣ} ⊢ₗ ⊢ᵣ) | ⇒-V Vₗ | ⇒-D Dᵣ = ⇒-D (D-ξ-+ᵣ Vₗ Dᵣ)
⇒-progress (⊢-+ {eₗ = eₗ} {eᵣ = eᵣ} ⊢ₗ ⊢ᵣ) | ⇒-D Dₗ | ⇒-V Vᵣ = ⇒-D (D-ξ-+ₗ Dₗ)
⇒-progress (⊢-+ {eₗ = eₗ} {eᵣ = eᵣ} ⊢ₗ ⊢ᵣ) | ⇒-D Dₗ | ⇒-D Dᵣ = ⇒-D (D-ξ-+ₗ Dₗ)
⇒-progress ⊢-# = ⇒-V V-#
⇒-progress (⊢-φ ⊢ₚ ⊢ₑ) with ⇒-progress ⊢ₑ
⇒-progress (⊢-φ {p = p} {ag = ag} {e = e} ⊢ₚ ⊢ₑ) | ⇒-V V = ⇒-D (D-β-φ V)
⇒-progress (⊢-φ {p = p} {ag = ag} {e = e} ⊢ₚ ⊢ₑ) | ⇒-D D = ⇒-D (D-ξ-φ D)
⇒-progress (⊢-δ ⊢) with ⇒-progress ⊢
⇒-progress (⊢-δ {r = r} {e = e} ⊢) | ⇒-V V = ⇒-D (D-β-δ V)
⇒-progress (⊢-δ {r = r} {e = e} ⊢) | ⇒-D D = ⇒-D (D-ξ-δ D)
⇒-progress (⊢-μ ⊢ₑ) = ⇒-D D-β-μ

⊢⊣-progress : ∀ a l {e c o}
  → e ⇒ c ⟨ o ⟩
  → ∃[ a′ ]((a , l) ⊢ c ⊣ a′)
⊢⊣-progress a l {c = c} D = (select a l c) , ⊢⊣-select

→-progress : ∀ {e τ c o}
  → ∅ ⊢ e ∶ τ
  → e ⇒ c ⟨ o ⟩
  → ∃[ o′ ](o —→ o′)
→-progress (⊢-· ⊢ₗ ⊢ᵣ) (D-ξ-·ₗ D) = →-progress ⊢ₗ D
→-progress (⊢-· ⊢ₗ ⊢ᵣ) (D-ξ-·ᵣ V D) = →-progress ⊢ᵣ D
→-progress (⊢-· {eᵣ = eᵣ} (⊢-ƛ {e = e} ⊢ₗ) ⊢ᵣ) (D-β-· V-ƛ Vᵣ) = applyₑ e 0 eᵣ , T-β-· Vᵣ
→-progress (⊢-+ ⊢ₗ ⊢ᵣ) (D-ξ-+ₗ D) = →-progress ⊢ₗ D
→-progress (⊢-+ ⊢ₗ ⊢ᵣ) (D-ξ-+ᵣ V D) = →-progress ⊢ᵣ D
→-progress (⊢-+ (⊢-# {n = nₗ}) (⊢-# {n = nᵣ})) (D-β-+ V-# V-#) = (# (nₗ Data.Nat.+ nᵣ)) , T-β-+
→-progress (⊢-φ x ⊢) (D-ξ-φ D) = →-progress ⊢ D
→-progress (⊢-φ {e = e} x ⊢) (D-β-φ V) = e , (T-β-φ V)
→-progress (⊢-δ ⊢) (D-ξ-δ D) = →-progress ⊢ D
→-progress (⊢-δ {e = e} ⊢) (D-β-δ V) = e , T-β-δ V
→-progress (⊢-μ {e = e} ⊢) (D-β-μ) = applyₑ e 0 (μ e) , T-β-μ

⇐-progress′ : ∀ {e τ c o o′}
  → ∅ ⊢[ e ]∶ τ
  → e ⇒ c ⟨ o ⟩
  → o —→ o′
  → ∃[ e′ ](e′ ⇐ (decay c) ⟨ o′ ⟩)
⇐-progress′ {c = c} {o′ = o′} ⊢ D T = (compose (decay c) o′) , (compose-⇐ (decay c) o′)

↦-progress : ∀ {e : Exp} {τ : Typ}
  → ∅ ⊢ e ∶ τ
  → e value ⊎ ∃[ e′ ](e ↦ e′)
↦-progress {ƛ e} (⊢-ƛ ⊢) = inj₁ V-ƛ
↦-progress {eₗ `· eᵣ} (⊢-· ⊢ₗ ⊢ᵣ)
    with (↦-progress ⊢ₗ)     with (↦-progress ⊢ᵣ)
... | inj₁ (V-ƛ {e})          | inj₁ V = inj₂ (applyₑ e 0 eᵣ , (step (D-β-· V-ƛ V) (T-β-· V) C-∘))
... | inj₁ V-ƛ                | inj₂ (eᵣ′ , step D T C) = inj₂ ((eₗ `· eᵣ′) , (step (D-ξ-·ᵣ V-ƛ D) T (C-·ᵣ C)))
... | inj₂ (eₗ′ , step D T C) | _ = inj₂ (eₗ′ `· eᵣ , (step (D-ξ-·ₗ D) T (C-·ₗ C)))
↦-progress {eₗ `+ eᵣ} (⊢-+ ⊢ₗ ⊢ᵣ)
    with (↦-progress ⊢ₗ)     with (↦-progress ⊢ᵣ)
... | inj₁ (V-# {nₗ})         | inj₁ (V-# {nᵣ}) = inj₂ ((# (nₗ + nᵣ)) , (step (D-β-+ V-# V-#) (T-β-+) C-∘))
... | inj₁ V-#                | inj₂ (eᵣ′ , step D T C) = inj₂ ((eₗ `+ eᵣ′) , (step (D-ξ-+ᵣ V-# D) T (C-+ᵣ C)))
... | inj₂ (eₗ′ , step D T C) | _ = inj₂ (eₗ′ `+ eᵣ , (step (D-ξ-+ₗ D) T (C-+ₗ C)))
↦-progress {# _} ⊢-# = inj₁ V-#
↦-progress {φ f e} (⊢-φ x ⊢) with (↦-progress ⊢)
... | inj₁ V = inj₂ (e , (step (D-β-φ V) (T-β-φ V) C-∘))
... | inj₂ (e′ , step D T C) = inj₂ (φ f e′ , step (D-ξ-φ D) T (C-φ C))
↦-progress {δ r e} (⊢-δ ⊢) with (↦-progress ⊢)
... | inj₁ V = inj₂ (e , (step (D-β-δ V) (T-β-δ V) C-∘))
... | inj₂ (e′ , step D T C) = inj₂ (δ r e′ , step (D-ξ-δ D) T (C-δ C))
↦-progress {μ e} (⊢-μ ⊢ₑ) = inj₂ (applyₑ e 0 (μ e) , step D-β-μ T-β-μ C-∘)

-- progress : ∀ {p a g l e τ}
--   → ∅ ⊢[ e ]∶ τ
--   → ∃[ e′ ]((p , a , g , l) ⊢ e ⇥′ e′)
-- progress {p} {a} {g} {l} {e} ⊢ = {!!}
