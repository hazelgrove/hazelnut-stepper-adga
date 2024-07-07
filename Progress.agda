module Progress where

open import Base
open import Match
open import Statics
open import Dynamics
open import Preservation
open import Data.Nat using (ℕ)
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
¬value-⇝-¬value ¬V (I-`-⊤ _) ()
¬value-⇝-¬value ¬V (I-`-⊥ _) ()
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
↦-progress {eₗ `· eᵣ} (⊢-· ⊢ₗ ⊢ᵣ) with (↦-progress ⊢ₗ) with (↦-progress ⊢ᵣ)
↦-progress {(ƛ e) `· eᵣ} (⊢-· ⊢ₗ ⊢ᵣ) | inj₁ (V-ƛ {e}) | inj₁ V = inj₂ (applyₑ e 0 eᵣ , (step (D-β-· V-ƛ V) (T-β-· V) {!!}))
... | inj₁ V-ƛ | inj₂ y = {!!}
... | inj₂ (eₗ′ , step D T C) | _ = inj₂ (eₗ′ `· eᵣ , (step (D-ξ-·ₗ D) T (D-ξ-·ₗ C)))
↦-progress {_ `+ _} (⊢-+ ⊢ₗ ⊢ᵣ) = {!!}
↦-progress {# _} ⊢-# = inj₁ V-#
↦-progress {φ (_ , _) _} (⊢-φ x ⊢) = {!!}
↦-progress {δ _ _} (⊢-δ ⊢) = {!!}

progress : ∀ {p a g l e τ}
  → ∅ ⊢[ e ]∶ τ
  → ∃[ e′ ]((p , a , g , l) ⊢ e ⇥′ e′)
progress {p} {a} {g} {l} {e} ⊢ = {!!}
