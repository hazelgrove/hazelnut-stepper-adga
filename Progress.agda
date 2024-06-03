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

data _⊢_⇥⟨_⟩_ : Pat × Act × Gas × ℕ → Exp → ℕ → Exp → Set where
  step : ∀ {p a g l e e′ e₀ e₀′ ε ε₀}
    → instr p a g l e ⇒ ε₀ ⟨ e₀ ⟩
    → (a , l) ⊢ ε ⊣ ∥
    → e₀ —→ e₀′
    → e′ ⇐ (decay ε) ⟨ e₀′ ⟩
    → (p , a , g , l) ⊢ e ⇥⟨ 1 ⟩ e′

  skip : ∀ {p a g l e e′ e″ e₀ e₀′ ε ε₀ n}
    → instr p a g l e ⇒ ε₀ ⟨ e₀ ⟩
    → e₀ filter-like ⊎ (a , l) ⊢ ε ⊣ ⊳
    → e₀ —→ e₀′
    → e′ ⇐ (decay ε) ⟨ e₀′ ⟩
    → (p , a , g , l) ⊢ e′ ⇥⟨ n ⟩ e″
    → (p , a , g , l) ⊢ e ⇥⟨ n ⟩ e″

  done : ∀ {p a g l v}
    → v value
    → (p , a , g , l) ⊢ v ⇥⟨ 0 ⟩ v

data Progress_under_ : Exp → Pat × Act × Gas × ℕ → Set where
  P : ∀ {p a g l e e′ n}
    → (p , a , g , l) ⊢ e ⇥⟨ n ⟩ e′
    → Progress e under (p , a , g , l)

⇒-progress : ∀ {Γ e τ}
  → Γ ⊢[ e ]∶ τ
  → e value ⊎ ∃(λ ((c , o) : Dynamics.Ctx × Exp) → e ⇒ c ⟨ o ⟩)
⇒-progress (⊢-` {x = x} ∋) = inj₂ ((∘ , (` x)) , D-β-` {x})
⇒-progress (⊢-ƛ ⊢) = inj₁ V-ƛ
⇒-progress (⊢-· ⊢ₗ ⊢ᵣ) with ⇒-progress ⊢ₗ with ⇒-progress ⊢ᵣ
⇒-progress (⊢-· {eₗ = eₗ} {eᵣ = eᵣ} ⊢ₗ ⊢ᵣ) | inj₁ Vₗ | inj₁ Vᵣ = inj₂ ((∘ , eₗ · eᵣ) , D-β-· Vₗ Vᵣ)
⇒-progress (⊢-· {eₗ = eₗ} {eᵣ = eᵣ} ⊢ₗ ⊢ᵣ) | inj₁ Vₗ | inj₂ ((c , o) , Dᵣ) = inj₂ (((eₗ ·ᵣ c) , o) , D-ξ-·-r Vₗ Dᵣ)
⇒-progress (⊢-· {eₗ = eₗ} {eᵣ = eᵣ} ⊢ₗ ⊢ᵣ) | inj₂ ((c , o) , Dₗ) | inj₁ Vᵣ = inj₂ ((c ·ₗ eᵣ , o) , D-ξ-·-l Dₗ)
⇒-progress (⊢-· {eₗ = eₗ} {eᵣ = eᵣ} ⊢ₗ ⊢ᵣ) | inj₂ ((c , o) , Dₗ) | inj₂ Dᵣ = inj₂ ((c ·ₗ eᵣ , o) , D-ξ-·-l Dₗ)
⇒-progress (⊢-+ ⊢ₗ ⊢ᵣ) with ⇒-progress ⊢ₗ with ⇒-progress ⊢ᵣ
⇒-progress (⊢-+ {eₗ = eₗ} {eᵣ = eᵣ} ⊢ₗ ⊢ᵣ) | inj₁ Vₗ | inj₁ Vᵣ = inj₂ ((∘ , eₗ + eᵣ) , D-β-+ Vₗ Vᵣ)
⇒-progress (⊢-+ {eₗ = eₗ} {eᵣ = eᵣ} ⊢ₗ ⊢ᵣ) | inj₁ Vₗ | inj₂ ((c , o) , Dᵣ) = inj₂ (((eₗ +ᵣ c) , o) , D-ξ-+-r Vₗ Dᵣ)
⇒-progress (⊢-+ {eₗ = eₗ} {eᵣ = eᵣ} ⊢ₗ ⊢ᵣ) | inj₂ ((c , o) , Dₗ) | inj₁ Vᵣ = inj₂ ((c +ₗ eᵣ , o) , D-ξ-+-l Dₗ)
⇒-progress (⊢-+ {eₗ = eₗ} {eᵣ = eᵣ} ⊢ₗ ⊢ᵣ) | inj₂ ((c , o) , Dₗ) | inj₂ Dᵣ = inj₂ ((c +ₗ eᵣ , o) , D-ξ-+-l Dₗ)
⇒-progress ⊢-# = inj₁ V-#
⇒-progress (⊢-φ ⊢ₚ ⊢ₑ) with ⇒-progress ⊢ₑ
⇒-progress (⊢-φ {p = p} {ag = ag} {e = e} ⊢ₚ ⊢ₑ) | inj₁ V = inj₂ ((∘ , φ (p , ag) e) , (D-β-φ V))
⇒-progress (⊢-φ {p = p} {ag = ag} {e = e} ⊢ₚ ⊢ₑ) | inj₂ ((c , o) , D) = inj₂ (((φ (p , ag) c) , o) , (D-ξ-φ D))
⇒-progress (⊢-δ ⊢) with ⇒-progress ⊢
⇒-progress (⊢-δ {r = r} {e = e} ⊢) | inj₁ V = inj₂ ((∘ , (δ r e)) , D-β-δ V)
⇒-progress (⊢-δ {r = r} {e = e} ⊢) | inj₂ ((c , o) , D) = inj₂ (((δ r c) , o) , D-ξ-δ D)

-- ⇝-progress : ∀ {Γ p a g l e τ}
--   → Γ ⊢ e ∶ τ
--   → e value ⊎ 

-- ⇝-progress {p = p} (⊢-` {x = x} ∋) with p matches? (` x)
-- ⇝-progress {a = a} {g = g} {l = l} (⊢-` {x = x} ∋) | yes M-E = δ (a , g , l) (` x) , (I-`-⊤ M-E)
-- ⇝-progress (⊢-` {x = x} ∋) | no ¬M = ` x , I-`-⊥ (λ M → ¬M M)
-- ⇝-progress (⊢-ƛ {e = e} ⊢) = ƛ e , (I-V V-ƛ)
-- ⇝-progress {p = p} (⊢-· {eₗ = eₗ} {eᵣ = eᵣ} ⊢ₗ ⊢ᵣ) with (p matches? (eₗ · eᵣ)) with (⇝-progress ⊢ₗ) with (⇝-progress ⊢ᵣ)
-- ⇝-progress {a = a} {g} {l} (⊢-· ⊢ₗ ⊢ᵣ) | yes M | eₗ , ⇝ₗ | eᵣ , ⇝ᵣ = δ (a , g , l) (eₗ · eᵣ) , I-·-⊤ M ⇝ₗ ⇝ᵣ
-- ⇝-progress (⊢-· ⊢ₗ ⊢ᵣ) | no ¬M | eₗ , ⇝ₗ | eᵣ , ⇝ᵣ = (eₗ · eᵣ) , (I-·-⊥ (λ { M → ¬M M }) ⇝ₗ ⇝ᵣ)
-- ⇝-progress {p = p} (⊢-+ {eₗ = eₗ} {eᵣ = eᵣ} ⊢ₗ ⊢ᵣ) with (p matches? (eₗ + eᵣ)) with (⇝-progress ⊢ₗ) with (⇝-progress ⊢ᵣ)
-- ⇝-progress {a = a} {g} {l} (⊢-+ ⊢ₗ ⊢ᵣ) | yes M | eₗ , ⇝ₗ | eᵣ , ⇝ᵣ = δ (a , g , l) (eₗ + eᵣ) , I-+-⊤ M ⇝ₗ ⇝ᵣ
-- ⇝-progress (⊢-+ ⊢ₗ ⊢ᵣ) | no ¬M | eₗ , ⇝ₗ | eᵣ , ⇝ᵣ = (eₗ + eᵣ) , (I-+-⊥ (λ { M → ¬M M }) ⇝ₗ ⇝ᵣ)
-- ⇝-progress (⊢-# {n = n}) = (# n) , I-V V-#
-- ⇝-progress {p = pat} {a = act} {g = gas} {l = lvl} (⊢-φ {p = p} {a , g} {e = e} ⊢ₚ ⊢ₑ) with (⇝-progress ⊢ₑ)
-- ⇝-progress {p = pat} {a = act} {g = gas} {l = lvl} (⊢-φ {p = p} {a , g} {e = e} ⊢ₚ ⊢ₑ) | e′ , ⇝′ with (⇝-preserve ⊢ₑ ⇝′)
-- ⇝-progress {p = pat} {a = act} {g = gas} {l = lvl} (⊢-φ {p = p} {a , g} {e = e} ⊢ₚ ⊢ₑ) | e′ , ⇝′ | ⊢ₑ′ with (⇝-progress {p = p} {a} {g} {l = ℕ.suc lvl} ⊢ₑ′)
-- ⇝-progress {p = pat} {a = act} {g = gas} {l = lvl} (⊢-φ {p = p} {a , g} {e = e} ⊢ₚ ⊢ₑ) | e′ , ⇝′ | ⊢ₑ′ | e″ , ⇝″ = {!!}
-- ⇝-progress (⊢-δ ⊢) = {!!}

progress : ∀ {Γ p a g l e τ}
  → Γ ⊢ e ∶ τ
  → Progress e under (p , a , g , l)
progress {p = p} (⊢-` {x = x} ∋) with p matches? (` x)
... | yes M-E = P {!!}
... | no ¬M  = {!!}
progress (⊢-ƛ ⊢) = {!!}
progress (⊢-· ⊢ₗ ⊢ᵣ) = {!!}
progress (⊢-+ ⊢ₗ ⊢ᵣ) = {!!}
progress ⊢-# = {!!}
progress (⊢-φ ⊢ₚ ⊢ₑ) = {!!}
progress (⊢-δ ⊢) = {!!}
