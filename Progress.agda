module Progress where

open import Base
open import Match
open import Statics
open import Dynamics
open import Preservation
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Nullary using (Dec; yes; no; ¬_; _×-dec_)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≡_; cong; cong₂; subst; subst₂; sym; trans)

data _⊢_⇥⟨_⟩_ : Pat × Act × Gas × ℕ → Exp → ℕ → Exp → Set where
  step : ∀ {p a g l e e′ eᵢ e₀ e₀′ ε ε₀}
    → (p , a , g , l) ⊢ e ⇝ eᵢ
    → eᵢ ⇒ ε₀ ⟨ e₀ ⟩
    → (a , l) ⊢ ε ⊣ ∥
    → e₀ —→ e₀′
    → e′ ⇐ (decay ε) ⟨ e₀′ ⟩
    → (p , a , g , l) ⊢ e ⇥⟨ 1 ⟩ e′

  skip : ∀ {p a g l e e′ e″ eᵢ e₀ e₀′ ε ε₀ n}
    → (p , a , g , l) ⊢ e ⇝ eᵢ
    → eᵢ ⇒ ε₀ ⟨ e₀ ⟩
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
