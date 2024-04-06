open import Core
open import Data.Nat using (ℕ; zero; suc)

module Statics where
  data Typ : Set where
    _⇒_ : Typ → Typ → Typ
    Ν    : Typ

  data Ctx : Set where
    ∅   : Ctx
    _,_ : Ctx → Typ → Ctx

  length : Ctx → ℕ
  length ∅ = 0
  length (Γ , τ) = suc (length Γ)

  infix 4 _∋_∶_

  data _∋_∶_ : Ctx → ℕ → Typ → Set where
    ∋-Z : ∀ {Γ τ}
      → Γ , τ ∋ zero ∶ τ

    ∋-S : ∀ {Γ x τ τ′}
      → Γ ∋ x ∶ τ
      → Γ , τ′ ∋ (suc x) ∶ τ

  infix 4 _⊢[_]∶_
  infix 4 _⊢⟨_⟩∶_

  data _⊢[_]∶_ : Ctx → Exp → Typ → Set
  data _⊢⟨_⟩∶_ : Ctx → Pat → Typ → Set
  
  data _⊢[_]∶_ where
    ⊢-` : ∀ {Γ x τ}
      → Γ ∋ x ∶ τ
      → Γ ⊢[ ` x ]∶ τ

    ⊢-ƛ : ∀ {Γ e τₓ τₑ}
      → Γ , τₓ ⊢[ e ]∶ τₑ
      → Γ ⊢[ ƛ e ]∶ (τₓ ⇒ τₑ)

    ⊢-+ : ∀ {Γ e₁ e₂}
      → Γ ⊢[ e₁ ]∶ Ν
      → Γ ⊢[ e₂ ]∶ Ν
      → Γ ⊢[ (e₁ + e₂) ]∶ Ν

    ⊢-# : ∀ {Γ n}
      → Γ ⊢[ (# n) ]∶ Ν

    ⊢-φ : ∀ {Γ f τₚ e τₑ}
      → Γ ⊢⟨ Filter.pat f ⟩∶ τₚ
      → Γ ⊢[ e ]∶ τₑ
      → Γ ⊢[ φ f e ]∶ τₑ

    ⊢-δ : ∀ {Γ r e τ}
      → Γ ⊢[ e ]∶ τ
      → Γ ⊢[ δ r e ]∶ τ

  data _⊢⟨_⟩∶_ where
    ⊢-E : ∀ {Γ τ}
      → Γ ⊢⟨ $e ⟩∶ τ

    ⊢-V : ∀ {Γ τ}
      → Γ ⊢⟨ $v ⟩∶ τ

    ⊢-` : ∀ {Γ x τ}
      → Γ ∋ x ∶ τ
      → Γ ⊢⟨ ` x ⟩∶ τ

    ⊢-ƛ : ∀ {Γ e τₓ τₑ}
      → Γ , τₓ ⊢[ e ]∶ τₑ
      → Γ ⊢⟨ ƛ e ⟩∶ (τₓ ⇒ τₑ)

    ⊢-· : ∀ {Γ e₁ e₂ τ₁ τ₂}
      → Γ ⊢⟨ e₁ ⟩∶ τ₂ ⇒ τ₁
      → Γ ⊢⟨ e₂ ⟩∶ τ₂
      → Γ ⊢⟨ (e₁ · e₂) ⟩∶ τ₁

    ⊢-# : ∀ {Γ n}
      → Γ ⊢⟨ (# n) ⟩∶ Ν

    ⊢-+ : ∀ {Γ e₁ e₂}
      → Γ ⊢⟨ e₁ ⟩∶ Ν
      → Γ ⊢⟨ e₂ ⟩∶ Ν
      → Γ ⊢⟨ (e₁ + e₂) ⟩∶ Ν
