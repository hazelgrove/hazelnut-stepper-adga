module Statics where

open import Base
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)

infixr 7 _`→_

data Typ : Set where
  _`→_ : Typ → Typ → Typ
  `ℕ    : Typ

infixl 5 _⸴_

data Ctx : Set where
  ∅   : Ctx
  _⸴_ : (Γ : Ctx) → (τ : Typ) → Ctx

infix 4 _∋_∶_

data _∋_∶_ : Ctx → ℕ → Typ → Set where
  ∋-Z : ∀ {Γ τ}
    → Γ ⸴ τ ∋ zero ∶ τ

  ∋-S : ∀ {Γ x τ τ′}
    → Γ ∋ x ∶ τ
    → Γ ⸴ τ′ ∋ suc x ∶ τ

infix 4 _⊢[_]∶_
infix 4 _⊢<_>∶_

data _⊢[_]∶_ : Ctx → Exp → Typ → Set
data _⊢<_>∶_ : Ctx → Pat → Typ → Set

data _⊢[_]∶_ where
  ⊢-` : ∀ {Γ x τ}
    → (∋ : Γ ∋ x ∶ τ)
    → Γ ⊢[ ` x ]∶ τ

  ⊢-ƛ : ∀ {Γ e τₓ τₑ}
    → (⊢ₑ : Γ ⸴ τₓ ⊢[ e ]∶ τₑ)
    → Γ ⊢[ ƛ e ]∶ τₓ `→ τₑ

  ⊢-· : ∀ {Γ eₗ eᵣ τ₁ τ₂}
    → (⊢ₗ : Γ ⊢[ eₗ ]∶ τ₂ `→ τ₁)
    → (⊢ᵣ : Γ ⊢[ eᵣ ]∶ τ₂)
    → Γ ⊢[ eₗ `· eᵣ ]∶ τ₁

  ⊢-+ : ∀ {Γ eₗ eᵣ}
    → (⊢ₗ : Γ ⊢[ eₗ ]∶ `ℕ)
    → (⊢ᵣ : Γ ⊢[ eᵣ ]∶ `ℕ)
    → Γ ⊢[ eₗ `+ eᵣ ]∶ `ℕ

  ⊢-# : ∀ {Γ n}
    → Γ ⊢[ # n ]∶ `ℕ

  ⊢-φ : ∀ {Γ p ag τₚ e τₑ}
    → (⊢ₚ : Γ ⊢< p >∶ τₚ)
    → (⊢ₑ : Γ ⊢[ e ]∶ τₑ)
    → Γ ⊢[ φ (p , ag) e ]∶ τₑ

  ⊢-δ : ∀ {Γ r e τ}
    → (⊢ₑ : Γ ⊢[ e ]∶ τ)
    → Γ ⊢[ δ r e ]∶ τ

  ⊢-μ : ∀ {Γ e τ}
    → (⊢ₑ : Γ ⸴ τ ⊢[ e ]∶ τ)
    → Γ ⊢[ μ e ]∶ τ

data _⊢<_>∶_ where
  ⊢-E : ∀ {Γ τ}
    → Γ ⊢< $e >∶ τ

  ⊢-V : ∀ {Γ τ}
    → Γ ⊢< $v >∶ τ

  ⊢-` : ∀ {Γ x τ}
    → (∋ : Γ ∋ x ∶ τ)
    → Γ ⊢< ` x >∶ τ

  ⊢-ƛ : ∀ {Γ p τₓ τₚ}
    → (⊢ₚ : Γ ⸴ τₓ ⊢< p >∶ τₚ)
    → Γ ⊢< ƛ p >∶ τₓ `→ τₚ

  ⊢-· : ∀ {Γ pₗ pᵣ τ₁ τ₂}
    → (⊢ₗ : Γ ⊢< pₗ >∶ τ₂ `→ τ₁)
    → (⊢ᵣ : Γ ⊢< pᵣ >∶ τ₂)
    → Γ ⊢< pₗ `· pᵣ >∶ τ₁

  ⊢-# : ∀ {Γ n}
    → Γ ⊢< # n >∶ `ℕ

  ⊢-+ : ∀ {Γ pₗ pᵣ}
    → (⊢ₗ : Γ ⊢< pₗ >∶ `ℕ)
    → (⊢ᵣ : Γ ⊢< pᵣ >∶ `ℕ)
    → Γ ⊢< pₗ `+ pᵣ >∶ `ℕ

  ⊢-μ : ∀ {Γ p τ}
    → (⊢ₚ : Γ ⸴ τ ⊢< p >∶ τ)
    → Γ ⊢< μ p >∶ τ
