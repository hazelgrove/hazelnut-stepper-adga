open import Base
open import Dynamics renaming (Ctx to EvalCtx)
open import Data.Product using (_,_; _×_)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; _<_; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; _≡_; cong; cong₂; subst; sym)

module Statics where
  data Typ : Set where
    _`→_ : Typ → Typ → Typ
    `ℕ    : Typ

  infixl 5 _⸴_

  data Ctx : Set where
    ∅   : Ctx
    _⸴_ : (Γ : Ctx) → (τ : Typ) → Ctx

  length : Ctx → ℕ
  length ∅ = 0
  length (Γ ⸴ τ) = suc (length Γ)

  insert : ∀ (Γ : Ctx) → (n : ℕ) → Typ → Ctx
  insert Γ zero τ₀ = Γ ⸴ τ₀
  insert ∅ (suc n) τ₀ = ∅
  insert (Γ ⸴ τ) (suc n) τ₀ = insert Γ n τ₀ ⸴ τ

  update : ∀ (Γ : Ctx) → (n : ℕ) → Typ → Ctx
  update ∅ zero τ = ∅
  update (Γ ⸴ τ) zero τ₀ = Γ ⸴ τ₀
  update ∅ (suc n) τ = ∅
  update (Γ ⸴ τ) (suc n) τ₀ = update Γ n τ₀ ⸴ τ

  delete : ∀ (Γ : Ctx) → (n : ℕ) → Ctx
  delete ∅       zero    = ∅
  delete ∅       (suc n) = ∅
  delete (Γ ⸴ τ) zero    = Γ
  delete (Γ ⸴ τ) (suc n) = delete Γ n ⸴ τ
  -- delete (Γ ⸴ τ) zero = Γ
  -- delete (Γ ⸴ τ) (suc n) = delete Γ n

  infix 4 _∋_∶_

  data _∋_∶_ : Ctx → ℕ → Typ → Set where
    ∋-Z : ∀ {Γ τ}
      → Γ ⸴ τ ∋ zero ∶ τ

    ∋-S : ∀ {Γ x τ τ′}
      → Γ ∋ x ∶ τ
      → Γ ⸴ τ′ ∋ (suc x) ∶ τ

  record Typable (T : Set) : Set₁ where
    field
      synthesize : Ctx → T → Typ → Set

  infix 4 _⊢[_]∶_
  infix 4 _⊢<_>∶_
  infix 4 _⊢⟨_⟩∶_

  data _⊢[_]∶_ : Ctx → Exp → Typ → Set
  data _⊢<_>∶_ : Ctx → Pat → Typ → Set
  data _⊢⟨_⟩∶_ : Ctx → EvalCtx → Typ → Set

  data _⊢[_]∶_ where
    ⊢-` : ∀ {Γ x τ}
      → (∋ : Γ ∋ x ∶ τ)
      → Γ ⊢[ ` x ]∶ τ

    ⊢-ƛ : ∀ {Γ e τₓ τₑ}
      → (Γ ⸴ τₓ) ⊢[ e ]∶ τₑ
      → Γ ⊢[ ƛ e ]∶ (τₓ `→ τₑ)

    ⊢-· : ∀ {Γ eₗ eᵣ τ₁ τ₂}
      → (⊢ₗ : Γ ⊢[ eₗ ]∶ (τ₂ `→ τ₁))
      → (⊢ᵣ : Γ ⊢[ eᵣ ]∶ τ₂)
      → Γ ⊢[ (eₗ `· eᵣ) ]∶ τ₁

    ⊢-+ : ∀ {Γ eₗ eᵣ}
      → (⊢ₗ : Γ ⊢[ eₗ ]∶ `ℕ)
      → (⊢ᵣ : Γ ⊢[ eᵣ ]∶ `ℕ)
      → Γ ⊢[ (eₗ `+ eᵣ) ]∶ `ℕ

    ⊢-# : ∀ {Γ n}
      → Γ ⊢[ (# n) ]∶ `ℕ

    ⊢-φ : ∀ {Γ p ag τₚ e τₑ}
      → Γ ⊢< p >∶ τₚ
      → Γ ⊢[ e ]∶ τₑ
      → Γ ⊢[ φ (p , ag) e ]∶ τₑ

    ⊢-δ : ∀ {Γ r e τ}
      → Γ ⊢[ e ]∶ τ
      → Γ ⊢[ δ r e ]∶ τ

    ⊢-μ : ∀ {Γ e τ}
      → (Γ ⸴ τ) ⊢[ e ]∶ τ
      → Γ ⊢[ μ e ]∶ τ

  data _⊢<_>∶_ where
    ⊢-E : ∀ {Γ τ}
      → Γ ⊢<  $e >∶ τ

    ⊢-V : ∀ {Γ τ}
      → Γ ⊢<  $v >∶ τ

    ⊢-` : ∀ {Γ x τ}
      → Γ ∋ x ∶ τ
      → Γ ⊢<  ` x >∶ τ

    ⊢-ƛ : ∀ {Γ e τₓ τₑ}
      → (Γ ⸴ τₓ) ⊢[ e ]∶ τₑ
      → Γ ⊢<  ƛ e >∶ (τₓ `→ τₑ)

    ⊢-· : ∀ {Γ e₁ e₂ τ₁ τ₂}
      → Γ ⊢< e₁ >∶ (τ₂ `→ τ₁)
      → Γ ⊢< e₂ >∶ τ₂
      → Γ ⊢< (e₁ `· e₂) >∶ τ₁

    ⊢-# : ∀ {Γ n}
      → Γ ⊢< (# n) >∶ `ℕ

    ⊢-+ : ∀ {Γ e₁ e₂}
      → Γ ⊢< e₁ >∶ `ℕ
      → Γ ⊢< e₂ >∶ `ℕ
      → Γ ⊢< (e₁ `+ e₂) >∶ `ℕ

    ⊢-μ : ∀ {Γ e τ}
      → (Γ ⸴ τ) ⊢[ e ]∶ τ
      → Γ ⊢< (μ e) >∶ τ

  data _⊢⟨_⟩∶_ where
    ⊢-∘ : ∀ {Γ τ}
      → Γ ⊢⟨ ∘ ⟩∶ τ

    ⊢-·ₗ : ∀ {Γ εₗ eᵣ τₗ τᵣ}
      → Γ ⊢⟨ εₗ ⟩∶ (τᵣ `→ τₗ)
      → Γ ⊢[ eᵣ ]∶ τᵣ
      → Γ ⊢⟨ εₗ ·ₗ eᵣ ⟩∶ τₗ

    ⊢-·ᵣ : ∀ {Γ eₗ εᵣ τₗ τᵣ}
      → Γ ⊢[ eₗ ]∶ (τᵣ `→ τₗ)
      → Γ ⊢⟨ εᵣ ⟩∶ τᵣ
      → Γ ⊢⟨ eₗ ·ᵣ εᵣ ⟩∶ τₗ

    ⊢-+ₗ : ∀ {Γ εₗ eᵣ}
      → Γ ⊢⟨ εₗ ⟩∶ `ℕ
      → Γ ⊢[ eᵣ ]∶ `ℕ
      → Γ ⊢⟨ εₗ +ₗ eᵣ ⟩∶ `ℕ

    ⊢-+ᵣ : ∀ {Γ eₗ εᵣ}
      → Γ ⊢[ eₗ ]∶ `ℕ
      → Γ ⊢⟨ εᵣ ⟩∶ `ℕ
      → Γ ⊢⟨ eₗ +ᵣ εᵣ ⟩∶ `ℕ

    ⊢-φ : ∀ {Γ p ag τₚ e τₑ}
      → Γ ⊢< p >∶ τₚ
      → Γ ⊢⟨ e ⟩∶ τₑ
      → Γ ⊢⟨ φ (p , ag) e ⟩∶ τₑ

    ⊢-δ : ∀ {Γ r e τ}
      → Γ ⊢⟨ e ⟩∶ τ
      → Γ ⊢⟨ δ r e ⟩∶ τ

  _⊢_∶_ : {T : Set} ⦃ TypableT : Typable T ⦄ → Ctx → T → Typ → Set
  _⊢_∶_ ⦃ TypableT ⦄ Γ t τ = Typable.synthesize TypableT Γ t τ

  instance
    TypableExp : Typable Exp
    TypableExp = record { synthesize = λ Γ e τ → Γ ⊢[ e ]∶ τ }

    TypablePat : Typable Pat
    TypablePat = record { synthesize = λ Γ e τ → Γ ⊢< e >∶ τ }

    TypableCtx : Typable Dynamics.Ctx
    TypableCtx = record { synthesize = λ Γ ε τ → Γ ⊢⟨ ε ⟩∶ τ }
