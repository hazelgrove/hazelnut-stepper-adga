open import Core
open import Dynamics renaming (Ctx to EvalCtx)
open import Data.Product using (_,_)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; _<_)

module Statics where
  data Typ : Set where
    _⇒_ : Typ → Typ → Typ
    Ν    : Typ

  data Ctx : Set where
    ∅   : Ctx
    _⸴_ : Ctx → Typ → Ctx

  length : Ctx → ℕ
  length ∅ = 0
  length (Γ ⸴ τ) = suc (length Γ)

  insert : ∀ {Γ : Ctx} → {n : ℕ} → (p : n ≤ length Γ) → Typ → Ctx
  insert {Γ} {zero} p τ = Γ ⸴ τ
  insert {Γ ⸴ τ′} {suc n} (s≤s p) τ = (insert p τ) ⸴ τ′

  update : ∀ {Γ : Ctx} → {n : ℕ} → (p : n < length Γ) → Typ → Ctx
  update {Γ ⸴ τ′} {n = ℕ.zero} p τ = Γ ⸴ τ
  update {Γ ⸴ τ′} {n = ℕ.suc n} (s≤s p) τ = (update p τ) ⸴ τ′

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
      → Γ ⊢[ ƛ e ]∶ (τₓ ⇒ τₑ)

    ⊢-· : ∀ {Γ e₁ e₂ τ₁ τ₂}
      → Γ ⊢[ e₁ ]∶ (τ₂ ⇒ τ₁)
      → Γ ⊢[ e₂ ]∶ τ₂
      → Γ ⊢[ (e₁ · e₂) ]∶ τ₁

    ⊢-+ : ∀ {Γ e₁ e₂}
      → Γ ⊢[ e₁ ]∶ Ν
      → Γ ⊢[ e₂ ]∶ Ν
      → Γ ⊢[ (e₁ + e₂) ]∶ Ν

    ⊢-# : ∀ {Γ n}
      → Γ ⊢[ (# n) ]∶ Ν

    ⊢-φ : ∀ {Γ p ag τₚ e τₑ}
      → Γ ⊢< p >∶ τₚ
      → Γ ⊢[ e ]∶ τₑ
      → Γ ⊢[ φ (p , ag) e ]∶ τₑ

    ⊢-δ : ∀ {Γ r e τ}
      → Γ ⊢[ e ]∶ τ
      → Γ ⊢[ δ r e ]∶ τ

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
      → Γ ⊢<  ƛ e >∶ (τₓ ⇒ τₑ)

    ⊢-· : ∀ {Γ e₁ e₂ τ₁ τ₂}
      → Γ ⊢< e₁ >∶ (τ₂ ⇒ τ₁)
      → Γ ⊢< e₂ >∶ τ₂
      → Γ ⊢< (e₁ · e₂) >∶ τ₁

    ⊢-# : ∀ {Γ n}
      → Γ ⊢< (# n) >∶ Ν

    ⊢-+ : ∀ {Γ e₁ e₂}
      → Γ ⊢< e₁ >∶ Ν
      → Γ ⊢< e₂ >∶ Ν
      → Γ ⊢< (e₁ + e₂) >∶ Ν

  data _⊢⟨_⟩∶_ where
    ⊢-∘ : ∀ {Γ τ}
      → Γ ⊢⟨ ∘ ⟩∶ τ

    ⊢-·-l : ∀ {Γ εₗ eᵣ τₗ τᵣ}
      → Γ ⊢⟨ εₗ ⟩∶ (τᵣ ⇒ τₗ)
      → Γ ⊢[ eᵣ ]∶ τᵣ
      → Γ ⊢⟨ εₗ ·ₗ eᵣ ⟩∶ τₗ

    ⊢-·-r : ∀ {Γ eₗ εᵣ τₗ τᵣ}
      → Γ ⊢[ eₗ ]∶ (τᵣ ⇒ τₗ)
      → Γ ⊢⟨ εᵣ ⟩∶ τᵣ
      → Γ ⊢⟨ eₗ ·ᵣ εᵣ ⟩∶ τₗ 


  _⊢_∶_ : {T : Set} ⦃ TypableT : Typable T ⦄ → Ctx → T → Typ → Set
  _⊢_∶_ ⦃ TypableT ⦄ Γ t τ = Typable.synthesize TypableT Γ t τ

  instance
    TypableExp : Typable Exp
    TypableExp = record { synthesize = λ Γ e τ → Γ ⊢[ e ]∶ τ }

    TypablePat : Typable Pat
    TypablePat = record { synthesize = λ Γ e τ → Γ ⊢< e >∶ τ }

    TypableCtx : Typable Dynamics.Ctx
    TypableCtx = record { synthesize = λ Γ ε τ → Γ ⊢⟨ ε ⟩∶ τ }
