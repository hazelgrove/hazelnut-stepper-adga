open import Base
open import Dynamics
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_; _,_)

module Progress where
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
      → e₀ filter ⊎ (a , l) ⊢ ε ⊣ ⊳
      → e₀ —→ e₀′
      → e′ ⇐ (decay ε) ⟨ e₀′ ⟩
      → (p , a , g , l) ⊢ e′ ⇥⟨ n ⟩ e″
      → (p , a , g , l) ⊢ e ⇥⟨ n ⟩ e″

    done : ∀ {p a g l v}
      → v value
      → (p , a , g , l) ⊢ v ⇥⟨ 0 ⟩ v
