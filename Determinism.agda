open import Base
open import Dynamics
open import Data.Nat using (s≤s)
open import Data.Nat.Properties using (≤⇒≯)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)

module Determinism where

_deterministic : ∀ {A B : Set} → (R : A → B → Set) → Set
R deterministic = ∀ {x} {y₁ y₂} → R x y₁ → R x y₂ → y₁ ≡ y₂

⇝-deterministic : ∀ {p a g l} → ((p , a , g , l) ⊢_⇝_) deterministic
⇝-deterministic (I-V V) (I-V V₁) = refl
⇝-deterministic (I-`-⊤ M) (I-`-⊤ M₁) = refl
⇝-deterministic (I-`-⊤ M) (I-`-⊥ ¬M) = ⊥-elim (¬M M)
⇝-deterministic (I-`-⊥ ¬M) (I-`-⊤ M) = ⊥-elim (¬M M)
⇝-deterministic (I-`-⊥ ¬M) (I-`-⊥ ¬M₁) = refl
⇝-deterministic (I-·-⊤ M I₁ I₃) (I-·-⊤ M₁ I₂ I₄) with ⇝-deterministic I₁ I₂ with ⇝-deterministic I₃ I₄
⇝-deterministic (I-·-⊤ M I₁ I₃) (I-·-⊤ M₁ I₂ I₄) | refl | refl = refl
⇝-deterministic (I-·-⊤ M I₁ I₃) (I-·-⊥ ¬M I₂ I₄) = ⊥-elim (¬M M)
⇝-deterministic (I-·-⊥ ¬M I₁ I₃) (I-·-⊤ M I₂ I₄) = ⊥-elim (¬M M)
⇝-deterministic (I-·-⊥ ¬M I₁ I₃) (I-·-⊥ ¬M₁ I₂ I₄) with ⇝-deterministic I₁ I₂ with ⇝-deterministic I₃ I₄
⇝-deterministic (I-·-⊥ ¬M I₁ I₃) (I-·-⊥ ¬M₁ I₂ I₄) | refl | refl = refl
⇝-deterministic (I-+-⊤ M I₁ I₃) (I-+-⊤ M₁ I₂ I₄) with ⇝-deterministic I₁ I₂ with ⇝-deterministic I₃ I₄
⇝-deterministic (I-+-⊤ M I₁ I₃) (I-+-⊤ M₁ I₂ I₄) | refl | refl = refl
⇝-deterministic (I-+-⊤ M I₁ I₃) (I-+-⊥ ¬M I₂ I₄) = ⊥-elim (¬M M)
⇝-deterministic (I-+-⊥ ¬M I₁ I₃) (I-+-⊤ M I₂ I₄) = ⊥-elim (¬M M)
⇝-deterministic (I-+-⊥ ¬M I₁ I₃) (I-+-⊥ ¬M₁ I₂ I₄) with ⇝-deterministic I₁ I₂ with ⇝-deterministic I₃ I₄
⇝-deterministic (I-+-⊥ ¬M I₁ I₃) (I-+-⊥ ¬M₁ I₂ I₄) | refl | refl = refl
⇝-deterministic (I-φ I₁ I₃) (I-φ I₂ I₄) with ⇝-deterministic I₁ I₂
⇝-deterministic (I-φ I₁ I₃) (I-φ I₂ I₄) | refl with ⇝-deterministic I₃ I₄
⇝-deterministic (I-φ I₁ I₃) (I-φ I₂ I₄) | refl | refl = refl
⇝-deterministic (I-δ I₁) (I-δ I₂) with ⇝-deterministic I₁ I₂
⇝-deterministic (I-δ I₁) (I-δ I₂) | refl = refl

⇒¬value : ∀ {e c o} → e ⇒ c ⟨ o ⟩ → ¬ (e value)
⇒¬value (D-ξ-·ₗ D) = λ ()
⇒¬value (D-ξ-·ᵣ V D) = λ ()
⇒¬value (D-β-· Vₗ Vᵣ) = λ ()
⇒¬value (D-ξ-+ₗ D) = λ ()
⇒¬value (D-ξ-+ᵣ V D) = λ ()
⇒¬value (D-β-+ Vₗ Vᵣ) = λ ()
⇒¬value (D-ξ-φ D) = λ ()
⇒¬value (D-β-φ V) = λ ()
⇒¬value (D-ξ-δ D) = λ ()
⇒¬value (D-β-δ V) = λ ()

⇒-deterministic : _⇒_ deterministic
⇒-deterministic (D-ξ-·ₗ D₁) (D-ξ-·ₗ D₂) with ⇒-deterministic D₁ D₂
⇒-deterministic (D-ξ-·ₗ D₁) (D-ξ-·ₗ D₂) | refl = refl
⇒-deterministic (D-ξ-·ₗ Dₗ) (D-ξ-·ᵣ Vₗ Dᵣ) = ⊥-elim (⇒¬value Dₗ Vₗ)
⇒-deterministic (D-ξ-·ₗ Dₗ) (D-β-· Vₗ Vᵣ) = ⊥-elim (⇒¬value Dₗ Vₗ)
⇒-deterministic (D-ξ-·ᵣ V₁ D₁) (D-ξ-·ₗ D₂) = ⊥-elim (⇒¬value D₂ V₁)
⇒-deterministic (D-ξ-·ᵣ V₁ D₁) (D-ξ-·ᵣ Vᵣ D₂) with ⇒-deterministic D₁ D₂
⇒-deterministic (D-ξ-·ᵣ V₁ D₁) (D-ξ-·ᵣ Vᵣ D₂) | refl = refl
⇒-deterministic (D-ξ-·ᵣ V₁ D₁) (D-β-· Vₗ Vᵣ) = ⊥-elim (⇒¬value D₁ Vᵣ)
⇒-deterministic (D-β-· Vₗ _) (D-ξ-·ₗ Dₗ) = ⊥-elim (⇒¬value Dₗ Vₗ)
⇒-deterministic (D-β-· _ Vᵣ) (D-ξ-·ᵣ _ Dᵣ) = ⊥-elim (⇒¬value Dᵣ Vᵣ)
⇒-deterministic (D-β-· V-ƛ V-ƛ) (D-β-· V-ƛ V-ƛ) = refl
⇒-deterministic (D-β-· V-ƛ V-#) (D-β-· V-ƛ V-#) = refl
⇒-deterministic (D-β-· V-# V-ƛ) (D-β-· V-# V-ƛ) = refl
⇒-deterministic (D-β-· V-# V-#) (D-β-· V-# V-#) = refl
⇒-deterministic (D-ξ-+ₗ D₁) (D-ξ-+ₗ D₂) with ⇒-deterministic D₁ D₂
⇒-deterministic (D-ξ-+ₗ D₁) (D-ξ-+ₗ D₂) | refl = refl
⇒-deterministic (D-ξ-+ₗ Dₗ) (D-ξ-+ᵣ Vₗ Dᵣ) = ⊥-elim (⇒¬value Dₗ Vₗ)
⇒-deterministic (D-ξ-+ₗ Dₗ) (D-β-+ Vₗ Vᵣ) = ⊥-elim (⇒¬value Dₗ Vₗ)
⇒-deterministic (D-ξ-+ᵣ V₁ D₁) (D-ξ-+ₗ D₂) = ⊥-elim (⇒¬value D₂ V₁)
⇒-deterministic (D-ξ-+ᵣ V₁ D₁) (D-ξ-+ᵣ Vᵣ D₂) with ⇒-deterministic D₁ D₂
⇒-deterministic (D-ξ-+ᵣ V₁ D₁) (D-ξ-+ᵣ Vᵣ D₂) | refl = refl
⇒-deterministic (D-ξ-+ᵣ V₁ D₁) (D-β-+ Vₗ Vᵣ) = ⊥-elim (⇒¬value D₁ Vᵣ)
⇒-deterministic (D-β-+ Vₗ _) (D-ξ-+ₗ Dₗ) = ⊥-elim (⇒¬value Dₗ Vₗ)
⇒-deterministic (D-β-+ _ Vᵣ) (D-ξ-+ᵣ _ Dᵣ) = ⊥-elim (⇒¬value Dᵣ Vᵣ)
⇒-deterministic (D-β-+ V-ƛ V-ƛ) (D-β-+ V-ƛ V-ƛ) = refl
⇒-deterministic (D-β-+ V-ƛ V-#) (D-β-+ V-ƛ V-#) = refl
⇒-deterministic (D-β-+ V-# V-ƛ) (D-β-+ V-# V-ƛ) = refl
⇒-deterministic (D-β-+ V-# V-#) (D-β-+ V-# V-#) = refl
⇒-deterministic (D-ξ-φ D₁) (D-ξ-φ D₂) with ⇒-deterministic D₁ D₂
⇒-deterministic (D-ξ-φ D₁) (D-ξ-φ D₂) | refl = refl
⇒-deterministic (D-ξ-φ D) (D-β-φ V) = ⊥-elim (⇒¬value D V)
⇒-deterministic (D-β-φ V) (D-ξ-φ D) = ⊥-elim (⇒¬value D V)
⇒-deterministic (D-β-φ V-ƛ) (D-β-φ V-ƛ) = refl
⇒-deterministic (D-β-φ V-#) (D-β-φ V-#) = refl
⇒-deterministic (D-ξ-δ D₁) (D-ξ-δ D₂) with ⇒-deterministic D₁ D₂
⇒-deterministic (D-ξ-δ D₁) (D-ξ-δ D₂) | refl = refl
⇒-deterministic (D-ξ-δ D) (D-β-δ V) = ⊥-elim (⇒¬value D V)
⇒-deterministic (D-β-δ V) (D-ξ-δ D) = ⊥-elim (⇒¬value D V)
⇒-deterministic (D-β-δ V-ƛ) (D-β-δ V-ƛ) = refl
⇒-deterministic (D-β-δ V-#) (D-β-δ V-#) = refl

⊢⊣-deterministic : ∀ {a l} → ((a , l) ⊢_⊣_) deterministic
⊢⊣-deterministic A-∘ A-∘ = refl
⊢⊣-deterministic (A-·ₗ ⊣₁) (A-·ₗ ⊣₂) = ⊢⊣-deterministic ⊣₁ ⊣₂
⊢⊣-deterministic (A-·-r ⊣₁) (A-·-r ⊣₂) = ⊢⊣-deterministic ⊣₁ ⊣₂
⊢⊣-deterministic (A-+-l ⊣₁) (A-+-l ⊣₂) = ⊢⊣-deterministic ⊣₁ ⊣₂
⊢⊣-deterministic (A-+-r ⊣₁) (A-+-r ⊣₂) = ⊢⊣-deterministic ⊣₁ ⊣₂
⊢⊣-deterministic (A-φ ⊣₁) (A-φ ⊣₂) = ⊢⊣-deterministic ⊣₁ ⊣₂
⊢⊣-deterministic (A-Δ-> _ ⊣₁) (A-Δ-> _ ⊣₂) = ⊢⊣-deterministic ⊣₁ ⊣₂
⊢⊣-deterministic (A-Δ-> > ⊣₁) (A-Δ-≤ ≤ ⊣₂) = ⊥-elim (≤⇒≯ ≤ >)
⊢⊣-deterministic (A-Δ-≤ ≤ ⊣₁) (A-Δ-> > ⊣₂) = ⊥-elim (≤⇒≯ ≤ >)
⊢⊣-deterministic (A-Δ-≤ ≤ ⊣₁) (A-Δ-≤ > ⊣₂) = ⊢⊣-deterministic ⊣₁ ⊣₂

→-deterministic : _—→_ deterministic
→-deterministic (T-β-· V₁) (T-β-· V₂) = refl
→-deterministic T-β-+ T-β-+ = refl
→-deterministic (T-β-φ V₁) (T-β-φ V₂) = refl
→-deterministic (T-β-δ V₁) (T-β-δ V₂) = refl

flip : ∀ {A B : Set} → (A → B → Set) → (B → A → Set)
flip f b a = f a b

⇐-deterministic : flip _⇒_ deterministic
⇐-deterministic (D-ξ-·ₗ D₁) (D-ξ-·ₗ D₂) with ⇐-deterministic D₁ D₂
⇐-deterministic (D-ξ-·ₗ D₁) (D-ξ-·ₗ D₂) | refl = refl
⇐-deterministic (D-ξ-·ᵣ V D₁) (D-ξ-·ᵣ V₁ D₂) with ⇐-deterministic D₁ D₂
⇐-deterministic (D-ξ-·ᵣ V D₁) (D-ξ-·ᵣ V₁ D₂) | refl = refl
⇐-deterministic (D-β-· V-ƛ _) (D-β-· V-ƛ _) = refl
⇐-deterministic (D-β-· V-# _) (D-β-· V-# _) = refl
⇐-deterministic (D-ξ-+ₗ D₁) (D-ξ-+ₗ D₂) with ⇐-deterministic D₁ D₂
⇐-deterministic (D-ξ-+ₗ D₁) (D-ξ-+ₗ D₂) | refl = refl
⇐-deterministic (D-ξ-+ᵣ V D₁) (D-ξ-+ᵣ V₁ D₂) with ⇐-deterministic D₁ D₂
⇐-deterministic (D-ξ-+ᵣ V D₁) (D-ξ-+ᵣ V₁ D₂) | refl = refl
⇐-deterministic (D-β-+ V-ƛ _) (D-β-+ V-ƛ _) = refl
⇐-deterministic (D-β-+ V-# _) (D-β-+ V-# _) = refl
⇐-deterministic (D-ξ-φ D₁) (D-ξ-φ D₂) with ⇐-deterministic D₁ D₂
⇐-deterministic (D-ξ-φ D₁) (D-ξ-φ D₂) | refl = refl
⇐-deterministic (D-β-φ V-ƛ) (D-β-φ V-ƛ) = refl
⇐-deterministic (D-β-φ V-#) (D-β-φ V-#) = refl
⇐-deterministic (D-ξ-δ D₁) (D-ξ-δ D₂) with ⇐-deterministic D₁ D₂
⇐-deterministic (D-ξ-δ D₁) (D-ξ-δ D₂) | refl = refl
⇐-deterministic (D-β-δ V-ƛ) (D-β-δ V-ƛ) = refl
⇐-deterministic (D-β-δ V-#) (D-β-δ V-#) = refl

⇥-deterministic : _⇥_ deterministic
⇥-deterministic (step I₁ D₁ (¬F₁ , A₁) T₁ C₁) (step I₂ D₂ (¬F₂ , A₂) T₂ C₂)
           with ⇝-deterministic I₁ I₂
... | refl with ⇒-deterministic D₁ D₂
... | refl with ⊢⊣-deterministic A₁ A₂
... | refl with →-deterministic T₁ T₂
... | refl with ⇐-deterministic C₁ C₂
... | refl
    = refl
⇥-deterministic (step I₁ D₁ (F₁ , _) T₁ C₁) (skip I₂ D₂ (inj₁ F₂) T₂ C₂ S₂)
           with ⇝-deterministic I₁ I₂
... | refl with ⇒-deterministic D₁ D₂
... | refl = ⊥-elim (F₁ F₂)
⇥-deterministic (step I₁ D₁ (F₁ , A₁) T₁ C₁) (skip I₂ D₂ (inj₂ A₂) T₂ C₂ S₂)
           with ⇝-deterministic I₁ I₂
... | refl with ⇒-deterministic D₁ D₂
... | refl with ⊢⊣-deterministic A₁ A₂
... | ()
⇥-deterministic (step (I-V V-ƛ) () A₁ T₁ C₁) (done V-ƛ)
⇥-deterministic (step (I-V V-#) () A₁ T₁ C₁) (done V-#)
⇥-deterministic (skip I₁ D₁ (inj₁ F₁) T₁ C₁ S₁) (step I₂ D₂ (F₂ , A₂) T₂ C₂)
           with ⇝-deterministic I₁ I₂
... | refl with ⇒-deterministic D₁ D₂
... | refl
    = ⊥-elim (F₂ F₁)
⇥-deterministic (skip I₁ D₁ (inj₂ A₁) T₁ C₁ S₁) (step I₂ D₂ (F₂ , A₂) T₂ C₂)
           with ⇝-deterministic I₁ I₂
... | refl with ⇒-deterministic D₁ D₂
... | refl with ⊢⊣-deterministic A₁ A₂
... | ()
⇥-deterministic (skip I₁ D₁ (inj₁ F₁) T₁ C₁ S₁) (skip I₂ D₂ A₂ T₂ C₂ S₂)
           with ⇝-deterministic I₁ I₂
... | refl with ⇒-deterministic D₁ D₂
... | refl with →-deterministic T₁ T₂
... | refl with ⇐-deterministic C₁ C₂
... | refl with ⇥-deterministic S₁ S₂
... | refl
    = refl
⇥-deterministic (skip I₁ D₁ (inj₂ A₁) T₁ C₁ S₁) (skip I₂ D₂ A₂ T₂ C₂ S₂)
           with ⇝-deterministic I₁ I₂
... | refl with ⇒-deterministic D₁ D₂
... | refl with →-deterministic T₁ T₂
... | refl with ⇐-deterministic C₁ C₂
... | refl with ⇥-deterministic S₁ S₂
... | refl
    = refl
⇥-deterministic (skip (I-V V-ƛ) () (inj₁ F₁) T₁ C₁ S₁) (done V-ƛ)
⇥-deterministic (skip (I-V V-#) () (inj₁ F₁) T₁ C₁ S₁) (done V-#)
⇥-deterministic (skip (I-V V-ƛ) () (inj₂ A₁) T₁ C₁ S₁) (done V-ƛ)
⇥-deterministic (skip (I-V V-#) () (inj₂ A₁) T₁ C₁ S₁) (done V-#)
⇥-deterministic (done V-ƛ) (step (I-V V-ƛ) () A₂ T₂ C₂)
⇥-deterministic (done V-#) (step (I-V V-#) () A₂ T₂ C₂)
⇥-deterministic (done V-ƛ) (skip (I-V V-ƛ) () A₂ T₂ C₂ S₂)
⇥-deterministic (done V-#) (skip (I-V V-#) () A₂ T₂ C₂ S₂)
⇥-deterministic (done V-ƛ) (done V-ƛ) = refl
⇥-deterministic (done V-#) (done V-#) = refl
