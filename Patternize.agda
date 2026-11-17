module Patternize where

open import Base
open import Substitution using (patternize)
open import Match
open import Function using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

private
  ƛ-inj : ∀ {a b : Exp} → (ƛ a) ≡ (ƛ b) → a ≡ b
  ƛ-inj refl = refl

  μ-inj : ∀ {a b : Exp} → μ a ≡ μ b → a ≡ b
  μ-inj refl = refl

  ·-injₗ : ∀ {a b c d : Exp} → (a `· b) ≡ (c `· d) → a ≡ c
  ·-injₗ refl = refl

  ·-injᵣ : ∀ {a b c d : Exp} → (a `· b) ≡ (c `· d) → b ≡ d
  ·-injᵣ refl = refl

  +-injₗ : ∀ {a b c d : Exp} → (a `+ b) ≡ (c `+ d) → a ≡ c
  +-injₗ refl = refl

  +-injᵣ : ∀ {a b c d : Exp} → (a `+ b) ≡ (c `+ d) → b ≡ d
  +-injᵣ refl = refl

patternize-sound : ∀ (e₁ e₂ : Exp)
  → patternize e₁ matches e₂
  → strip e₁ ≡ strip e₂
patternize-sound (φ f e₁) e₂ m = patternize-sound e₁ e₂ m
patternize-sound (δ r e₁) e₂ m = patternize-sound e₁ e₂ m
patternize-sound e₁ (φ f e₂) m = patternize-sound e₁ e₂ (unwrap-φ m)
patternize-sound e₁ (δ r e₂) m = patternize-sound e₁ e₂ (unwrap-δ m)
patternize-sound (` i) (` .i) M-` = refl
patternize-sound (ƛ e₁) (ƛ e₂) (M-ƛ m) = cong ƛ_ (patternize-sound e₁ e₂ m)
patternize-sound (l₁ `· r₁) (l₂ `· r₂) (M-· mₗ mᵣ) =
  cong₂ _`·_ (patternize-sound l₁ l₂ mₗ) (patternize-sound r₁ r₂ mᵣ)
patternize-sound (# n) (# .n) M-# = refl
patternize-sound (l₁ `+ r₁) (l₂ `+ r₂) (M-+ mₗ mᵣ) =
  cong₂ _`+_ (patternize-sound l₁ l₂ mₗ) (patternize-sound r₁ r₂ mᵣ)
patternize-sound (μ e₁) (μ e₂) (M-μ m) = cong μ (patternize-sound e₁ e₂ m)
patternize-sound (` i₁) (ƛ e₂) ()
patternize-sound (` i₁) (l₂ `· r₂) ()
patternize-sound (` i₁) (# n₂) ()
patternize-sound (` i₁) (l₂ `+ r₂) ()
patternize-sound (` i₁) (μ e₂) ()
patternize-sound (ƛ e₁) (` i₂) ()
patternize-sound (ƛ e₁) (l₂ `· r₂) ()
patternize-sound (ƛ e₁) (# n₂) ()
patternize-sound (ƛ e₁) (l₂ `+ r₂) ()
patternize-sound (ƛ e₁) (μ e₂) ()
patternize-sound (l₁ `· r₁) (` i₂) ()
patternize-sound (l₁ `· r₁) (ƛ e₂) ()
patternize-sound (l₁ `· r₁) (# n₂) ()
patternize-sound (l₁ `· r₁) (l₂ `+ r₂) ()
patternize-sound (l₁ `· r₁) (μ e₂) ()
patternize-sound (# n₁) (` i₂) ()
patternize-sound (# n₁) (ƛ e₂) ()
patternize-sound (# n₁) (l₂ `· r₂) ()
patternize-sound (# n₁) (l₂ `+ r₂) ()
patternize-sound (# n₁) (μ e₂) ()
patternize-sound (l₁ `+ r₁) (` i₂) ()
patternize-sound (l₁ `+ r₁) (ƛ e₂) ()
patternize-sound (l₁ `+ r₁) (l₂ `· r₂) ()
patternize-sound (l₁ `+ r₁) (# n₂) ()
patternize-sound (l₁ `+ r₁) (μ e₂) ()
patternize-sound (μ e₁) (` i₂) ()
patternize-sound (μ e₁) (ƛ e₂) ()
patternize-sound (μ e₁) (l₂ `· r₂) ()
patternize-sound (μ e₁) (# n₂) ()
patternize-sound (μ e₁) (l₂ `+ r₂) ()

patternize-complete : ∀ (e₁ e₂ : Exp)
  → strip e₁ ≡ strip e₂
  → patternize e₁ matches e₂
patternize-complete (φ f e₁) e₂ eq = patternize-complete e₁ e₂ eq
patternize-complete (δ r e₁) e₂ eq = patternize-complete e₁ e₂ eq
patternize-complete e₁ (φ f e₂) eq = M-φ (patternize-complete e₁ e₂ eq)
patternize-complete e₁ (δ r e₂) eq = M-δ (patternize-complete e₁ e₂ eq)
patternize-complete (` i) (` .i) refl = M-`
patternize-complete (ƛ e₁) (ƛ e₂) eq = M-ƛ (patternize-complete e₁ e₂ (ƛ-inj eq))
patternize-complete (l₁ `· r₁) (l₂ `· r₂) eq =
  M-· (patternize-complete l₁ l₂ (·-injₗ eq)) (patternize-complete r₁ r₂ (·-injᵣ eq))
patternize-complete (# n) (# .n) refl = M-#
patternize-complete (l₁ `+ r₁) (l₂ `+ r₂) eq =
  M-+ (patternize-complete l₁ l₂ (+-injₗ eq)) (patternize-complete r₁ r₂ (+-injᵣ eq))
patternize-complete (μ e₁) (μ e₂) eq = M-μ (patternize-complete e₁ e₂ (μ-inj eq))
patternize-complete (` i₁) (ƛ e₂) ()
patternize-complete (` i₁) (l₂ `· r₂) ()
patternize-complete (` i₁) (# n₂) ()
patternize-complete (` i₁) (l₂ `+ r₂) ()
patternize-complete (` i₁) (μ e₂) ()
patternize-complete (ƛ e₁) (` i₂) ()
patternize-complete (ƛ e₁) (l₂ `· r₂) ()
patternize-complete (ƛ e₁) (# n₂) ()
patternize-complete (ƛ e₁) (l₂ `+ r₂) ()
patternize-complete (ƛ e₁) (μ e₂) ()
patternize-complete (l₁ `· r₁) (` i₂) ()
patternize-complete (l₁ `· r₁) (ƛ e₂) ()
patternize-complete (l₁ `· r₁) (# n₂) ()
patternize-complete (l₁ `· r₁) (l₂ `+ r₂) ()
patternize-complete (l₁ `· r₁) (μ e₂) ()
patternize-complete (# n₁) (` i₂) ()
patternize-complete (# n₁) (ƛ e₂) ()
patternize-complete (# n₁) (l₂ `· r₂) ()
patternize-complete (# n₁) (l₂ `+ r₂) ()
patternize-complete (# n₁) (μ e₂) ()
patternize-complete (l₁ `+ r₁) (` i₂) ()
patternize-complete (l₁ `+ r₁) (ƛ e₂) ()
patternize-complete (l₁ `+ r₁) (l₂ `· r₂) ()
patternize-complete (l₁ `+ r₁) (# n₂) ()
patternize-complete (l₁ `+ r₁) (μ e₂) ()
patternize-complete (μ e₁) (` i₂) ()
patternize-complete (μ e₁) (ƛ e₂) ()
patternize-complete (μ e₁) (l₂ `· r₂) ()
patternize-complete (μ e₁) (# n₂) ()
patternize-complete (μ e₁) (l₂ `+ r₂) ()

patternize-matches⇔strip-≡ : ∀ (e₁ e₂ : Exp)
  → (patternize e₁ matches e₂) ⇔ (strip e₁ ≡ strip e₂)
patternize-matches⇔strip-≡ e₁ e₂ =
  mk⇔ (patternize-sound e₁ e₂) (patternize-complete e₁ e₂)
