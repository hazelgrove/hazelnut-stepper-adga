module Substitution where

open import Base
open import Data.Nat using (ℕ; zero; suc; _≟_; <-cmp; s≤s)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)

↑ₙ : (c : ℕ) → (d : ℕ) → ℕ → ℕ
↑ₙ zero    zero    x       = x
↑ₙ zero    (suc d) x       = suc (↑ₙ zero d x)
↑ₙ (suc c) d       zero    = zero
↑ₙ (suc c) d       (suc x) = suc (↑ₙ c d x)

↑ₑ : (c : ℕ) → (d : ℕ) → Exp → Exp
↑ₚ : (c : ℕ) → (d : ℕ) → Pat → Pat

↑ₑ c d (` x)     = ` (↑ₙ c d x)
↑ₑ c d (ƛ e)     = ƛ ↑ₑ (suc c) d e
↑ₑ c d (eₗ `· eᵣ) = ↑ₑ c d eₗ `· ↑ₑ c d eᵣ
↑ₑ c d (# n)     = # n
↑ₑ c d (eₗ `+ eᵣ) = ↑ₑ c d eₗ `+ ↑ₑ c d eᵣ
↑ₑ c d (φ f e)   = φ (↑ₚ c d (proj₁ f) , (proj₂ f)) (↑ₑ c d e)
↑ₑ c d (δ r e)   = δ r (↑ₑ c d e)
↑ₑ c d (μ e)     = μ (↑ₑ (suc c) d e)

↑ₚ c d $e        = $e
↑ₚ c d $v        = $v
↑ₚ c d (` x)     = ` (↑ₙ c d x)
↑ₚ c d (ƛ p)     = ƛ ↑ₚ (suc c) d p
↑ₚ c d (pₗ `· pᵣ) = ↑ₚ c d pₗ `· ↑ₚ c d pᵣ
↑ₚ c d (# n)     = # n
↑ₚ c d (pₗ `+ pᵣ) = ↑ₚ c d pₗ `+ ↑ₚ c d pᵣ
↑ₚ c d (μ p)     = μ (↑ₚ (suc c) d p)

patternize : Exp → Pat
patternize (` i)    = ` i
patternize (ƛ e)    = ƛ patternize e
patternize (l `· r) = patternize l `· patternize r
patternize (# n)    = # n
patternize (l `+ r) = patternize l `+ patternize r
patternize (φ f e)  = patternize e
patternize (δ r e)  = patternize e
patternize (μ e)    = μ (patternize e)

[_/_]ₑ_ : Exp → ℕ → Exp → Exp
[_/_]ₚ_ : Exp → ℕ → Pat → Pat

[_/_]ₑ_ v y (` x)   with x ≟ y
[_/_]ₑ_ v y (` x)   | yes refl = v
[_/_]ₑ_ v y (` x)   | no  x≢y  = ` x
[_/_]ₑ_ v y (ƛ e)   = ƛ ([_/_]ₑ_ (↑ₑ 0 1 v) (suc y) e)
[_/_]ₑ_ v y (l `· r) = ([_/_]ₑ_ v y l) `· ([_/_]ₑ_ v y r)
[_/_]ₑ_ v y (# n)   = # n
[_/_]ₑ_ v y (l `+ r) = ([_/_]ₑ_ v y l) `+ ([_/_]ₑ_ v y r)
[_/_]ₑ_ v y (φ f e) = φ ([_/_]ₚ_ v y (proj₁ f) , proj₂ f) ([_/_]ₑ_ v y e)
[_/_]ₑ_ v y (δ r e) = δ r ([_/_]ₑ_ v y e)
[_/_]ₑ_ v y (μ e)   = μ ([_/_]ₑ_ (↑ₑ 0 1 v) (suc y) e)

[_/_]ₚ_ v y $e      = $e
[_/_]ₚ_ v y $v      = $v
[_/_]ₚ_ v y (` x)   with x ≟ y
[_/_]ₚ_ v y (` x)   | yes refl = patternize v
[_/_]ₚ_ v y (` x)   | no  x≢y  = ` x
[_/_]ₚ_ v y (ƛ p)   = ƛ ([_/_]ₚ_ (↑ₑ 0 1 v) (suc y) p)
[_/_]ₚ_ v y (l `· r) = ([_/_]ₚ_ v y l) `· ([_/_]ₚ_ v y r)
[_/_]ₚ_ v y (# n)   = # n
[_/_]ₚ_ v y (l `+ r) = ([_/_]ₚ_ v y l) `+ ([_/_]ₚ_ v y r)
[_/_]ₚ_ v y (μ p)   = μ ([_/_]ₚ_ (↑ₑ 0 1 v) (suc y) p)

applyₙ : (i : ℕ) → (x : ℕ) → (v : Exp) → Exp
applyₙ i x v with <-cmp i x
applyₙ i       x v | tri< _ _ _       = ` i
applyₙ i       x v | tri≈ _ _ _       = v
applyₙ (suc i) x v | tri> _ _ (s≤s _) = ` i

applyₑ : Exp → ℕ → Exp → Exp
applyₚ : Pat → ℕ → Exp → Pat

applyₑ (` i)      x v = applyₙ i x v
applyₑ (ƛ e)      x v = ƛ applyₑ e (suc x) (↑ₑ 0 1 v)
applyₑ (eₗ `· eᵣ) x v = applyₑ eₗ x v `· applyₑ eᵣ x v
applyₑ (# n)      x v = # n
applyₑ (eₗ `+ eᵣ) x v = applyₑ eₗ x v `+ applyₑ eᵣ x v
applyₑ (φ f e)    x v = φ (applyₚ (proj₁ f) x v , proj₂ f) (applyₑ e x v)
applyₑ (δ r e)    x v = δ r (applyₑ e x v)
applyₑ (μ e)      x v = μ (applyₑ e (suc x) (↑ₑ 0 1 v))

applyₚ $e         x v = $e
applyₚ $v         x v = $v
applyₚ (` i)      x v = patternize (applyₙ i x v)
applyₚ (ƛ p)      x v = ƛ applyₚ p (suc x) (↑ₑ 0 1 v)
applyₚ (pₗ `· pᵣ) x v = applyₚ pₗ x v `· applyₚ pᵣ x v
applyₚ (# n)      x v = # n
applyₚ (pₗ `+ pᵣ) x v = applyₚ pₗ x v `+ applyₚ pᵣ x v
applyₚ (μ p)      x v = μ (applyₚ p (suc x) (↑ₑ 0 1 v))
