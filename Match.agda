open import Core
open import Subst
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

module Match where
  strip : Exp → Exp
  strip (` x) = ` x
  strip (ƛ e) = ƛ (strip e)
  strip (l · r) = (strip l) · (strip r)
  strip (# n) = # n
  strip (l + r) = (strip l) + (strip r)
  strip (φ f e) = strip e
  strip (δ r e) = strip e

  infix 4 _matches_

  data _matches_ : Pat → Exp → Set where
    M-E : ∀ {e}
      → $e matches e

    M-V : ∀ {v}
      → v value
      → $v matches v

    M-· : ∀ {pₗ pᵣ eₗ eᵣ}
      → pₗ matches eₗ
      → pᵣ matches eᵣ
      → (pₗ · pᵣ) matches (eₗ · eᵣ)

    M-ƛ : ∀ {eₚ eₑ}
      → (strip eₚ) ≡ (strip eₑ)
      → (ƛ eₚ) matches (ƛ eₑ)
