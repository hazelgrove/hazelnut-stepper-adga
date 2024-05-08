module Match where

open import Base
open import Substitution
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Relation.Nullary using (Dec; yes; no; ¬_; _×-dec_)
import Relation.Nullary.Decidable as Dec

-- strip e
-- Strips off filter and residue from an expression.
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

-- infix 4 _matches?_

-- _matches?_ : (p : Pat) → (e : Exp) → Dec (p matches e)
-- $e matches? ` x   = yes M-E
-- $e matches? ƛ e   = yes M-E
-- $e matches? l · r = yes M-E
-- $e matches? (# n) = yes M-E
-- $e matches? l + r = yes M-E
-- $e matches? φ f e = yes M-E
-- $e matches? δ r e = yes M-E
-- $v matches? ` x = no (λ { (M-V ()) })
-- $v matches? ƛ e = yes (M-V V-ƛ)
-- $v matches? l · r = no λ { (M-V ()) }
-- $v matches? (# n) = yes (M-V V-#)
-- $v matches? l + r = no λ { (M-V ()) }
-- $v matches? φ f e = no λ { (M-V ()) }
-- $v matches? δ r e = no λ { (M-V ()) }
-- ` x matches? e = no (λ ())
-- ƛ p matches? ` x = no (λ ())
-- ƛ p matches? ƛ e   = {!!}
-- ƛ p matches? l · r = no (λ ())
-- ƛ p matches? (# n) = no (λ ())
-- ƛ p matches? l + r = no (λ ())
-- ƛ p matches? φ f e = no (λ ())
-- ƛ p matches? δ r e = no (λ ())
-- p · p₁ matches? e = {!!}
-- (# n) matches? e = no (λ ())
-- p + p₁ matches? e = no (λ ())
