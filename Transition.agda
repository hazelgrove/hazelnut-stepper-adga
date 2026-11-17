module Transition where

open import Base
open import Substitution using (applyₑ)
open import Data.Nat using (_+_)

infix 4 _—→_

data _—→_ : Exp → Exp → Set where
  T-β-· : ∀ {e v}
    → (V : v value)
    → (ƛ e) `· v —→ applyₑ e 0 v

  T-β-+ : ∀ {nₗ nᵣ}
    → # nₗ `+ # nᵣ —→ # (nₗ + nᵣ)

  T-β-φ : ∀ {f v}
    → (V : v value)
    → φ f v —→ v

  T-β-δ : ∀ {r v}
    → (V : v value)
    → δ r v —→ v

  T-β-μ : ∀ {e}
    → μ e —→ applyₑ e 0 (μ e)
