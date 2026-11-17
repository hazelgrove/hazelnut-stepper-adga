module Ctx where

open import Base

infixl 7 _+ₗ_ _+ᵣ_
infixl 8 _·ₗ_ _·ᵣ_

data Ctx : Set where
  ∘    : Ctx
  _·ₗ_ : (c : Ctx) → (r : Exp) → Ctx
  _·ᵣ_ : (l : Exp) → (c : Ctx) → Ctx
  _+ₗ_ : (c : Ctx) → (r : Exp) → Ctx
  _+ᵣ_ : (l : Exp) → (c : Ctx) → Ctx
  φ    : (f : Filter) → (c : Ctx) → Ctx
  δ    : (r : Residue) → (c : Ctx) → Ctx

compose : Ctx → Exp → Exp
compose ∘        e = e
compose (c ·ₗ r) e = compose c (e `· r)
compose (l ·ᵣ c) e = compose c (l `· e)
compose (c +ₗ r) e = compose c (e `+ r)
compose (l +ᵣ c) e = compose c (l `+ e)
compose (φ f c)  e = compose c (φ f e)
compose (δ r c)  e = compose c (δ r e)
