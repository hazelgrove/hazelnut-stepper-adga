module Base where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Relation.Nullary using (Dec; yes; no)

data Act : Set where
  ⊳ : Act
  ∥ : Act

data Gas : Set where
  𝟙 : Gas
  ⋆ : Gas

data Exp : Set
data Pat : Set

Filter  : Set
Filter  = Pat × Act × Gas

Residue : Set
Residue = Act × ℕ

infix  5 ƛ_
infixl 7 _`+_
infixl 8 _`·_
infix  9 `_

data Exp where
  `_   : (i : ℕ) → Exp
  ƛ_   : (e : Exp) → Exp
  _`·_ : (l : Exp) → (r : Exp) → Exp
  #_   : (n : ℕ) → Exp
  _`+_ : (l : Exp) → (r : Exp) → Exp
  φ    : (f : Filter) → (e : Exp) → Exp
  δ    : (r : Residue) → (e : Exp) → Exp
  μ    : (e : Exp) → Exp

data Pat where
  $e   : Pat
  $v   : Pat
  `_   : (i : ℕ) → Pat
  ƛ_   : (p : Pat) → Pat
  _`·_ : (l : Pat) → (r : Pat) → Pat
  #_   : (n : ℕ) → Pat
  _`+_ : (l : Pat) → (r : Pat) → Pat
  μ    : (p : Pat) → Pat

data _value : Exp → Set where
  V-ƛ : ∀ {e : Exp}
    → (ƛ e) value
  V-# : ∀ {n : ℕ}
    → (# n) value

_value? : (e : Exp) → Dec (e value)
(` i) value? = no λ ()
(ƛ e) value? = yes V-ƛ
(e `· e₁) value? = no (λ ())
(# n) value? = yes V-#
(e `+ e₁) value? = no (λ ())
φ f e value? = no (λ ())
δ r e value? = no (λ ())
μ e value? = no (λ ())
