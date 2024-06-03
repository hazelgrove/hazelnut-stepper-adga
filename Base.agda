module Base where

open import Data.Nat using (ℕ)
open import Data.Nat.Induction using (<′-wellFounded)
open import Data.Product using (_×_)

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
Residue = Act × Gas × ℕ

infix  5 ƛ_
infixl 7 _+_
infixl 8 _·_
infix  9 `_

data Exp where
  `_  : (i : ℕ) → Exp
  ƛ_  : (e : Exp) → Exp
  _·_ : (l : Exp) → (r : Exp) → Exp
  #_  : (n : ℕ) → Exp
  _+_ : (l : Exp) → (r : Exp) → Exp
  φ   : (f : Filter) → (e : Exp) → Exp
  δ   : (r : Residue) → (e : Exp) → Exp

data Pat where
  $e  : Pat
  $v  : Pat
  `_  : (i : ℕ) → Pat
  ƛ_  : (e : Exp) → Pat
  _·_ : (l : Pat) → (r : Pat) → Pat
  #_  : (n : ℕ) → Pat
  _+_ : (l : Pat) → (r : Pat) → Pat

data _value : Exp → Set where
  V-ƛ : ∀ {e : Exp}
    → (ƛ e) value
  V-# : ∀ {n : ℕ}
    → (# n) value

data Val : Set where
  #_ : (n : ℕ) → Val
  ƛ_ : (e : Exp) → Val

data _filter-like : Exp → Set where
  F-φ : ∀ {f e}
    → φ f e filter-like

  F-δ : ∀ {r e}
    → δ r e filter-like
