open import Nat
open import Data.String using (String)
open import Data.Product using (_×_)

module Core where
  data Act : Set where
    ⊳ : Act
    ∥ : Act

  data Gas : Set where
    𝟙 : Gas
    ⋆ : Gas

  data Exp : Set
  data Pat : Set

  Var : Set
  Var = String

  Filter  : Set
  Filter  = Pat × Act × Gas

  Residue : Set
  Residue = Act × Gas × Nat

  infix  5 ƛ_
  infixl 7 _+_
  infixl 8 _·_
  infix  9 `_

  data Exp where
    `_  : (i : Nat) → Exp
    -- !_  : (x : Var)  → Exp
    ƛ_  : (e : Exp) → Exp
    _·_ : (l : Exp) → (r : Exp) → Exp
    #_  : (n : Nat) → Exp
    _+_ : (l : Exp) → (r : Exp) → Exp
    φ   : (f : Filter) → (e : Exp) → Exp
    δ   : (r : Residue) → (e : Exp) → Exp

  data Pat where
    $e  : Pat
    $v  : Pat
    `_  : (i : Nat) → Pat
    -- !_  : (x : Var) → Pat
    ƛ_  : (e : Exp) → Pat
    _·_ : (l : Pat) → (r : Pat) → Pat
    #_  : (n : Nat) → Pat
    _+_ : (l : Pat) → (r : Pat) → Pat

  data _value : Exp → Set where
    V-ƛ : ∀ {e : Exp}
      → (ƛ e) value
    V-# : ∀ {n : Nat}
      → (# n) value

  data _filter : Exp → Set where
    F-φ : ∀ {f e}
      → φ f e filter

    F-δ : ∀ {r e}
      → δ r e filter
