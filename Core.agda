open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
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

  Filter : Set
  Filter = Pat × Act × Gas

  Residue : Set
  Residue = Act × Gas × ℕ

  infix  5 ƛ_
  infixl 7 _+_
  infixl 8 _·_
  infix  9 `_

  data Exp where
    `_  : (x : ℕ) → Exp
    !_  : (x : ℕ) → Exp
    ƛ_  : (e : Exp) → Exp
    _·_ : (l : Exp) → (r : Exp) → Exp
    #_  : (n : ℕ) → Exp
    _+_ : (l : Exp) → (r : Exp) → Exp
    φ   : (f : Filter) → (e : Exp) → Exp
    δ   : (r : Residue) → (e : Exp) → Exp

  data Pat where
    $e  : Pat
    $v  : Pat
    `_  : (x : ℕ)   → Pat
    !_  : (x : ℕ)   → Pat
    ƛ_  : (e : Exp) → Pat
    _·_ : (l : Pat) → (r : Pat) → Pat
    #_  : (n : ℕ)   → Pat
    _+_ : (l : Pat) → (r : Pat) → Pat

  infix 4 [_]
  infix 4 <_>

  data Term : Set → Set where
    [_] : Exp → Term Exp
    <_> : Pat → Term Pat

  data _value : Exp → Set where
    V-ƛ : ∀ {e}
      → (ƛ e) value

  data _filter : Exp → Set where
    F-φ : ∀ {f e}
      → φ f e filter
    F-δ : ∀ {r e}
      → δ r e filter
