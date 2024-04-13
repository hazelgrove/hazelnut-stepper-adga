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

  record Filter : Set where
    inductive
    field
      pat : Pat
      act : Act
      gas : Gas

  record Residue : Set where
    field
      act : Act
      gas : Gas
      lvl : ℕ

  record Behavioral (T : Set) : Set where
    field
      act : T → Act
      gas : T → Gas

  instance
    BehavioralFilter : Behavioral Filter
    Behavioral.act BehavioralFilter = Filter.act
    Behavioral.gas BehavioralFilter = Filter.gas

    BehavioralResidue : Behavioral Residue
    Behavioral.act BehavioralResidue = Residue.act
    Behavioral.gas BehavioralResidue = Residue.gas

  act : {T : Set} ⦃ BehavioralT : Behavioral T ⦄ → T → Act
  act ⦃ BehavioralT ⦄ = Behavioral.act BehavioralT

  gas : {T : Set} ⦃ BehavioralT : Behavioral T ⦄ → T → Gas
  gas ⦃ BehavioralT ⦄ = Behavioral.gas BehavioralT

  infix  5 ƛ_
  infixl 7 _+_
  infixl 8 _·_
  infix  9 `_

  data Exp where
    `_  : (x : ℕ) → Exp
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
    ƛ_  : (e : Exp) → Pat
    _·_ : (l : Pat) → (r : Pat) → Pat
    #_  : (n : ℕ)   → Pat
    _+_ : (l : Pat) → (r : Pat) → Pat

  data _value : Exp → Set where
    V-ƛ : ∀ {e}
      → (ƛ e) value

  data _filter : Exp → Set where
    F-φ : ∀ {f e}
      → φ f e filter
    F-δ : ∀ {r e}
      → δ r e filter
