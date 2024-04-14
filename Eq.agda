open import Core
open import Data.Nat using (ℕ) renaming (_≟_ to _≟-nat_)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Nullary using (Dec; yes; no; _×-dec_) renaming (map′ to map-dec)

module Eq where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq public using (_≡_; refl; cong)

  DecEq : ∀ (T : Set) → Set
  DecEq T = (l : T) → (r : T) → Dec (l ≡ r)

  instance
    DecEqNat : DecEq ℕ
    DecEqNat l r = l ≟-nat r

  _≟_ : {T : Set} ⦃ DecEqT : DecEq T ⦄ → (l : T) → (r : T) → Dec (l ≡ r)
  _≟_ ⦃ DecEqT ⦄ = DecEqT

  _≟-act_ : (aₗ : Act) → (aᵣ : Act) → Dec (aₗ ≡ aᵣ)
  ⊳ ≟-act ⊳ = yes refl
  ⊳ ≟-act ∥ = no (λ ())
  ∥ ≟-act ⊳ = no (λ ())
  ∥ ≟-act ∥ = yes refl

  instance
    DecEqAct : DecEq Act
    DecEqAct = _≟-act_

  _≟-gas_ : (gₗ : Gas) → (gᵣ : Gas) → Dec (gₗ ≡ gᵣ)
  𝟙 ≟-gas 𝟙 = yes refl
  𝟙 ≟-gas ⋆ = no (λ ())
  ⋆ ≟-gas 𝟙 = no (λ ())
  ⋆ ≟-gas ⋆ = yes refl

  instance
    DecEqGas : DecEq Gas
    DecEqGas = _≟-gas_

  _≟-exp_ : (eₗ : Exp) → (eᵣ : Exp) → Dec (eₗ ≡ eᵣ)
  _≟-pat_ : (pₗ : Pat) → (pᵣ : Pat) → Dec (pₗ ≡ pᵣ)

  -- instance
  --   DecEqProduct : ∀ {A B} ⦃ DecEqA : DecEq A ⦄ ⦃ DecEqB : DecEq B ⦄ → DecEq (A × B)
  --   DecEq.eq DecEqProduct (aₗ , aᵣ) (bₗ , bᵣ) with (aₗ ≟ bₗ) ×-dec (aᵣ ≟ bᵣ)
  --   DecEq.eq DecEqProduct (aₗ , aᵣ) (aₗ , aᵣ) | yes (refl , refl) = yes refl
  --   DecEq.eq DecEqProduct (aₗ , aᵣ) (bₗ , bᵣ) | no a≢b = no λ { refl → a≢b (refl , refl) }

  (` x) ≟-exp (` y) with x ≟-nat y
  (` x) ≟-exp (` y) | yes refl = yes refl
  (` x) ≟-exp (` y) | no x≢y = no λ { refl → x≢y refl }
  (` x) ≟-exp (ƛ e) = no (λ ())
  (` x) ≟-exp (l · r) = no (λ ())
  (` x) ≟-exp (# n) = no (λ ())
  (` x) ≟-exp (l + r) = no (λ ())
  (` x) ≟-exp φ f e = no (λ ())
  (` x) ≟-exp δ r e = no (λ ())
  (ƛ e) ≟-exp (` x) = no (λ ())
  (ƛ l) ≟-exp (ƛ r) with l ≟-exp r
  (ƛ l) ≟-exp (ƛ r) | yes refl = yes refl
  (ƛ l) ≟-exp (ƛ r) | no l≢r = no λ { refl → l≢r refl }
  (ƛ e) ≟-exp (l · r) = no (λ ())
  (ƛ e) ≟-exp (# n) = no (λ ())
  (ƛ e) ≟-exp (l + r) = no (λ ())
  (ƛ _) ≟-exp φ f e = no (λ ())
  (ƛ _) ≟-exp δ r e = no (λ ())
  (lₗ · lᵣ) ≟-exp (` x) = no (λ ())
  (lₗ · lᵣ) ≟-exp (ƛ e) = no (λ ())
  (lₗ · lᵣ) ≟-exp (rₗ · rᵣ) with (lₗ ≟-exp rₗ) ×-dec (lᵣ ≟-exp rᵣ)
  (lₗ · lᵣ) ≟-exp (lₗ · lᵣ) | yes (refl , refl) = yes refl
  (lₗ · lᵣ) ≟-exp (rₗ · rᵣ) | no l≢r = no λ { refl → l≢r (refl , refl) }
  (lₗ · lᵣ) ≟-exp (# n) = no (λ ())
  (lₗ · lᵣ) ≟-exp (rₗ + rᵣ) = no (λ ())
  (lₗ · lᵣ) ≟-exp φ f e = no (λ ())
  (lₗ · lᵣ) ≟-exp δ r e = no (λ ())
  (# n) ≟-exp (` x) = no (λ ())
  (# n) ≟-exp (ƛ r) = no (λ ())
  (# n) ≟-exp (r · r₁) = no (λ ())
  (# n) ≟-exp (# m) with n ≟-nat m
  (# n) ≟-exp (# m) | yes refl = yes refl
  (# n) ≟-exp (# m) | no n≢m = no λ { refl → n≢m refl }
  (# n) ≟-exp (r + r₁) = no (λ ())
  (# n) ≟-exp φ f r = no (λ ())
  (# n) ≟-exp δ r r₁ = no (λ ())
  (lₗ + lᵣ) ≟-exp (` x) = no (λ ())
  (lₗ + lᵣ) ≟-exp (ƛ e) = no (λ ())
  (lₗ + lᵣ) ≟-exp (rₗ · rᵣ) = no (λ ())
  (lₗ + lᵣ) ≟-exp (# n) = no (λ ())
  (lₗ + lᵣ) ≟-exp (rₗ + rᵣ) with (lₗ ≟-exp rₗ) ×-dec (lᵣ ≟-exp rᵣ)
  (lₗ + lᵣ) ≟-exp (lₗ + lᵣ) | yes (refl , refl) = yes refl
  (lₗ + lᵣ) ≟-exp (rₗ + rᵣ) | no l≢r = no λ { refl → l≢r (refl , refl) }
  (lₗ + lᵣ) ≟-exp φ f e = no (λ ())
  (lₗ + lᵣ) ≟-exp δ r e = no (λ ())
  φ f l ≟-exp (` x) = no (λ ())
  φ f l ≟-exp (ƛ r) = no (λ ())
  φ f l ≟-exp (r · r₁) = no (λ ())
  φ f l ≟-exp (# n) = no (λ ())
  φ f l ≟-exp (r + r₁) = no (λ ())
  φ fₗ eₗ ≟-exp φ fᵣ eᵣ with ({!!}) ×-dec (eₗ ≟-exp eᵣ)
  φ fₗ eₗ ≟-exp φ fᵣ eᵣ | yes (x , refl) = yes x
  φ fₗ eₗ ≟-exp φ fᵣ eᵣ | no l≢r = no λ { refl → l≢r (refl , refl) }
  φ f l ≟-exp δ r r₁ = no (λ ())
  δ r eₗ ≟-exp (` x) = no (λ ())
  δ r eₗ ≟-exp (ƛ eᵣ) = no (λ ())
  δ r eₗ ≟-exp (eᵣ · eᵣ₁) = no (λ ())
  δ r eₗ ≟-exp (# n) = no (λ ())
  δ r eₗ ≟-exp (eᵣ + eᵣ₁) = no (λ ())
  δ r eₗ ≟-exp φ f eᵣ = no (λ ())
  δ rₗ eₗ ≟-exp δ rᵣ eᵣ with ({!!}) ×-dec (eₗ ≟-exp eᵣ)
  δ rₗ eₗ ≟-exp δ rᵣ eᵣ | yes (x , refl) = yes {!!}
  δ rₗ eₗ ≟-exp δ rᵣ eᵣ | no l≢r = no (λ { refl → l≢r (refl , refl) })

  $e ≟-pat $e = yes refl
  $e ≟-pat $v = no (λ ())
  $e ≟-pat (` x) = no (λ ())
  $e ≟-pat (ƛ e) = no (λ ())
  $e ≟-pat (pᵣ · pᵣ₁) = no (λ ())
  $e ≟-pat (# n) = no (λ ())
  $e ≟-pat (pᵣ + pᵣ₁) = no (λ ())
  $v ≟-pat $e = no (λ ())
  $v ≟-pat $v = yes refl
  $v ≟-pat (` x) = no (λ ())
  $v ≟-pat (ƛ e) = no (λ ())
  $v ≟-pat (pᵣ · pᵣ₁) = no (λ ())
  $v ≟-pat (# n) = no (λ ())
  $v ≟-pat (pᵣ + pᵣ₁) = no (λ ())
  (` x) ≟-pat $e = no (λ ())
  (` x) ≟-pat $v = no (λ ())
  (` x) ≟-pat (` y) with x ≟-nat y
  (` x) ≟-pat (` y) | yes refl = yes refl
  (` x) ≟-pat (` y) | no x≢y = no (λ { refl → x≢y refl })
  (` x) ≟-pat (ƛ e) = no (λ ())
  (` x) ≟-pat (pᵣ · pᵣ₁) = no (λ ())
  (` x) ≟-pat (# n) = no (λ ())
  (` x) ≟-pat (pᵣ + pᵣ₁) = no (λ ())
  (ƛ e) ≟-pat $e = no (λ ())
  (ƛ e) ≟-pat $v = no (λ ())
  (ƛ e) ≟-pat (` x) = no (λ ())
  (ƛ eₗ) ≟-pat (ƛ eᵣ) with eₗ ≟-exp eᵣ
  (ƛ eₗ) ≟-pat (ƛ eᵣ) | yes refl = yes refl
  (ƛ eₗ) ≟-pat (ƛ eᵣ) | no l≢r = no λ { refl → l≢r refl }
  (ƛ e) ≟-pat (pᵣ · pᵣ₁) = no (λ ())
  (ƛ e) ≟-pat (# n) = no (λ ())
  (ƛ e) ≟-pat (pᵣ + pᵣ₁) = no (λ ())
  (pₗ · pₗ₁) ≟-pat $e = no (λ ())
  (pₗ · pₗ₁) ≟-pat $v = no (λ ())
  (pₗ · pₗ₁) ≟-pat (` x) = no (λ ())
  (pₗ · pₗ₁) ≟-pat (ƛ e) = no (λ ())
  (pₗ · pₗ₁) ≟-pat (pᵣ · pᵣ₁) = {!!}
  (pₗ · pₗ₁) ≟-pat (# n) = no (λ ())
  (pₗ · pₗ₁) ≟-pat (pᵣ + pᵣ₁) = no (λ ())
  (# n) ≟-pat $e = no (λ ())
  (# n) ≟-pat $v = no (λ ())
  (# n) ≟-pat (` x) = no (λ ())
  (# n) ≟-pat (ƛ e) = no (λ ())
  (# n) ≟-pat (pᵣ · pᵣ₁) = no (λ ())
  (# n) ≟-pat (# m) with n ≟-nat m
  (# n) ≟-pat (# m) | yes refl = yes refl
  (# n) ≟-pat (# m) | no n≢m = no λ { refl → n≢m refl }
  (# n) ≟-pat (pᵣ + pᵣ₁) = no (λ ())
  (pₗ + pₗ₁) ≟-pat $e = no (λ ())
  (pₗ + pₗ₁) ≟-pat $v = no (λ ())
  (pₗ + pₗ₁) ≟-pat (` x) = no (λ ())
  (pₗ + pₗ₁) ≟-pat (ƛ e) = no (λ ())
  (pₗ + pₗ₁) ≟-pat (pᵣ · pᵣ₁) = no (λ ())
  (pₗ + pₗ₁) ≟-pat (# n) = no (λ ())
  (pₗ + pₗ₁) ≟-pat (pᵣ + pᵣ₁) = {!!}

  instance
    DecEqExp : DecEq Exp
    DecEqExp = _≟-exp_

  instance
    DecEqPat : DecEq Pat
    DecEqPat = _≟-pat_

