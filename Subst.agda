open import Core
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; _≡_)
open import Data.Nat using (ℕ; _>_; _≟_; _<?_; zero; suc; pred)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)

module Subst where
  ↑ₑ : Exp → ℕ → (d : ℕ) → ⦃ _ : d > 0 ⦄ → Exp
  ↑ₚ : Pat → ℕ → (d : ℕ) → ⦃ _ : d > 0 ⦄ → Pat

  ↑ₑ (` x)     c d with x <? c
  ↑ₑ (` x)     c d | yes _ = ` x
  ↑ₑ (` x)     c d | no  _ = ` (x Data.Nat.+ d)
  ↑ₑ (ƛ e)     c d = ƛ ↑ₑ e (suc c) d
  ↑ₑ (eₗ · eᵣ) c d = ↑ₑ eₗ c d · ↑ₑ eᵣ c d
  ↑ₑ (# n)     c d = # n
  ↑ₑ (eₗ + eᵣ) c d = (↑ₑ eₗ c d) + (↑ₑ eᵣ c d)
  ↑ₑ (φ f e)   c d = φ record f { pat = ↑ₚ (Core.Filter.pat f) c d } (↑ₑ e c d)
  ↑ₑ (δ r e)   c d = δ r (↑ₑ e c d)

  ↑ₚ $e        c d = $e
  ↑ₚ $v        c d = $v
  ↑ₚ (` x)     c d with x <? c
  ↑ₚ (` x)     c d | yes _ = ` x
  ↑ₚ (` x)     c d | no  _ = ` (d Data.Nat.+ x)
  ↑ₚ (ƛ e)     c d = ƛ ↑ₑ e (suc c) d
  ↑ₚ (pₗ · pᵣ) c d = ↑ₚ pₗ c d · ↑ₚ pᵣ c d
  ↑ₚ (# n)     c d = # n
  ↑ₚ (pₗ + pᵣ) c d = ↑ₚ pₗ c d + ↑ₚ pᵣ c d

  ↓ₑ : Exp → ℕ → ℕ → Exp
  ↓ₚ : Pat → ℕ → ℕ → Pat

  ↓ₑ (` x)     c d with x <? c
  ↓ₑ (` x)     c d | yes _ = ` x
  ↓ₑ (` x)     c d | no  _ = ` (x Data.Nat.∸ d)
  ↓ₑ (ƛ e)     c d = ƛ ↓ₑ e (suc c) d
  ↓ₑ (eₗ · eᵣ) c d = ↓ₑ eₗ c d · ↓ₑ eᵣ c d
  ↓ₑ (# n)     c d = # n
  ↓ₑ (eₗ + eᵣ) c d = (↓ₑ eₗ c d) + (↓ₑ eᵣ c d)
  ↓ₑ (φ f e)   c d = φ record f { pat = ↓ₚ (Core.Filter.pat f) c d } (↓ₑ e c d)
  ↓ₑ (δ r e)   c d = δ r (↓ₑ e c d)

  ↓ₚ $e        c d = $e
  ↓ₚ $v        c d = $v
  ↓ₚ (` x)     c d with x <? c
  ↓ₚ (` x)     c d | yes _ = ` x
  ↓ₚ (` x)     c d | no  _ = ` (x Data.Nat.∸ d)
  ↓ₚ (ƛ e)     c d = ƛ ↓ₑ e (suc c) d
  ↓ₚ (pₗ · pᵣ) c d = ↓ₚ pₗ c d · ↓ₚ pᵣ c d
  ↓ₚ (# n)     c d = # n
  ↓ₚ (pₗ + pᵣ) c d = ↓ₚ pₗ c d + ↓ₚ pᵣ c d

  patternize : Core.Exp → Core.Pat
  patternize (` x) = ` x
  patternize (ƛ e) = ƛ e
  patternize (l · r) = patternize l · patternize r
  patternize (# n) = # n
  patternize (l + r) = patternize l + patternize r
  patternize (φ f e) = patternize e
  patternize (δ r e) = patternize e

  instance
    _ : 1 > 0
    _ = Data.Nat.s≤s Data.Nat.z≤n

  [_/_]ₑ_ : Core.Exp → ℕ → Core.Exp → Core.Exp
  [_/_]ₚ_ : Core.Exp → ℕ → Core.Pat → Core.Pat

  [_/_]ₑ_ v y (` x) with x ≟ y
  [_/_]ₑ_ v y (` x) | yes refl = v
  [_/_]ₑ_ v y (` x) | no  x≢y  = ` x
  [_/_]ₑ_ v y (ƛ e) = ƛ ([_/_]ₑ_ (↑ₑ v 0 1) (suc y) e)
  [_/_]ₑ_ v y (l · r) = ([_/_]ₑ_ v y l) · ([_/_]ₑ_ v y r)
  [_/_]ₑ_ v y (# n) = # n
  [_/_]ₑ_ v y (l + r) = ([_/_]ₑ_ v y l) + ([_/_]ₑ_ v y r)
  [_/_]ₑ_ v y (φ f e) = φ record f { pat = [_/_]ₚ_ v y (Core.Filter.pat f) } ([_/_]ₑ_ v y e)
  [_/_]ₑ_ v y (δ r e) = δ r ([_/_]ₑ_ v y e)

  [_/_]ₚ_ v y $e = $e
  [_/_]ₚ_ v y $v = $v
  [_/_]ₚ_ v y (` x) with x ≟ y
  [_/_]ₚ_ v y (` x) | yes refl = patternize v
  [_/_]ₚ_ v y (` x) | no  x≢y  = ` x
  [_/_]ₚ_ v y (ƛ e) = ƛ ([_/_]ₑ_ (↑ₑ v 0 1) (suc y) e)
  [_/_]ₚ_ v y (l · r) = ([_/_]ₚ_ v y l) · ([_/_]ₚ_ v y r)
  [_/_]ₚ_ v y (# n) = # n
  [_/_]ₚ_ v y (l + r) = ([_/_]ₚ_ v y l) + ([_/_]ₚ_ v y r)

  record Term {T : Set} : Set₁ where
    field
      ↑ : T → ℕ → (d : ℕ) → ⦃ _ : d > 0 ⦄ → T
      ↓ : T → ℕ → (d : ℕ) → T
      subst : Core.Exp → ℕ → T → T

  instance
    TermExp : Term {Core.Exp}
    TermExp =
      record
        { ↑ = ↑ₑ ; ↓ = ↓ₑ ; subst = [_/_]ₑ_ }

    TermPat : Term {Core.Pat}
    TermPat =
      record
        { ↑ = ↑ₚ ; ↓ = ↓ₚ ; subst = [_/_]ₚ_ }

  _↑_ : {T : Set} ⦃ TermT : Term {T} ⦄ → (t : T) → (c : ℕ) → (d : ℕ) → ⦃ _ : d > 0 ⦄ → T
  _↑_ ⦃ TermT ⦄ = Term.↑ TermT

  _↓_ : {T : Set} ⦃ TermT : Term {T} ⦄ → (t : T) → (c : ℕ) → (d : ℕ) → T
  _↓_ ⦃ TermT ⦄ = Term.↓ TermT

  [_/_]_ : {T : Set} ⦃ TermT : Term {T} ⦄ → (v : Core.Exp) → (n : ℕ) → T → T
  [_/_]_ ⦃ TermT ⦄ = Term.subst TermT
