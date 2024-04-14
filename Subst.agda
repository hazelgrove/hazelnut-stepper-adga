open import Core
open import Data.Nat using (ℕ; _>_; _≟_; _<?_; zero; suc; pred; _≡ᵇ_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; _≡_; cong; cong₂)
open import Data.Bool using (Bool; not; _∧_; false)

module Subst where
  deadₑ : (y : ℕ) → (e : Exp) → Bool
  deadₚ : (y : ℕ) → (p : Pat) → Bool

  deadₑ y (` x) = not (x ≡ᵇ y)
  deadₑ y (ƛ e) = deadₑ (suc y) e
  deadₑ y (eₗ · eᵣ) = deadₑ y eₗ ∧ deadₑ y eᵣ
  deadₑ y (# n)     = false
  deadₑ y (eₗ + eᵣ) = deadₑ y eₗ ∧ deadₑ y eᵣ
  deadₑ y (φ f e)   = deadₚ y (proj₁ f) ∧ deadₑ y e
  deadₑ y (δ r e)   = deadₑ y e

  deadₚ y $e = false
  deadₚ y $v = false
  deadₚ y (` x) = not (x ≡ᵇ y)
  deadₚ y (ƛ e) = deadₑ (suc y) e
  deadₚ y (pₗ · pᵣ) = deadₚ y pₗ ∧ deadₚ y pᵣ
  deadₚ y (# n) = false
  deadₚ y (pₗ + pᵣ) = deadₚ y pₗ ∧ deadₚ y pᵣ

  ↑ₙ : (c : ℕ) → (d : ℕ) → ℕ → ℕ
  ↑ₙ zero    zero    x       = x
  ↑ₙ zero    (suc d) x       = suc (↑ₙ zero d x)
  ↑ₙ (suc c) d       zero    = zero
  ↑ₙ (suc c) d       (suc x) = suc (↑ₙ c d x)

  ↑ₙ⁰ : ∀ {c n : ℕ} → ↑ₙ c 0 n ≡ n
  ↑ₙ⁰ {zero} {n} = refl
  ↑ₙ⁰ {suc c} {zero} = refl
  ↑ₙ⁰ {suc c} {suc n} = cong suc (↑ₙ⁰ {c} {n})

  ↑ₙ-cascade : ∀ {c d n : ℕ} → ↑ₙ c 1 (↑ₙ c d n) ≡ ↑ₙ c (suc d) n
  ↑ₙ-cascade {zero}  {d} {n}     = refl
  ↑ₙ-cascade {suc c} {d} {zero}  = refl
  ↑ₙ-cascade {suc c} {d} {suc n} = cong suc (↑ₙ-cascade {c} {d} {n})

  ↑ₑ : (c : ℕ) → (d : ℕ) → Exp → Exp
  ↑ₚ : (c : ℕ) → (d : ℕ) → Pat → Pat

  ↑ₑ-cascade : ∀ {c d : ℕ} {e : Exp} → ↑ₑ c 1 (↑ₑ c d e) ≡ ↑ₑ c (suc d) e
  ↑ₚ-cascade : ∀ {c d : ℕ} {p : Pat} → ↑ₚ c 1 (↑ₚ c d p) ≡ ↑ₚ c (suc d) p

  ↑ₑ c d (` x)     = ` (↑ₙ c d x)
  ↑ₑ c d (ƛ e)     = ƛ ↑ₑ (suc c) d e
  ↑ₑ c d (eₗ · eᵣ) = ↑ₑ c d eₗ · ↑ₑ c d eᵣ
  ↑ₑ c d (# n)     = # n
  ↑ₑ c d (eₗ + eᵣ) = ↑ₑ c d eₗ + ↑ₑ c d eᵣ
  ↑ₑ c d (φ f e)   = φ (↑ₚ c d (proj₁ f) , (proj₂ f)) (↑ₑ c d e)
  ↑ₑ c d (δ r e)   = δ r (↑ₑ c d e)

  ↑ₑ-cascade {c} {d} {` x}     = cong `_ (↑ₙ-cascade {c} {d} {x})
  ↑ₑ-cascade {c} {d} {ƛ e}     = cong ƛ_ ↑ₑ-cascade
  ↑ₑ-cascade {c} {d} {eₗ · eᵣ} = cong₂ _·_ ↑ₑ-cascade ↑ₑ-cascade
  ↑ₑ-cascade {c} {d} {# n}     = refl
  ↑ₑ-cascade {c} {d} {eₗ + eᵣ} = cong₂ _+_ ↑ₑ-cascade ↑ₑ-cascade
  ↑ₑ-cascade {c} {d} {φ f e}   = cong₂ (λ p → φ (p , proj₂ f)) ↑ₚ-cascade ↑ₑ-cascade
  ↑ₑ-cascade {c} {d} {δ r e}   = cong (δ r) ↑ₑ-cascade

  ↑ₚ c d $e        = $e
  ↑ₚ c d $v        = $v
  ↑ₚ c d (` x)     = ` (↑ₙ c d x)
  ↑ₚ c d (ƛ e)     = ƛ ↑ₑ (suc c) d e
  ↑ₚ c d (pₗ · pᵣ) = ↑ₚ c d pₗ · ↑ₚ c d pᵣ
  ↑ₚ c d (# n)     = # n
  ↑ₚ c d (pₗ + pᵣ) = ↑ₚ c d pₗ + ↑ₚ c d pᵣ

  ↑ₚ-cascade {c} {d} {$e} = refl
  ↑ₚ-cascade {c} {d} {$v} = refl
  ↑ₚ-cascade {c} {d} {` x} = cong `_ (↑ₙ-cascade {c} {d} {x})
  ↑ₚ-cascade {c} {d} {ƛ e} = cong ƛ_ ↑ₑ-cascade
  ↑ₚ-cascade {c} {d} {p · p₁} = cong₂ _·_ ↑ₚ-cascade ↑ₚ-cascade
  ↑ₚ-cascade {c} {d} {# n} = refl
  ↑ₚ-cascade {c} {d} {p + p₁} = cong₂ _+_ ↑ₚ-cascade ↑ₚ-cascade

  ↓ₑ : (c : ℕ) → (d : ℕ) → Exp → Exp
  ↓ₚ : (c : ℕ) → (d : ℕ) → Pat → Pat

  ↓ₑ c d (` x)     with x <? c
  ↓ₑ c d (` x)     | yes _ = ` x
  ↓ₑ c d (` x)     | no  _ = ` (x Data.Nat.∸ d)
  ↓ₑ c d (ƛ e)     = ƛ ↓ₑ (suc c) d e
  ↓ₑ c d (eₗ · eᵣ) = ↓ₑ c d eₗ · ↓ₑ c d eᵣ
  ↓ₑ c d (# n)     = # n
  ↓ₑ c d (eₗ + eᵣ) = (↓ₑ c d eₗ) + (↓ₑ c d eᵣ)
  ↓ₑ c d (φ f e)   = φ (↓ₚ c d (proj₁ f) , proj₂ f) (↓ₑ c d e)
  ↓ₑ c d (δ r e)   = δ r (↓ₑ c d e)

  ↓ₚ c d $e        = $e
  ↓ₚ c d $v        = $v
  ↓ₚ c d (` x)     with x <? c
  ↓ₚ c d (` x)     | yes _ = ` x
  ↓ₚ c d (` x)     | no  _ = ` (x Data.Nat.∸ d)
  ↓ₚ c d (ƛ e)     = ƛ ↓ₑ (suc c) d e
  ↓ₚ c d (pₗ · pᵣ) = ↓ₚ c d pₗ · ↓ₚ c d pᵣ
  ↓ₚ c d (# n)     = # n
  ↓ₚ c d (pₗ + pᵣ) = ↓ₚ c d pₗ + ↓ₚ c d pᵣ

  patternize : Exp → Pat
  patternize (` x)   = ` x
  patternize (ƛ e)   = ƛ e
  patternize (l · r) = patternize l · patternize r
  patternize (# n)   = # n
  patternize (l + r) = patternize l + patternize r
  patternize (φ f e) = patternize e
  patternize (δ r e) = patternize e

  [_/_]ₑ_ : Exp → ℕ → Exp → Exp
  [_/_]ₚ_ : Exp → ℕ → Pat → Pat

  [_/_]ₑ_ v y (` x)   with x ≟ y
  [_/_]ₑ_ v y (` x)   | yes refl = v
  [_/_]ₑ_ v y (` x)   | no  x≢y  = ` x
  [_/_]ₑ_ v y (ƛ e)   = ƛ ([_/_]ₑ_ (↑ₑ 0 1 v) (suc y) e)
  [_/_]ₑ_ v y (l · r) = ([_/_]ₑ_ v y l) · ([_/_]ₑ_ v y r)
  [_/_]ₑ_ v y (# n)   = # n
  [_/_]ₑ_ v y (l + r) = ([_/_]ₑ_ v y l) + ([_/_]ₑ_ v y r)
  [_/_]ₑ_ v y (φ f e) = φ ([_/_]ₚ_ v y (proj₁ f) , proj₂ f) ([_/_]ₑ_ v y e)
  [_/_]ₑ_ v y (δ r e) = δ r ([_/_]ₑ_ v y e)

  [_/_]ₚ_ v y $e      = $e
  [_/_]ₚ_ v y $v      = $v
  [_/_]ₚ_ v y (` x)   with x ≟ y
  [_/_]ₚ_ v y (` x)   | yes refl = patternize v
  [_/_]ₚ_ v y (` x)   | no  x≢y  = ` x
  [_/_]ₚ_ v y (ƛ e)   = ƛ ([_/_]ₑ_ (↑ₑ 0 1 v) (suc y) e)
  [_/_]ₚ_ v y (l · r) = ([_/_]ₚ_ v y l) · ([_/_]ₚ_ v y r)
  [_/_]ₚ_ v y (# n)   = # n
  [_/_]ₚ_ v y (l + r) = ([_/_]ₚ_ v y l) + ([_/_]ₚ_ v y r)

  record Term (T : Set) : Set₁ where
    field
      ↑ : ℕ → (d : ℕ) → T → T
      ↓ : ℕ → (d : ℕ) → T → T
      subst : Exp → ℕ → T → T

  ↑ : {T : Set} ⦃ TermT : Term T ⦄ → (c : ℕ) → (d : ℕ) → T → T
  ↑ ⦃ TermT ⦄ = Term.↑ TermT

  Cascade : ∀ (T : Set) ⦃ TermT : Term T ⦄ → Set
  Cascade T = ∀ {c d : ℕ} {t : T} → ↑ c 1 (↑ c d t) ≡ ↑ c (suc d) t

  instance
    TermExp : Term (Core.Exp)
    TermExp =
      record
        { ↑ = ↑ₑ ; ↓ = ↓ₑ ; subst = [_/_]ₑ_ }

    TermPat : Term (Core.Pat)
    TermPat =
      record
        { ↑ = ↑ₚ ; ↓ = ↓ₚ ; subst = [_/_]ₚ_ }

  instance
    CascadeExp : Cascade Exp
    CascadeExp = ↑ₑ-cascade

  ↑-cascade : ∀ {T : Set} ⦃ TermT : Term T ⦄ ⦃ CascadeT : Cascade T ⦄ {c d : ℕ} {e : T} → ↑ c 1 (↑ c d e) ≡ ↑ c (suc d) e
  ↑-cascade ⦃ CascadeT = CascadeT ⦄ = CascadeT

  ↓ : {T : Set} ⦃ TermT : Term T ⦄ → (c : ℕ) → (d : ℕ) → T → T
  ↓ ⦃ TermT ⦄ = Term.↓ TermT

  [_/_]_ : {T : Set} ⦃ TermT : Term T ⦄ → (v : Core.Exp) → (n : ℕ) → T → T
  [_/_]_ ⦃ TermT ⦄ = Term.subst TermT
