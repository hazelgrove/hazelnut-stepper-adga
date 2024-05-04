open import Core
open import Data.Nat using (ℕ; _>_; _≟_; _<?_; zero; suc; pred; _≡ᵇ_; z≤n; s≤s; _≤_; _<_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; _≡_; cong; cong₂)
open import Data.Bool using (Bool; not; _∧_; false)
open import Data.Fin using (Fin)

module Subst where
  ↑ₙ : (c : ℕ) → (d : ℕ) → ℕ → ℕ
  ↑ₙ zero    zero    x       = x
  ↑ₙ zero    (suc d) x       = suc (↑ₙ zero d x)
  ↑ₙ (suc c) d       zero    = zero
  ↑ₙ (suc c) d       (suc x) = suc (↑ₙ c d x)

  ↑ₙ⁰ : ∀ {c n : ℕ} → ↑ₙ c 0 n ≡ n
  ↑ₙ⁰ {zero}  {n}     = refl
  ↑ₙ⁰ {suc c} {zero}  = refl
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

  ↓ₙ : (c : ℕ) → (d : ℕ) → (x : ℕ) → ℕ
  ↓ₙ zero zero zero = zero
  ↓ₙ zero (suc d) zero = zero
  ↓ₙ zero zero (suc x) = suc x
  ↓ₙ zero (suc d) (suc x) = ↓ₙ zero d x
  ↓ₙ (suc c) zero zero = zero
  ↓ₙ (suc c) (suc d) zero = zero
  ↓ₙ (suc c) zero (suc x) = suc x
  ↓ₙ (suc c) (suc d) (suc x) = ↓ₙ c d x

  ↓ₑ : (c : ℕ) → (d : ℕ) → (e : Exp) → Exp
  ↓ₚ : (c : ℕ) → (d : ℕ) → (p : Pat) → Pat

  ↓ₑ c d (` x)     = ` (↓ₙ c x d)
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
  patternize (` i)   = ` i
  -- patternize (! x)   = ! x
  patternize (ƛ e)   = ƛ e
  patternize (l · r) = patternize l · patternize r
  patternize (# n)   = # n
  patternize (l + r) = patternize l + patternize r
  patternize (φ f e) = patternize e
  patternize (δ r e) = patternize e

  -- [_↦_]ₑ_ : ℕ → Var → Exp → Exp
  -- [_↦_]ₚ_ : ℕ → Var → Pat → Pat

  -- [ k ↦ x ]ₑ (` i)     with i ≟ k
  -- [ k ↦ x ]ₑ (` i)     | yes _ = ! x
  -- [ k ↦ x ]ₑ (` i)     | no  _ = ` i
  -- [ k ↦ x ]ₑ (! y)     = ! y
  -- [ k ↦ x ]ₑ (ƛ e)     = ƛ ([ (suc k) ↦ x ]ₑ e)
  -- [ k ↦ x ]ₑ (eₗ · eᵣ) = ([ k ↦ x ]ₑ eₗ) · ([ k ↦ x ]ₑ eᵣ)
  -- [ k ↦ x ]ₑ (# n)     = # n
  -- [ k ↦ x ]ₑ (eₗ + eᵣ) = ([ k ↦ x ]ₑ eₗ) + ([ k ↦ x ]ₑ eᵣ)
  -- [ k ↦ x ]ₑ φ f e     = φ (([ k ↦ x ]ₚ proj₁ f) , proj₂ f) ([ k ↦ x ]ₑ e)
  -- [ k ↦ x ]ₑ δ r e     = [ k ↦ x ]ₑ e

  -- [ k ↦ x ]ₚ $e        = $e
  -- [ k ↦ x ]ₚ $v        = $v
  -- [ k ↦ x ]ₚ (` i)     with i ≟ k
  -- [ k ↦ x ]ₚ (` i)     | yes _ = ! x
  -- [ k ↦ x ]ₚ (` i)     | no  _ = ` i
  -- [ k ↦ x ]ₚ (! y)     = ! y
  -- [ k ↦ x ]ₚ (ƛ p)     = ƛ ([ (suc k) ↦ x ]ₑ p)
  -- [ k ↦ x ]ₚ (pₗ · pᵣ) = ([ k ↦ x ]ₚ pₗ) · ([ k ↦ x ]ₚ pᵣ)
  -- [ k ↦ x ]ₚ (# n)     = # n
  -- [ k ↦ x ]ₚ (pₗ + pᵣ) = ([ k ↦ x ]ₚ pₗ) + ([ k ↦ x ]ₚ pᵣ)

  -- [_↤_]ₑ_ : ℕ → Var → Exp → Exp
  -- [_↤_]ₚ_ : ℕ → Var → Pat → Pat

  -- [ k ↤ x ]ₑ (` i)     = ` i
  -- [ k ↤ x ]ₑ (! y)     with (x Data.String.≟ y)
  -- [ k ↤ x ]ₑ (! y)     | yes _ = ` k
  -- [ k ↤ x ]ₑ (! y)     | no  _ = ! y
  -- [ k ↤ x ]ₑ (ƛ e)     = ƛ ([ (suc k) ↤ x ]ₑ e)
  -- [ k ↤ x ]ₑ (eₗ · eᵣ) = ([ k ↤ x ]ₑ eₗ) · ([ k ↤ x ]ₑ eᵣ)
  -- [ k ↤ x ]ₑ (# n)     = # n
  -- [ k ↤ x ]ₑ (eₗ + eᵣ) = ([ k ↤ x ]ₑ eₗ) + ([ k ↤ x ]ₑ eᵣ)
  -- [ k ↤ x ]ₑ φ f e     = φ (([ k ↤ x ]ₚ proj₁ f) , proj₂ f) ([ k ↤ x ]ₑ e)
  -- [ k ↤ x ]ₑ δ r e     = [ k ↤ x ]ₑ e

  -- [ k ↤ x ]ₚ $e        = $e
  -- [ k ↤ x ]ₚ $v        = $v
  -- [ k ↤ x ]ₚ (` i)     = ` i
  -- [ k ↤ x ]ₚ (! y)     with (x Data.String.≟ y)
  -- [ k ↤ x ]ₚ (! y)     | yes _ = ` k
  -- [ k ↤ x ]ₚ (! y)     | no  _ = ! y
  -- [ k ↤ x ]ₚ (ƛ p)     = ƛ ([ (suc k) ↤ x ]ₑ p)
  -- [ k ↤ x ]ₚ (pₗ · pᵣ) = ([ k ↤ x ]ₚ pₗ) · ([ k ↤ x ]ₚ pᵣ)
  -- [ k ↤ x ]ₚ (# n)     = # n
  -- [ k ↤ x ]ₚ (pₗ + pᵣ) = ([ k ↤ x ]ₚ pₗ) + ([ k ↤ x ]ₚ pᵣ)

  -- data _closed-at_ : Exp → ℕ → Set where
  --   LC-` : ∀ {i k}
  --     → i < k
  --     → (` i) closed-at k
  --   LC-! : ∀ {x k}
  --     → (! x) closed-at k
  --   LC-· : ∀ {eₗ eᵣ k}
  --     → eₗ closed-at k
  --     → eᵣ closed-at k
  --     → (eₗ · eᵣ) closed-at k
  --   LC-ƛ : ∀ {k e}
  --     → e closed-at k
  --     → (ƛ e) closed-at (suc k)

  -- _closed : Exp → Set
  -- e closed = e closed-at 0

  -- fvₑ : Exp → List Var
  -- fvₚ : Pat → List Var
  -- fvₑ (` i)     = []
  -- fvₑ (! x)     = x ∷ []
  -- fvₑ (ƛ e)     = fvₑ e
  -- fvₑ (eₗ · eᵣ) = (fvₑ eₗ) ++ (fvₑ eᵣ)
  -- fvₑ (# n)     = []
  -- fvₑ (eₗ + eᵣ) = (fvₑ eₗ) ++ (fvₑ eᵣ)
  -- fvₑ (φ f e)   = fvₚ (proj₁ f) ++ (fvₑ e)
  -- fvₑ (δ r e)   = fvₑ e

  -- fvₚ $e        = []
  -- fvₚ $v        = []
  -- fvₚ (` i)     = []
  -- fvₚ (! x)     = x ∷ []
  -- fvₚ (ƛ e)     = fvₑ e
  -- fvₚ (eₗ · eᵣ) = (fvₚ eₗ) ++ (fvₚ eᵣ)
  -- fvₚ (# n)     = []
  -- fvₚ (eₗ + eᵣ) = (fvₚ eₗ) ++ (fvₚ eᵣ)

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
