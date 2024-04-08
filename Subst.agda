import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl)
open import Data.Nat using (ℕ; _≟_; _<?_; zero; suc; pred)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)

module Subst where

  module Inner where
    open import Core

    _↑-exp_ : Exp → ℕ → Exp
    _↑-pat_ : Pat → ℕ → Pat

    (` x) ↑-exp n with x <? n
    (` x) ↑-exp n | yes _ = (` x)
    (` x) ↑-exp n | no  _ = ` (suc x)
    (ƛ e) ↑-exp n = ƛ (e ↑-exp (suc n))
    (l · r) ↑-exp n = (l ↑-exp n) · (r ↑-exp n)
    (# n) ↑-exp _ = # n
    (l + r) ↑-exp n = (l ↑-exp n) + (r ↑-exp n)
    φ (p , ag) e ↑-exp n = φ ((p ↑-pat n) , ag) (e ↑-exp n)
    δ r e ↑-exp n = δ r (e ↑-exp n)

    $e ↑-pat n = $e
    $v ↑-pat n = $v
    (` x) ↑-pat n with x <? n
    (` x) ↑-pat n | yes _ = ` x
    (` x) ↑-pat n | no  _ = ` (suc x)
    (ƛ e) ↑-pat n = ƛ (e ↑-exp (suc n))
    (l · r) ↑-pat n = (l ↑-pat n) · (r ↑-pat n)
    (# n) ↑-pat _ = # n
    (l + r) ↑-pat n = (l ↑-pat n) + (r ↑-pat n)

    _↓-exp_ : Exp → ℕ → Exp
    _↓-pat_ : Pat → ℕ → Pat

    (` x) ↓-exp n with x <? n
    (` x) ↓-exp n | yes _ = ` x
    (` x) ↓-exp n | no  _ = ` (pred x)
    (ƛ e) ↓-exp n = ƛ (e ↓-exp (suc n))
    (l · r) ↓-exp n = (l ↓-exp n) · (r ↓-exp n)
    (# n) ↓-exp _ = # n
    (l + r) ↓-exp n = (l ↓-exp n) + (r ↓-exp n)
    (φ (p , ag) e) ↓-exp n = φ ((p ↓-pat n) , ag) (e ↓-exp n)
    (δ r e) ↓-exp n = δ r (e ↓-exp n)

    $e ↓-pat n = $e
    $v ↓-pat n = $v
    (` x) ↓-pat n with x <? n
    (` x) ↓-pat n | yes _ = ` x
    (` x) ↓-pat n | no  _ = ` pred x
    (ƛ e) ↓-pat n = ƛ (e ↓-exp (suc n))
    (l · r) ↓-pat n = (l ↓-pat n) · (r ↓-pat n)
    (# n) ↓-pat _ = # n
    (l + r) ↓-pat n = (l ↓-pat n) · (r ↓-pat n)

    toPat : Exp → Pat
    toPat (` x) = ` x
    toPat (ƛ e) = ƛ e
    toPat (l · r) = toPat l · toPat r
    toPat (# n) = # n
    toPat (l + r) = toPat l + toPat r
    toPat (φ f e) = toPat e
    toPat (δ r e) = toPat e

    subst-exp : Exp → ℕ → Exp → Exp
    subst-pat : Pat → ℕ → Exp → Pat

    subst-exp (` x) y v with x ≟ y
    subst-exp (` x) y v | yes refl = v
    subst-exp (` x) y v | no  x≢y  = ` x
    subst-exp (ƛ e) y v = ƛ (subst-exp e (suc y) (v ↑-exp ℕ.zero))
    subst-exp (l · r) y v = (subst-exp l y v) · (subst-exp r y v)
    subst-exp (# n) y v = # n
    subst-exp (l + r) y v = (subst-exp l y v) + (subst-exp r y v)
    subst-exp (φ (p , ag) e) y v = φ ((subst-pat p y v) , ag) (subst-exp e y v)
    subst-exp (δ r e) y v = δ r (subst-exp e y v)

    subst-pat $e y v = $e
    subst-pat $v y v = $v
    subst-pat (` x) y v with x ≟ y
    subst-pat (` x) y v | yes refl = toPat v
    subst-pat (` x) y v | no  x≢y  = ` x
    subst-pat (ƛ e) y v = ƛ (subst-exp e (suc y) (v ↑-exp ℕ.zero))
    subst-pat (l · r) y v = (subst-pat l y v) · (subst-pat r y v)
    subst-pat (# n) y v = # n
    subst-pat (l + r) y v = (subst-pat l y v) + (subst-pat r y v)

  open Inner
  open import Core using ()

  record Term (T : Set) : Set where
    field
      shift-up   : T → ℕ → T
      shift-down : T → ℕ → T
      subst      : T → ℕ → Core.Exp → T

  _↑_ : {T : Set} ⦃ TermT : Term T ⦄ → T → ℕ → T
  _↑_ ⦃ TermT ⦄ e n = Term.shift-up TermT e n

  _↓_ : {T : Set} ⦃ TermT : Term T ⦄ → T → ℕ → T
  _↓_ ⦃ TermT ⦄ e n = Term.shift-down TermT e n

  [_/_]_ : {T : Set} ⦃ TermT : Term T ⦄ → T → ℕ → Core.Exp → T
  [_/_]_ ⦃ TermT = TermT ⦄ v x e = Term.subst TermT v x e

  instance
    TermExp : Term Core.Exp
    TermExp = record { shift-up = _↑-exp_ ; shift-down = _↓-exp_ ; subst = subst-exp }

  instance
    TermPat : Term Core.Pat
    TermPat = record { shift-up = _↑-pat_ ; shift-down = _↓-pat_ ; subst = subst-pat }

  -- module Exp where
  --   open import Core
  --   infixl 3 _↑_

  --   _↑_ : Exp → ℕ → Exp
  --   e ↑ n = e ↑-exp n

  --   _↓_ : Exp → ℕ → Exp
  --   e ↓ n = e ↓-exp n

  --   [_/_]_ : Exp → ℕ → Exp → Exp
  --   [ v / x ] e = subst-exp e x v

  -- module Pat where
  --   open import Core
  --   infixl 3 _↑_

  --   _↑_ : Pat → ℕ → Pat
  --   p ↑ n = p ↑-pat n

  --   [_/_]_ : Exp → ℕ → Pat → Pat
  --   [ v / x ] e = subst-pat e x v
