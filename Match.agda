module Match where

open import Base
open import Data.Nat using (_≟_)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no; _×-dec_)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

strip : Exp → Exp
strip (` x) = ` x
strip (ƛ e) = ƛ (strip e)
strip (l `· r) = (strip l) `· (strip r)
strip (# n) = # n
strip (l `+ r) = (strip l) `+ (strip r)
strip (φ f e) = strip e
strip (δ r e) = strip e
strip (μ e) = μ (strip e)

strip-δ : Exp → Exp
strip-δ (` x) = ` x
strip-δ (ƛ e) = ƛ (strip-δ e)
strip-δ (l `· r) = (strip-δ l) `· (strip-δ r)
strip-δ (# n) = # n
strip-δ (l `+ r) = (strip-δ l) `+ (strip-δ r)
strip-δ (φ f e) = φ f (strip-δ e)
strip-δ (δ r e) = strip-δ e
strip-δ (μ e) = μ (strip-δ e)

infix 4 _matches_

data _matches_ : Pat → Exp → Set where
  M-E : ∀ {e}
    → $e matches e

  M-V : ∀ {v}
    → v value
    → $v matches v

  M-` : ∀ {i}
    → (` i) matches (` i)

  M-# : ∀ {n}
    → (# n) matches (# n)

  M-· : ∀ {pₗ pᵣ eₗ eᵣ}
    → pₗ matches eₗ
    → pᵣ matches eᵣ
    → (pₗ `· pᵣ) matches (eₗ `· eᵣ)

  M-+ : ∀ {pₗ pᵣ eₗ eᵣ}
    → pₗ matches eₗ
    → pᵣ matches eᵣ
    → (pₗ `+ pᵣ) matches (eₗ `+ eᵣ)

  M-ƛ : ∀ {p e}
    → p matches e
    → (ƛ p) matches (ƛ e)

  M-μ : ∀ {p e}
    → p matches e
    → (μ p) matches (μ e)

  M-φ : ∀ {p f e}
    → p matches e
    → p matches (φ f e)

  M-δ : ∀ {p r e}
    → p matches e
    → p matches (δ r e)

unwrap-φ : ∀ {p f e} → p matches (φ f e) → p matches e
unwrap-φ M-E = M-E
unwrap-φ (M-V ())
unwrap-φ (M-φ m) = m

unwrap-δ : ∀ {p r e} → p matches (δ r e) → p matches e
unwrap-δ M-E = M-E
unwrap-δ (M-V ())
unwrap-δ (M-δ m) = m

infix 4 _matches?_

_matches?_ : (p : Pat) → (e : Exp) → Dec (p matches e)
p matches? φ f e = map′ M-φ unwrap-φ (p matches? e)
p matches? δ r e = map′ M-δ unwrap-δ (p matches? e)
$e matches? e = yes M-E
$v matches? (` i) = no (λ { (M-V ()) })
$v matches? (ƛ e) = yes (M-V V-ƛ)
$v matches? (eₗ `· eᵣ) = no (λ { (M-V ()) })
$v matches? (# n) = yes (M-V V-#)
$v matches? (eₗ `+ eᵣ) = no (λ { (M-V ()) })
$v matches? (μ e) = no (λ { (M-V ()) })
(` i) matches? (` j) with i ≟ j
(` i) matches? (` .i) | yes refl = yes M-`
(` i) matches? (` j) | no i≢j = no (λ { M-` → i≢j refl })
(ƛ p) matches? (ƛ e) = map′ M-ƛ (λ { (M-ƛ m) → m }) (p matches? e)
(pₗ `· pᵣ) matches? (eₗ `· eᵣ) =
  map′ (λ { (mₗ , mᵣ) → M-· mₗ mᵣ }) (λ { (M-· mₗ mᵣ) → mₗ , mᵣ })
    ((pₗ matches? eₗ) ×-dec (pᵣ matches? eᵣ))
(# n) matches? (# m) with n ≟ m
(# n) matches? (# .n) | yes refl = yes M-#
(# n) matches? (# m) | no n≢m = no (λ { M-# → n≢m refl })
(pₗ `+ pᵣ) matches? (eₗ `+ eᵣ) =
  map′ (λ { (mₗ , mᵣ) → M-+ mₗ mᵣ }) (λ { (M-+ mₗ mᵣ) → mₗ , mᵣ })
    ((pₗ matches? eₗ) ×-dec (pᵣ matches? eᵣ))
(μ p) matches? (μ e) = map′ M-μ (λ { (M-μ m) → m }) (p matches? e)
(` i) matches? (ƛ e) = no (λ ())
(` i) matches? (eₗ `· eᵣ) = no (λ ())
(` i) matches? (# m) = no (λ ())
(` i) matches? (eₗ `+ eᵣ) = no (λ ())
(` i) matches? (μ e) = no (λ ())
(ƛ p) matches? (` j) = no (λ ())
(ƛ p) matches? (eₗ `· eᵣ) = no (λ ())
(ƛ p) matches? (# m) = no (λ ())
(ƛ p) matches? (eₗ `+ eᵣ) = no (λ ())
(ƛ p) matches? (μ e) = no (λ ())
(pₗ `· pᵣ) matches? (` j) = no (λ ())
(pₗ `· pᵣ) matches? (ƛ e) = no (λ ())
(pₗ `· pᵣ) matches? (# m) = no (λ ())
(pₗ `· pᵣ) matches? (eₗ `+ eᵣ) = no (λ ())
(pₗ `· pᵣ) matches? (μ e) = no (λ ())
(# n) matches? (` j) = no (λ ())
(# n) matches? (ƛ e) = no (λ ())
(# n) matches? (eₗ `· eᵣ) = no (λ ())
(# n) matches? (eₗ `+ eᵣ) = no (λ ())
(# n) matches? (μ e) = no (λ ())
(pₗ `+ pᵣ) matches? (` j) = no (λ ())
(pₗ `+ pᵣ) matches? (ƛ e) = no (λ ())
(pₗ `+ pᵣ) matches? (eₗ `· eᵣ) = no (λ ())
(pₗ `+ pᵣ) matches? (# m) = no (λ ())
(pₗ `+ pᵣ) matches? (μ e) = no (λ ())
(μ p) matches? (` j) = no (λ ())
(μ p) matches? (ƛ e) = no (λ ())
(μ p) matches? (eₗ `· eᵣ) = no (λ ())
(μ p) matches? (# m) = no (λ ())
(μ p) matches? (eₗ `+ eᵣ) = no (λ ())
