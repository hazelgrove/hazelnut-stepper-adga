open import Data.String using (String)
open import Data.Nat using (ℕ; _+_; _≤_; _>_; _<_; s≤s; z≤n; _≤?_; _<?_; pred; suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Integer using (ℤ)
open import Data.Product using (_,_; _×_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_; _×-dec_)
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.Definitions using (tri<; tri>; tri≈)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; _≢_; cong₂; sym)
open import Function using (_↔_)

data Act : Set where
  eval : Act
  pause : Act

_≟-act_ : (a₁ : Act) → (a₂ : Act) → Dec (a₁ ≡ a₂)
eval ≟-act eval = yes refl
eval ≟-act pause = no λ ()
pause ≟-act eval = no λ ()
pause ≟-act pause = yes refl

data Gas : Set where
  𝟙 : Gas
  ⋆ : Gas

_≟-gas_ : (g₁ : Gas) → (g₂ : Gas) → Dec (g₁ ≡ g₂)
𝟙 ≟-gas 𝟙 = yes refl
𝟙 ≟-gas ⋆ = no λ ()
⋆ ≟-gas 𝟙 = no λ ()
⋆ ≟-gas ⋆ = yes refl

Id : Set
Id = ℕ

data Pat : Set
data Exp : Set

infix 5 ƛ_
infix 5 φ_⇒_
infix 5 δ_⇒_
infixl 7 _`+_
infixl 8 _`·_
infix 9 #_
infix 9 `_

data Pat where
  $e   : Pat
  $v   : Pat
  `_   : Id → Pat
  ƛ_   : Exp → Pat
  _`·_ : Pat → Pat → Pat
  #_   : ℕ → Pat
  _`+_ : Pat → Pat → Pat

_≟-pat_ : (p₁ : Pat) → (p₂ : Pat) → Dec (p₁ ≡ p₂)
_≟-exp_ : (e₁ : Exp) → (e₂ : Exp) → Dec (e₁ ≡ e₂)

$e ≟-pat $e = yes refl
$e ≟-pat $v = no λ ()
$e ≟-pat (` x) = no (λ ())
$e ≟-pat (ƛ x) = no (λ ())
$e ≟-pat (p₂ `· p₃) = no (λ ())
$e ≟-pat (# x) = no (λ ())
$e ≟-pat (p₂ `+ p₃) = no (λ ())
$v ≟-pat $e = no (λ ())
$v ≟-pat $v = yes refl
$v ≟-pat (` x) = no (λ ())
$v ≟-pat (ƛ x) = no (λ ())
$v ≟-pat (p₂ `· p₃) = no (λ ())
$v ≟-pat (# x) = no (λ ())
$v ≟-pat (p₂ `+ p₃) = no (λ ())
(` x) ≟-pat $e = no (λ ())
(` x) ≟-pat $v = no (λ ())
(` x) ≟-pat (` y) with x Data.Nat.≟ y
(` x) ≟-pat (` y) | yes refl = yes refl
(` x) ≟-pat (` y) | no ¬x≟y = no (λ { refl → ¬x≟y refl })
(` x) ≟-pat (ƛ x₁) = no (λ ())
(` x) ≟-pat (p₂ `· p₃) = no (λ ())
(` x) ≟-pat (# x₁) = no (λ ())
(` x) ≟-pat (p₂ `+ p₃) = no (λ ())
(ƛ x) ≟-pat $e = no (λ ())
(ƛ x) ≟-pat $v = no (λ ())
(ƛ x) ≟-pat (` x₁) = no (λ ())
(ƛ x) ≟-pat (ƛ y) with x ≟-exp y
...               | yes refl = yes refl
...               | no ¬x≟y  = no (λ { refl → ¬x≟y refl })
(ƛ x) ≟-pat (p₂ `· p₃) = no (λ ())
(ƛ x) ≟-pat (# x₁) = no (λ ())
(ƛ x) ≟-pat (p₂ `+ p₃) = no (λ ())
(p₁ `· p₃) ≟-pat $e = no (λ ())
(p₁ `· p₃) ≟-pat $v = no (λ ())
(p₁ `· p₃) ≟-pat (` x) = no (λ ())
(p₁ `· p₃) ≟-pat (ƛ x) = no (λ ())
(p₁ `· p₃) ≟-pat (p₂ `· p₄) with (p₁ ≟-pat p₂) with (p₃ ≟-pat p₄)
... | yes refl | yes refl = yes refl
... | yes refl | no ¬3≟4  = no λ { refl → ¬3≟4 refl }
... | no ¬1≟2  | yes _    = no (λ { refl → ¬1≟2 refl })
... | no ¬1≟2  | no _     = no (λ { refl → ¬1≟2 refl })
(p₁ `· p₃) ≟-pat (# x) = no (λ ())
(p₁ `· p₃) ≟-pat (p₂ `+ p₄) = no (λ ())
(# x) ≟-pat $e = no (λ ())
(# x) ≟-pat $v = no (λ ())
(# x) ≟-pat (` x₁) = no (λ ())
(# x) ≟-pat (ƛ x₁) = no (λ ())
(# x) ≟-pat (p₂ `· p₃) = no (λ ())
(# x) ≟-pat (# y) with (x Data.Nat.≟ y)
(# x) ≟-pat (# y) | yes refl = yes refl
(# x) ≟-pat (# y) | no ¬x≟y  = no λ { refl → ¬x≟y refl }
(# x) ≟-pat (p₂ `+ p₃) = no (λ ())
(p₁ `+ p₃) ≟-pat $e = no (λ ())
(p₁ `+ p₃) ≟-pat $v = no (λ ())
(p₁ `+ p₃) ≟-pat (` x) = no (λ ())
(p₁ `+ p₃) ≟-pat (ƛ x) = no (λ ())
(p₁ `+ p₃) ≟-pat (p₂ `· p₄) = no (λ ())
(p₁ `+ p₃) ≟-pat (# x) = no (λ ())
(p₁ `+ p₃) ≟-pat (p₂ `+ p₄) with (p₁ ≟-pat p₂) with (p₃ ≟-pat p₄)
... | yes refl | yes refl = yes refl
... | yes refl | no ¬3≟4  = no λ { refl → ¬3≟4 refl }
... | no ¬1≟2  | yes _    = no (λ { refl → ¬1≟2 refl })
... | no ¬1≟2  | no _     = no (λ { refl → ¬1≟2 refl })

data Exp where
  `_    : Id → Exp
  ƛ_    : Exp → Exp
  _`·_  : Exp → Exp → Exp
  #_    : ℕ → Exp
  _`+_  : Exp → Exp → Exp
  φ_⇒_ : Pat × Act × Gas → Exp → Exp
  δ_⇒_ : Act × Gas × ℕ   → Exp → Exp

(` x) ≟-exp (` y) with (x Data.Nat.≟ y)
... | yes refl = yes refl
... | no x≢y = no λ { refl → x≢y refl }
(` x) ≟-exp (ƛ e₂) = no (λ ())
(` x) ≟-exp (e₂ `· e₃) = no (λ ())
(` x) ≟-exp (# x₁) = no (λ ())
(` x) ≟-exp (e₂ `+ e₃) = no (λ ())
(` x) ≟-exp (φ x₁ ⇒ e₂) = no (λ ())
(` x) ≟-exp (δ x₁ ⇒ e₂) = no (λ ())
(ƛ e₁) ≟-exp (` x) = no (λ ())
(ƛ e₁) ≟-exp (ƛ e₂) with (e₁ ≟-exp e₂)
... | yes refl = yes refl
... | no e₁≢e₂ = no λ { refl → e₁≢e₂ refl }
(ƛ e₁) ≟-exp (e₂ `· e₃) = no (λ ())
(ƛ e₁) ≟-exp (# x) = no (λ ())
(ƛ e₁) ≟-exp (e₂ `+ e₃) = no (λ ())
(ƛ e₁) ≟-exp (φ x ⇒ e₂) = no (λ ())
(ƛ e₁) ≟-exp (δ x ⇒ e₂) = no (λ ())
(e₁ `· e₃) ≟-exp (` x) = no (λ ())
(e₁ `· e₃) ≟-exp (ƛ e₂) = no (λ ())
(e₁ `· e₃) ≟-exp (e₂ `· e₄) with (e₁ ≟-exp e₂) ×-dec (e₃ ≟-exp e₄)
... | yes (refl , refl) = yes refl
... | no e₁≢e₂ = no λ { refl → e₁≢e₂ (refl , refl) }
(e₁ `· e₃) ≟-exp (# x) = no (λ ())
(e₁ `· e₃) ≟-exp (e₂ `+ e₄) = no (λ ())
(e₁ `· e₃) ≟-exp (φ x ⇒ e₂) = no (λ ())
(e₁ `· e₃) ≟-exp (δ x ⇒ e₂) = no (λ ())
(# x) ≟-exp (` x₁) = no (λ ())
(# x) ≟-exp (ƛ e₂) = no (λ ())
(# x) ≟-exp (e₂ `· e₃) = no (λ ())
(# x) ≟-exp (# y) with (x Data.Nat.≟ y)
... | yes refl = yes refl
... | no x≢y = no λ { refl → x≢y refl }
(# x) ≟-exp (e₂ `+ e₃) = no (λ ())
(# x) ≟-exp (φ x₁ ⇒ e₂) = no (λ ())
(# x) ≟-exp (δ x₁ ⇒ e₂) = no (λ ())
(e₁ `+ e₃) ≟-exp (` x) = no (λ ())
(e₁ `+ e₃) ≟-exp (ƛ e₂) = no (λ ())
(e₁ `+ e₃) ≟-exp (e₂ `· e₄) = no (λ ())
(e₁ `+ e₃) ≟-exp (# x) = no (λ ())
(e₁ `+ e₃) ≟-exp (e₂ `+ e₄) with (e₁ ≟-exp e₂) ×-dec (e₃ ≟-exp e₄)
... | yes (refl , refl) = yes refl
... | no e₁≢e₂ = no λ { refl → e₁≢e₂ (refl , refl) }
(e₁ `+ e₃) ≟-exp (φ x ⇒ e₂) = no (λ ())
(e₁ `+ e₃) ≟-exp (δ x ⇒ e₂) = no (λ ())
(φ x ⇒ e₁) ≟-exp (` x₁) = no (λ ())
(φ x ⇒ e₁) ≟-exp (ƛ e₂) = no (λ ())
(φ x ⇒ e₁) ≟-exp (e₂ `· e₃) = no (λ ())
(φ x ⇒ e₁) ≟-exp (# x₁) = no (λ ())
(φ x ⇒ e₁) ≟-exp (e₂ `+ e₃) = no (λ ())
(φ (p₁ , a₁ , g₁) ⇒ e₁) ≟-exp (φ (p₂ , a₂ , g₂) ⇒ e₂)
    with (p₁ ≟-pat p₂) ×-dec (a₁ ≟-act a₂) ×-dec (g₁ ≟-gas g₂) ×-dec (e₁ ≟-exp e₂)
... | yes (refl , refl , refl , refl) = yes refl
... | no page₁≢page₂ = no (λ { refl → page₁≢page₂ (refl , refl , refl , refl) })
(φ x ⇒ e₁) ≟-exp (δ x₁ ⇒ e₂) = no (λ ())
(δ x ⇒ e₁) ≟-exp (` x₁) = no (λ ())
(δ x ⇒ e₁) ≟-exp (ƛ e₂) = no (λ ())
(δ x ⇒ e₁) ≟-exp (e₂ `· e₃) = no (λ ())
(δ x ⇒ e₁) ≟-exp (# x₁) = no (λ ())
(δ x ⇒ e₁) ≟-exp (e₂ `+ e₃) = no (λ ())
(δ x ⇒ e₁) ≟-exp (φ x₁ ⇒ e₂) = no (λ ())
(δ (a₁ , g₁ , l₁) ⇒ e₁) ≟-exp (δ (a₂ , g₂ , l₂) ⇒ e₂)
    with (a₁ ≟-act a₂) ×-dec (g₁ ≟-gas g₂) ×-dec (l₁ Data.Nat.≟ l₂) ×-dec (e₁ ≟-exp e₂)
... | yes (refl , refl , refl , refl) = yes refl
... | no agle₁≢agle₂ = no λ { refl → agle₁≢agle₂ (refl , refl , refl , refl) }

data Value : Exp → Set where
  V-# : ∀ {n : ℕ}
    → Value (# n)

  V-ƛ : ∀ {e}
    → Value (ƛ e)

value? : ∀ (e : Exp) → Dec (Value e)
value? (` x) = no λ ()
value? (ƛ e) = yes V-ƛ
value? (e `· e₁) = no (λ ())
value? (# x) = yes V-#
value? (e `+ e₁) = no (λ ())
value? (φ x ⇒ e) = no (λ ())
value? (δ x ⇒ e) = no (λ ())

data Normal : Exp → Set where
  N-` : ∀ {x} → Normal (` x)
  N-ƛ : ∀ {e} → Normal e → Normal (ƛ e)
  N-· : ∀ {e₁ e₂} → Normal e₁ → Normal e₂ → Normal (e₁ `· e₂)
  N-# : ∀ {n} → Normal (# n)
  N-+ : ∀ {e₁ e₂} → Normal e₁ → Normal e₂ → Normal (e₁ `+ e₂)

data Filter : Exp → Set where
  F-Φ : ∀ {pag e}
    → Filter (φ pag ⇒ e)

  F-Δ : ∀ {agl e}
    → Filter (δ agl ⇒ e)

filter? : ∀ (e : Exp) → Dec (Filter e)
filter? (` x) = no λ ()
filter? (ƛ e) = no λ ()
filter? (e `· e₁) = no λ ()
filter? (# x) = no λ ()
filter? (e `+ e₁) = no λ ()
filter? (φ x ⇒ e) = yes F-Φ
filter? (δ x ⇒ e) = yes F-Δ

data PatVal : Pat → Set where
  PV-# : ∀ {n}
    → PatVal (# n)

  PV-ƛ : ∀ {e}
    → PatVal (ƛ e)

strip : Exp → Exp
strip (` x) = ` x
strip (ƛ e) = ƛ (strip e)
strip (e₁ `· e₂) = (strip e₁) `· (strip e₂)
strip (# n) = # n
strip (L `+ M) = (strip L) `+ (strip M)
strip (φ x ⇒ L) = strip L
strip (δ x ⇒ L) = strip L

strip-normal : ∀ (e : Exp) → Normal (strip e)
strip-normal (` x) = N-`
strip-normal (ƛ e) = N-ƛ (strip-normal e)
strip-normal (e₁ `· e₂) = N-· (strip-normal e₁) (strip-normal e₂)
strip-normal (# x) = N-#
strip-normal (e₁ `+ e₂) = N-+ (strip-normal e₁) (strip-normal e₂)
strip-normal (φ x ⇒ e) = strip-normal e
strip-normal (δ x ⇒ e) = strip-normal e

patternize : Exp → Pat
patternize (` x) = ` x
patternize (ƛ L) = ƛ L
patternize (L `· M) = (patternize L) `· (patternize M)
patternize (# n) = # n
patternize (L `+ M) = (patternize L) `+ (patternize M)
patternize (φ x ⇒ L) = patternize L
patternize (δ x ⇒ L) = patternize L

↑-ℕ : ℕ → ℕ → ℕ
↑-ℕ zero zero = suc zero
↑-ℕ zero (suc c) = zero
↑-ℕ (suc x) zero = suc (suc x)
↑-ℕ (suc x) (suc c) = suc (↑-ℕ x c)

↑_from : Exp → ℕ → Exp
↑ₚ_from : Pat → ℕ → Pat

↑ ` x from d = ` ↑-ℕ x d
↑ ƛ e from d = ƛ (↑ e from (ℕ.suc d))
↑ eₗ `· eᵣ from d  = (↑ eₗ from d) `· (↑ eᵣ from d)
↑ # x from d  = # x
↑ eₗ `+ eᵣ from d  = (↑ eₗ from d) `+ (↑ eᵣ from d)
↑ φ (p , a , g) ⇒ e from d  = φ ((↑ₚ p from d) , a , g) ⇒ (↑ e from d)
↑ δ agl ⇒ e from d  = δ agl ⇒ (↑ e from d)

↑ₚ $e from d = $e
↑ₚ $v from d = $v
↑ₚ ` x from d = ` ↑-ℕ x d
↑ₚ ƛ e from d = ƛ ↑ e from (ℕ.suc d)
↑ₚ eₗ `· eᵣ from d  = (↑ₚ eₗ from d) `· (↑ₚ eᵣ from d)
↑ₚ # x from d  = # x
↑ₚ eₗ `+ eᵣ from d  = (↑ₚ eₗ from d) `+ (↑ₚ eᵣ from d)

↓-ℕ : ℕ → ℕ → ℕ
↓-ℕ zero c = zero
↓-ℕ (suc x) zero = x
↓-ℕ (suc x) (suc c) = suc (↓-ℕ x c)

↑ : Exp → Exp
↑ e = ↑ e from 0

↓_from : Exp → ℕ → Exp
↓ₚ_from : Pat → ℕ → Pat

↓ ` x from d = ` ↓-ℕ x d
↓ ƛ e from d = ƛ ↓ e from (ℕ.suc d)
↓ eₗ `· eᵣ from d  = (↓ eₗ from d) `· (↓ eᵣ from d)
↓ # x from d  = # x
↓ eₗ `+ eᵣ from d  = (↓ eₗ from d) `+ (↓ eᵣ from d)
↓ φ (p , ag) ⇒ e from d  = φ ((↓ₚ p from d), ag) ⇒ (↓ e from d)
↓ δ r ⇒ e from d  = δ r ⇒ (↓ e from d)

↓ₚ $e from d = $e
↓ₚ $v from d = $v
↓ₚ ` x from d = ` ↓-ℕ x d
↓ₚ ƛ e      from d = ƛ ↓ e from (ℕ.suc d)
↓ₚ eₗ `· eᵣ from d = (↓ₚ eₗ from d) `· (↓ₚ eᵣ from d)
↓ₚ # x      from d = # x
↓ₚ eₗ `+ eᵣ from d = (↓ₚ eₗ from d) `+ (↓ₚ eᵣ from d)

↓ : Exp → Exp
↓ e = ↓ e from 0

_[_:=_] : Exp → ℕ → Exp → Exp
_⟨_:=_⟩ : Pat → ℕ → Exp → Pat

$e ⟨ _ := _ ⟩ = $e
$v ⟨ _ := _ ⟩ = $v
(` x) ⟨ y := v ⟩ with (x Data.Nat.≟ y)
... | yes refl = patternize v
... | no x≢y = (` x)
(ƛ e) ⟨ y := v ⟩ = ƛ (e [ (ℕ.suc y) := (↑ v) ])
(p₁ `· p₂) ⟨ x := v ⟩ = (p₁ ⟨ x := v ⟩) `· (p₂ ⟨ x := v ⟩)
(# n) ⟨ _ := _ ⟩ = # n
(p₁ `+ p₂) ⟨ x := v ⟩ = (p₁ ⟨ x := v ⟩) `+ (p₂ ⟨ x := v ⟩)

(` x) [ y := v ] with (x Data.Nat.≟ y)
... | yes refl = v
... | no ¬x≡y  = (` x)
(ƛ e) [ x := v ] = ƛ (e [ (ℕ.suc x) := (↑ v) ])
(e₁ `· e₂) [ x := v ] = (e₁ [ x := v ]) `· (e₂ [ x := v ])
(# n) [ x := v ] = # n
(e₁ `+ e₂) [ x := v ] = (e₁ [ x := v ]) `+ (e₂ [ x := v ])
(φ (p , ag) ⇒ e) [ x := v ] = φ ((p ⟨ x := v ⟩), ag) ⇒ e [ x := v ]
(δ agl ⇒ e) [ x := v ] = δ agl ⇒ e [ x := v ]

infix 4 _matches_

data _matches_ : Pat → Exp → Set where
  M-E : ∀ {e}
    → $e matches e

  M-V : ∀ {v}
    → Value v
    → $v matches v

  M-· : ∀ {pₗ pᵣ eₗ eᵣ}
    → pₗ matches eₗ
    → pᵣ matches eᵣ
    → (pₗ `· pᵣ) matches (eₗ `· eᵣ)

  M-+ : ∀ {pₗ pᵣ eₗ eᵣ}
    → pₗ matches eₗ
    → pᵣ matches eᵣ
    → (pₗ `+ pᵣ) matches (eₗ `+ eᵣ)

  M-ƛ : ∀ {eₚ eₑ}
    → (strip eₚ) ≡ (strip eₑ)
    → (ƛ eₚ) matches (ƛ eₑ)

  M-# : ∀ {n}
    → (# n) matches (# n)

_matches?_ : (p : Pat) → (e : Exp) → Dec (p matches e)
$e matches? e = yes M-E
$v matches? e with (value? e)
$v matches? e | yes V = yes (M-V V)
$v matches? e | no ¬V = no λ { (M-V V) → ¬V V }
(` x) matches? e = no λ ()
(ƛ x) matches? (` x₁) = no λ ()
(ƛ x) matches? (ƛ e) with ((strip x) ≟-exp (strip e))
... | yes pₛ≡eₛ = yes (M-ƛ pₛ≡eₛ)
... | no ¬pₛ≡eₛ = no λ { (M-ƛ pₛ≡eₛ) → ¬pₛ≡eₛ pₛ≡eₛ }
(ƛ x) matches? (e `· e₁) = no (λ ())
(ƛ x) matches? (# x₁) = no λ ()
(ƛ x) matches? (e `+ e₁) = no λ ()
(ƛ x) matches? (φ x₁ ⇒ e) = no λ ()
(ƛ x) matches? (δ x₁ ⇒ e) = no λ ()
(p₁ `· p₂) matches? (` x) = no λ ()
(p₁ `· p₂) matches? (ƛ e) = no λ ()
(p₁ `· p₂) matches? (e₁ `· e₂) with (p₁ matches? e₁) ×-dec (p₂ matches? e₂)
... | yes (matches₁ , matches₂) = yes (M-· matches₁ matches₂)
... | no ¬matches = no λ { (M-· matches₁ matches₂) → ¬matches (matches₁ , matches₂) }
(p₁ `· p₂) matches? (# x) = no λ ()
(p₁ `· p₂) matches? (e `+ e₁) = no λ ()
(p₁ `· p₂) matches? (φ x ⇒ e) = no λ ()
(p₁ `· p₂) matches? (δ x ⇒ e) = no λ ()
(# x) matches? (` x₁) = no λ ()
(# x) matches? (ƛ e) = no λ ()
(# x) matches? (e `· e₁) = no λ ()
(# x) matches? (# y) with (x Data.Nat.≟ y)
... | yes refl = yes M-#
... | no x≢y = no λ { M-# → x≢y refl }
(# x) matches? (e `+ e₁) = no λ ()
(# x) matches? (φ x₁ ⇒ e) = no λ ()
(# x) matches? (δ x₁ ⇒ e) = no λ ()
(p₁ `+ p₂) matches? (` x) = no λ ()
(p₁ `+ p₂) matches? (ƛ e) = no λ ()
(p₁ `+ p₂) matches? (e `· e₁) = no λ ()
(p₁ `+ p₂) matches? (# x) = no λ ()
(p₁ `+ p₂) matches? (e₁ `+ e₂) with (p₁ matches? e₁) ×-dec (p₂ matches? e₂)
... | yes (matches₁ , matches₂) = yes (M-+ matches₁ matches₂)
... | no ¬matches = no λ { (M-+ matches₁ matches₂) → ¬matches (matches₁ , matches₂) }
(p₁ `+ p₂) matches? (φ x ⇒ e) = no λ ()
(p₁ `+ p₂) matches? (δ x ⇒ e) = no λ ()

infix 0 _—→_

data _—→_ : Exp → Exp → Set where
  T-β-· : ∀ {vᵣ eₓ}
    → Value vᵣ
    → (ƛ eₓ) `· vᵣ —→ ↓ (eₓ [ 0 := (↑ vᵣ) ]) from 0

  T-β-+ : ∀ {nₗ nᵣ}
    → (# nₗ) `+ (# nᵣ) —→ (# (nₗ Data.Nat.+ nᵣ))

  T-β-φ : ∀ {pag v}
    → Value v
    → (φ pag ⇒ v) —→ v

  T-β-δ : ∀ {agl v}
    → Value v
    → (φ agl ⇒ v) —→ v

data Ctx : Set where
  ∘     : Ctx
  _·ₗ_  : Ctx → Exp → Ctx
  _·ᵣ_  : Exp → Ctx → Ctx
  _+ₗ_  : Ctx → Exp → Ctx
  _+ᵣ_  : Exp → Ctx → Ctx
  φ_⇒_ : Pat × Act × Gas → Ctx → Ctx
  δ_⇒_ : Act × Gas × ℕ → Ctx → Ctx

data _⇒_⟨_⟩ : Exp → Ctx → Exp → Set where
  D-β-` : ∀ {x}
    → (` x) ⇒ ∘ ⟨ (` x) ⟩

  D-ξ-·-l : ∀ {eₗ eᵣ ℰ eₗ′}
    → eₗ ⇒ ℰ ⟨ eₗ′ ⟩
    → (eₗ `· eᵣ) ⇒ (ℰ ·ₗ eᵣ) ⟨ eₗ′ ⟩

  D-ξ-·-r : ∀ {vₗ eᵣ ℰ eᵣ′}
    → Value vₗ
    → eᵣ ⇒ ℰ ⟨ eᵣ′ ⟩
    → (vₗ `· eᵣ) ⇒ (vₗ ·ᵣ ℰ) ⟨ eᵣ′ ⟩

  D-β-· : ∀ {vₗ vᵣ}
    → Value vₗ
    → Value vᵣ
    → (vₗ `· vᵣ) ⇒ ∘ ⟨ vₗ `· vᵣ ⟩

  D-ξ-+-l : ∀ {eₗ eᵣ ℰ eₗ′}
    → eₗ ⇒ ℰ ⟨ eₗ′ ⟩
    → (eₗ `+ eᵣ) ⇒ (ℰ +ₗ eᵣ) ⟨ eₗ′ ⟩

  D-ξ-+-r : ∀ {vₗ eᵣ ℰ eᵣ′}
    → Value vₗ
    → eᵣ ⇒ ℰ ⟨ eᵣ′ ⟩
    → (vₗ `+ eᵣ) ⇒ (vₗ +ᵣ ℰ) ⟨ eᵣ′ ⟩

  D-β-+ : ∀ {vₗ vᵣ}
    → Value vₗ
    → Value vᵣ
    → (vₗ `+ vᵣ) ⇒ ∘ ⟨ vₗ `+ vᵣ ⟩

  D-ξ-φ : ∀ {pag e ℰ e′}
    → e ⇒ ℰ ⟨ e′ ⟩
    → (φ pag ⇒ e) ⇒ (φ pag ⇒ ℰ) ⟨ e′ ⟩

  D-β-φ : ∀ {pag v}
    → Value v
    → (φ pag ⇒ v) ⇒ ∘ ⟨ φ pag ⇒ v ⟩

  D-ξ-δ : ∀ {agl e ℰ e′}
    → e ⇒ ℰ ⟨ e′ ⟩
    → (δ agl ⇒ e) ⇒ (δ agl ⇒ ℰ) ⟨ e′ ⟩

  D-β-δ : ∀ {agl v}
    → Value v
    → (δ agl ⇒ v) ⇒ ∘ ⟨ δ agl ⇒ v ⟩

V¬⇒ : ∀ {v ε e}
  → Value v
  → ¬ (v ⇒ ε ⟨ e ⟩)
V¬⇒ V-# ()
V¬⇒ V-ƛ ()

⇒¬V : ∀ {e ε e₀}
  → e ⇒ ε ⟨ e₀ ⟩
  → ¬ (Value e)
⇒¬V D-β-` ()
⇒¬V (D-ξ-·-l _) ()
⇒¬V (D-ξ-·-r _ _) ()
⇒¬V (D-β-· _ _) ()
⇒¬V (D-ξ-+-l _) ()
⇒¬V (D-ξ-+-r _ _) ()
⇒¬V (D-β-+ _ _) ()
⇒¬V (D-ξ-φ _) ()
⇒¬V (D-β-φ _) ()
⇒¬V (D-ξ-δ _) ()
⇒¬V (D-β-δ _) ()

data _⇐_⟨_⟩ : Exp → Ctx → Exp → Set where
  C-∘ : ∀ {e}
    → e ⇐ ∘ ⟨ e ⟩

  C-·ₗ : ∀ {εₗ eᵣ eₗ e}
    → eₗ ⇐ εₗ ⟨ e ⟩
    → (eₗ `· eᵣ) ⇐ (εₗ ·ₗ eᵣ) ⟨ e ⟩

  C-·ᵣ : ∀ {eₗ εᵣ eᵣ e}
    → eᵣ ⇐ εᵣ ⟨ e ⟩
    → (eₗ `· eᵣ) ⇐ (eₗ ·ᵣ εᵣ) ⟨ e ⟩

  C-+ₗ : ∀ {εₗ eᵣ eₗ e}
    → eₗ ⇐ εₗ ⟨ e ⟩
    → (eₗ `+ eᵣ) ⇐ (εₗ +ₗ eᵣ) ⟨ e ⟩

  C-+ᵣ : ∀ {eₗ εᵣ eᵣ e}
    → eᵣ ⇐ εᵣ ⟨ e ⟩
    → (eₗ `+ eᵣ) ⇐ (eₗ +ᵣ εᵣ) ⟨ e ⟩

  C-φ : ∀ {pag ε e e′}
    → e′ ⇐ ε ⟨ e ⟩
    → (φ pag ⇒ e′) ⇐ (φ pag ⇒ ε) ⟨ e ⟩

  C-δ : ∀ {agl ε e e′}
    → e′ ⇐ ε ⟨ e ⟩
    → (δ agl ⇒ e′) ⇐ (δ agl ⇒ ε) ⟨ e ⟩

data _⊢_⇝_ : Pat × Act × Gas × ℕ → Exp → Exp → Set where
  I-V : ∀ {pagl v}
    → Value v
    → pagl ⊢ v ⇝ v

  I-`-⊤ : ∀ {p a g l x}
    → p matches (` x)
    → (p , a , g , l) ⊢ (` x) ⇝ (δ (a , g , l) ⇒ (` x))

  I-`-⊥ : ∀ {p a g l x}
    → ¬ (p matches (` x))
    → (p , a , g , l) ⊢ (` x) ⇝ (` x)

  I-·-⊤ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → p matches (eₗ `· eᵣ)
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ `· eᵣ) ⇝ (δ (a , g , l) ⇒ (eₗ′ `· eᵣ′))

  I-·-⊥ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → ¬ (p matches (eₗ `· eᵣ))
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ `· eᵣ) ⇝ (eₗ′ `· eᵣ′)

  I-+-⊤ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → p matches (eₗ `+ eᵣ)
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ `+ eᵣ) ⇝ (δ (a , g , l) ⇒ (eₗ′ `+ eᵣ′))

  I-+-⊥ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → ¬ (p matches (eₗ `+ eᵣ))
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ `+ eᵣ) ⇝ (eₗ′ `+ eᵣ′)

  I-Φ : ∀ {pat act gas lvl p a g e e′ e″}
    → (pat , act , gas , lvl) ⊢ e ⇝ e′
    → (p , a , g , ℕ.suc lvl) ⊢ e′ ⇝ e″
    → (pat , act , gas , lvl) ⊢ (φ (p , a , g) ⇒ e) ⇝ (φ (p , a , g) ⇒ e″)

  I-Δ : ∀ {pat act gas lvl a g l e e′}
    → (pat , act , gas , lvl) ⊢ e ⇝ e′
    → (pat , act , gas , lvl) ⊢ (δ (a , g , l) ⇒ e) ⇝ (δ (a , g , l) ⇒ e′)

strip-instr : ∀ {p : Pat} {a : Act} {g : Gas} {l : ℕ} {e e′ : Exp}
  → (p , a , g , l) ⊢ e ⇝ e′
  → strip e′ ≡ strip e
strip-instr (I-V _) = refl
strip-instr (I-`-⊤ _) = refl
strip-instr (I-`-⊥ _) = refl
strip-instr (I-·-⊤ _ Iₗ Iᵣ) = Eq.cong₂ _`·_ (strip-instr Iₗ) (strip-instr Iᵣ)
strip-instr (I-·-⊥ _ Iₗ Iᵣ) = Eq.cong₂ _`·_ (strip-instr Iₗ) (strip-instr Iᵣ)
strip-instr (I-+-⊤ _ Iₗ Iᵣ) = Eq.cong₂ _`+_ (strip-instr Iₗ) (strip-instr Iᵣ)
strip-instr (I-+-⊥ _ Iₗ Iᵣ) = Eq.cong₂ _`+_ (strip-instr Iₗ) (strip-instr Iᵣ)
strip-instr (I-Φ I₀ I₁) = Eq.trans (strip-instr I₁) (strip-instr I₀)
strip-instr (I-Δ I) = (strip-instr I)

decay : Ctx → Ctx
decay ∘ = ∘
decay (ε ·ₗ e) = (decay ε) ·ₗ e
decay (e ·ᵣ ε) = e ·ᵣ (decay ε)
decay (ε +ₗ e) = (decay ε) +ₗ e
decay (e +ᵣ ε) = e +ᵣ (decay ε)
decay (φ f ⇒ ε) = decay ε
decay (δ r ⇒ ε) = decay ε

select : Act → ℕ → Ctx → Act
select act lvl ∘ = act
select act lvl (c ·ₗ e) = select act lvl c
select act lvl (e ·ᵣ c) = select act lvl c
select act lvl (c +ₗ e) = select act lvl c
select act lvl (e +ᵣ c) = select act lvl c
select act lvl (φ f ⇒ c) = select act lvl c
select act lvl (δ (a , g , l) ⇒ c) with l ≤? lvl
... | yes _ = select act lvl c
... | no  _ = select a l c

data _⊢_⊣_ : Act × ℕ → Ctx → Act → Set where
  A-∘ : ∀ {act lvl}
    → (act , lvl) ⊢ ∘ ⊣ act

  A-·ₗ : ∀ {act lvl εₗ eᵣ act′}
    → (act , lvl) ⊢ εₗ ⊣ act′
    → (act , lvl) ⊢ (εₗ ·ₗ eᵣ) ⊣ act′

  A-·-r : ∀ {act lvl eₗ εᵣ act′}
    → (act , lvl) ⊢ εᵣ ⊣ act′
    → (act , lvl) ⊢ (eₗ ·ᵣ εᵣ) ⊣ act′

  A-+-l : ∀ {act lvl εₗ eᵣ act′}
    → (act , lvl) ⊢ εₗ ⊣ act′
    → (act , lvl) ⊢ (εₗ +ₗ eᵣ) ⊣ act′

  A-+-r : ∀ {act lvl eₗ εᵣ act′}
    → (act , lvl) ⊢ εᵣ ⊣ act′
    → (act , lvl) ⊢ (eₗ +ᵣ εᵣ) ⊣ act′

  A-Φ : ∀ {act lvl ε act′ pag}
    → (act , lvl) ⊢ ε ⊣ act′
    → (act , lvl) ⊢ φ pag ⇒ ε ⊣ act′

  A-Δ-> : ∀ {act lvl ε act′ a g l}
    → l > lvl
    → (a , l) ⊢ ε ⊣ act′
    → (act , lvl) ⊢ δ (a , g , l) ⇒ ε ⊣ act′

  A-Δ-≤ : ∀ {act lvl ε act′ a g l}
    → l ≤ lvl
    → (act , lvl) ⊢ ε ⊣ act′
    → (act , lvl) ⊢ δ (a , g , l) ⇒ ε ⊣ act′

⊢⊣-select : ∀ {a l ε}
  → (a , l) ⊢ ε ⊣ (select a l ε)
⊢⊣-select {ε = ∘} = A-∘
⊢⊣-select {ε = ε ·ₗ e} = A-·ₗ ⊢⊣-select
⊢⊣-select {ε = e ·ᵣ ε} = A-·-r ⊢⊣-select
⊢⊣-select {ε = ε +ₗ e} = A-+-l ⊢⊣-select
⊢⊣-select {ε = e +ᵣ ε} = A-+-r ⊢⊣-select
⊢⊣-select {ε = φ f ⇒ ε} = A-Φ ⊢⊣-select
⊢⊣-select {a = act} {l = lvl} {ε = δ (a , _ , l) ⇒ ε} with (l ≤? lvl)
... | yes ≤ = (A-Δ-≤ ≤) ⊢⊣-select
... | no  ≰ = A-Δ-> (Data.Nat.Properties.≰⇒> ≰) ⊢⊣-select

data _⊢_↠_ : Pat × Act × Gas × ℕ → Exp → Exp → Set where
  skip : ∀ {p a g l e e′ eᵢ e₀ e₀′ ε ε₀}
    → (p , a , g , l) ⊢ e ⇝ eᵢ
    → eᵢ ⇒ ε₀ ⟨ e₀ ⟩
    → Filter e₀ ⊎ (a , l) ⊢ ε ⊣ eval
    → e₀ —→ e₀′
    → e′ ⇐ (decay ε) ⟨ e₀′ ⟩
    → (p , a , g , l) ⊢ e ↠ e′

data _⊢_⇥_⟨_⟩ : Pat × Act × Gas × ℕ → Exp → Ctx → Exp → Set where
  skip : ∀ {p a g l e e′ ε e₀}
    → (p , a , g , l) ⊢ e ↠ e′
    → (p , a , g , l) ⊢ e′ ⇥ ε ⟨ e₀ ⟩
    → (p , a , g , l) ⊢ e ⇥ ε ⟨ e₀ ⟩

  step : ∀ {p a g l e eᵢ e₀ ε ε₀}
    → (p , a , g , l) ⊢ e ⇝ eᵢ
    → eᵢ ⇒ ε₀ ⟨ e₀ ⟩
    → (a , l) ⊢ ε ⊣ pause
    → (p , a , g , l) ⊢ e ⇥ (decay ε) ⟨ e₀ ⟩

data _⊢_⇥_value : Pat × Act × Gas × ℕ → Exp → Exp → Set where
  skip : ∀ {p a g l e e′ v}
    → (p , a , g , l) ⊢ e ↠ e′
    → (p , a , g , l) ⊢ e′ ⇥ v value
    → (p , a , g , l) ⊢ e ⇥ v value

  done : ∀ {p a g l v}
    → Value v
    → (p , a , g , l) ⊢ v ⇥ v value

data _⊢_⇥_ : Pat × Act × Gas × ℕ → Exp → Exp → Set where
  step : ∀ {p a g l e e′ eᵢ e₀ e₀′ ε ε₀}
    → (p , a , g , l) ⊢ e ⇝ eᵢ
    → eᵢ ⇒ ε₀ ⟨ e₀ ⟩
    → (a , l) ⊢ ε ⊣ pause
    → e₀ —→ e₀′
    → e′ ⇐ (decay ε) ⟨ e₀′ ⟩
    → (p , a , g , l) ⊢ e ⇥ e′

  skip : ∀ {p a g l e e′ e″ eᵢ e₀ e₀′ ε ε₀}
    → (p , a , g , l) ⊢ e ⇝ eᵢ
    → eᵢ ⇒ ε₀ ⟨ e₀ ⟩
    → Filter e₀ ⊎ (a , l) ⊢ ε ⊣ eval
    → e₀ —→ e₀′
    → e′ ⇐ (decay ε) ⟨ e₀′ ⟩
    → (p , a , g , l) ⊢ e′ ⇥ e″
    → (p , a , g , l) ⊢ e ⇥ e″

  done : ∀ {p a g l v}
    → Value v
    → (p , a , g , l) ⊢ v ⇥ v

infixr 7 _⇒_

data Typ : Set where
  _⇒_ : Typ → Typ → Typ
  `ℕ   : Typ

infixl 5 _⸴_

data TypCtx : Set where
  ∅   : TypCtx
  _⸴_ : TypCtx → Typ → TypCtx

length : TypCtx → ℕ
length ∅ = 0
length (Γ ⸴ x) = ℕ.suc (length Γ)

lookup : ∀ {Γ : TypCtx} → {n : ℕ} → (p : n < length Γ) → Typ
lookup {_ ⸴ A} {ℕ.zero} (s≤s z≤n) = A
lookup {Γ ⸴ A} {ℕ.suc n} (s≤s p) = lookup p

insert : ∀ {Γ : TypCtx} → {n : ℕ} → (p : n ≤ length Γ) → Typ → TypCtx
insert {Γ} {n = ℕ.zero} p τ = Γ ⸴ τ
insert {Γ ⸴ τ₀} {n = ℕ.suc n} (s≤s p) τ₁ = (insert p τ₁) ⸴ τ₀

remove : ∀ {Γ : TypCtx} → {n : ℕ} → (p : n < length Γ) → TypCtx
remove {Γ ⸴ τ₀} {n = ℕ.zero} p = Γ
remove {Γ ⸴ τ₀} {n = ℕ.suc n} (s≤s p) = (remove p) ⸴ τ₀

update : ∀ {Γ : TypCtx} → {n : ℕ} → (p : n < length Γ) → Typ → TypCtx
update {Γ ⸴ τ₀} {n = ℕ.zero} p τ = Γ ⸴ τ
update {Γ ⸴ τ₀} {n = ℕ.suc n} (s≤s p) τ₁ = (update p τ₁) ⸴ τ₀

infix 4 _∋_∶_

data _∋_∶_ : TypCtx → Id → Typ → Set where
  ∋-Z : ∀ {Γ τ}
    → Γ ⸴ τ ∋ 0 ∶ τ

  ∋-S : ∀ {Γ x τ₁ τ₂}
    → Γ ∋ x ∶ τ₁
    → Γ ⸴ τ₂ ∋ (ℕ.suc x) ∶ τ₁

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ n ∶ lookup p
count {_ ⸴ _} {ℕ.zero} (s≤s z≤n) = ∋-Z
count {Γ ⸴ _} {ℕ.suc n} (s≤s p) = ∋-S (count p)

infix 4 _⊢_∶_
infix 4 _⊢_∻_

data _⊢_∶_ : TypCtx → Exp → Typ → Set
data _⊢_∻_ : TypCtx → Pat → Typ → Set

data _⊢_∶_ where
  ⊢-` : ∀ {Γ x τ}
    → Γ ∋ x ∶ τ
    → Γ ⊢ ` x ∶ τ

  ⊢-ƛ : ∀ {Γ e τₓ τₑ}
    → Γ ⸴ τₓ ⊢ e ∶ τₑ
    → Γ ⊢ ƛ e ∶ (τₓ ⇒ τₑ)

  ⊢-· : ∀ {Γ e₁ e₂ τ₁ τ₂}
    → Γ ⊢ e₁ ∶ (τ₂ ⇒ τ₁)
    → Γ ⊢ e₂ ∶ τ₂
    → Γ ⊢ (e₁ `· e₂) ∶ τ₁

  ⊢-+ : ∀ {Γ e₁ e₂}
    → Γ ⊢ e₁ ∶ `ℕ
    → Γ ⊢ e₂ ∶ `ℕ
    → Γ ⊢ (e₁ `+ e₂) ∶ `ℕ

  ⊢-# : ∀ {Γ n}
    → Γ ⊢ (# n) ∶ `ℕ

  ⊢-φ : ∀ {Γ p τₚ ag e τₑ}
    → Γ ⊢ p ∻ τₚ
    → Γ ⊢ e ∶ τₑ
    → Γ ⊢ φ (p , ag) ⇒ e ∶ τₑ

  ⊢-δ : ∀ {Γ agl e τ}
    → Γ ⊢ e ∶ τ
    → Γ ⊢ δ agl ⇒ e ∶ τ

data _⊢_∻_ where
  ⊢-E : ∀ {Γ τ}
    → Γ ⊢ $e ∻ τ

  ⊢-V : ∀ {Γ τ}
    → Γ ⊢ $v ∻ τ

  ⊢-` : ∀ {Γ x τ}
    → Γ ∋ x ∶ τ
    → Γ ⊢ ` x ∻ τ

  ⊢-ƛ : ∀ {Γ e τₓ τₑ}
    → Γ ⸴ τₓ ⊢ e ∶ τₑ
    → Γ ⊢ ƛ e ∻ (τₓ ⇒ τₑ)

  ⊢-· : ∀ {Γ e₁ e₂ τ₁ τ₂}
    → Γ ⊢ e₁ ∻ τ₂ ⇒ τ₁
    → Γ ⊢ e₂ ∻ τ₂
    → Γ ⊢ (e₁ `· e₂) ∻ τ₁

  ⊢-# : ∀ {Γ n}
    → Γ ⊢ (# n) ∻ `ℕ

  ⊢-+ : ∀ {Γ e₁ e₂}
    → Γ ⊢ e₁ ∻ `ℕ
    → Γ ⊢ e₂ ∻ `ℕ
    → Γ ⊢ (e₁ `+ e₂) ∻ `ℕ

ext : ∀ {Γ Δ}
  → (∀ {x A}   →     Γ ∋ x ∶ A →     Δ ∋ x ∶ A)
  → (∀ {x A B} → Γ ⸴ B ∋ x ∶ A → Δ ⸴ B ∋ x ∶ A)
ext ρ ∋-Z       =  ∋-Z
ext ρ (∋-S ∋x)  =  ∋-S (ρ ∋x)

rename-exp : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ∶ A → Δ ∋ x ∶ A)
  → (∀ {e A} → Γ ⊢ e ∶ A → Δ ⊢ e ∶ A)
rename-pat : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ∶ A → Δ ∋ x ∶ A)
  → (∀ {e A} → Γ ⊢ e ∻ A → Δ ⊢ e ∻ A)

rename-exp ρ (⊢-` ∋-x)   = ⊢-` (ρ ∋-x)
rename-exp ρ (⊢-ƛ ⊢-N)   = ⊢-ƛ (rename-exp (ext ρ) ⊢-N)
rename-exp ρ (⊢-· e₁ e₂) = ⊢-· (rename-exp ρ e₁) (rename-exp ρ e₂)
rename-exp ρ (⊢-+ e₁ e₂) = ⊢-+ (rename-exp ρ e₁) (rename-exp ρ e₂)
rename-exp ρ ⊢-#         = ⊢-#
rename-exp ρ (⊢-φ p e)   = ⊢-φ (rename-pat ρ p) (rename-exp ρ e)
rename-exp ρ (⊢-δ Γ-⊢)   = ⊢-δ (rename-exp ρ Γ-⊢)

rename-pat ρ ⊢-E         = ⊢-E
rename-pat ρ ⊢-V         = ⊢-V
rename-pat ρ (⊢-` ∋-x)   = ⊢-` (ρ ∋-x)
rename-pat ρ (⊢-ƛ x⊢e)   = ⊢-ƛ (rename-exp (ext ρ) x⊢e)
rename-pat ρ (⊢-· e₁ e₂) = ⊢-· (rename-pat ρ e₁) (rename-pat ρ e₂)
rename-pat ρ ⊢-#         = ⊢-#
rename-pat ρ (⊢-+ e₁ e₂) = ⊢-+ (rename-pat ρ e₁) (rename-pat ρ e₂)

weaken : ∀ {Γ e A}
  → ∅ ⊢ e ∶ A
  → Γ ⊢ e ∶ A
weaken {Γ} ⊢e = rename-exp ρ ⊢e
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ∶ C
    → Γ ∋ z ∶ C
  ρ ()

∋-functional : ∀ {Γ x τ₁ τ₂} → (Γ ∋ x ∶ τ₁) → (Γ ∋ x ∶ τ₂) → τ₁ ≡ τ₂
∋-functional ∋-Z ∋-Z = refl
∋-functional (∋-S ∋₁) (∋-S ∋₂) = ∋-functional ∋₁ ∋₂

insert-≤ : ∀ {Γ x y τ₁ τ₂}
  → (p : x ≤ length Γ)
  → x ≤ y
  → Γ ∋ y ∶ τ₂
  → (insert p τ₁) ∋ (ℕ.suc y) ∶ τ₂
insert-≤ {Γ ⸴ τ′} {ℕ.zero} {ℕ.zero} p x≤y ∋₂ = ∋-S ∋₂
insert-≤ {Γ ⸴ τ′} {ℕ.zero} {ℕ.suc y} p x≤y ∋₂ = ∋-S ∋₂
insert-≤ {Γ ⸴ τ′} {ℕ.suc x} {ℕ.suc y} (s≤s p) (s≤s x≤y) (∋-S ∋₂) = ∋-S (insert-≤ p x≤y ∋₂)

insert-> : ∀ {Γ x y τ₁ τ₂}
  → (p : x ≤ length Γ)
  → x > y
  → Γ ∋ y ∶ τ₂
  → (insert p τ₁) ∋ y ∶ τ₂
insert-> {Γ ⸴ τ′} {ℕ.suc x} {ℕ.zero} (s≤s p) (s≤s x>y) ∋-Z = ∋-Z
insert-> {Γ ⸴ τ′} {ℕ.suc x} {ℕ.suc y} (s≤s p) (s≤s x>y) (∋-S ∋₂) = ∋-S (insert-> p x>y ∋₂)

↑-preserve : ∀ {Γ e τₑ x}
  → Γ ⊢ e ∶ τₑ
  → (p : x ≤ length Γ)
  → (∀ {τₓ} → (insert p τₓ) ⊢ (↑ e from x) ∶ τₑ)
↑ₚ-preserve : ∀ {Γ p τₑ x}
  → Γ ⊢ p ∻ τₑ
  → (x∈Γ : x ≤ length Γ)
  → (∀ {τₓ} → (insert x∈Γ τₓ) ⊢ (↑ₚ p from x) ∻ τₑ)

↑-preserve {e = ` x} {x = y} (⊢-` ∋) ∈ with x <? y
↑-preserve {e = ` x} {x = y} (⊢-` ∋) ∈ | yes x<y = {!!}
↑-preserve {e = ` x} {x = y} (⊢-` ∋) ∈ | no  x≮y = ⊢-` {!!}
↑-preserve {e = ƛ e} (⊢-ƛ ⊢) ∈ = ⊢-ƛ (↑-preserve ⊢ (s≤s ∈))
↑-preserve {e = e₁ `· e₂} (⊢-· ⊢₁ ⊢₂) ∈ = ⊢-· (↑-preserve ⊢₁ ∈) (↑-preserve ⊢₂ ∈)
↑-preserve {e = # x} ⊢-# ∈ = ⊢-#
↑-preserve {e = e₁ `+ e₂} (⊢-+ ⊢₁ ⊢₂) ∈ = ⊢-+ (↑-preserve ⊢₁ ∈) (↑-preserve ⊢₂ ∈)
↑-preserve {e = φ f ⇒ e} (⊢-φ ⊢ₚ ⊢ₑ) ∈ = ⊢-φ (↑ₚ-preserve ⊢ₚ ∈) (↑-preserve ⊢ₑ ∈)
↑-preserve {e = δ r ⇒ e} (⊢-δ ⊢) ∈ = ⊢-δ (↑-preserve ⊢ ∈)

↑ₚ-preserve ⊢-E ∈ = ⊢-E
↑ₚ-preserve ⊢-V ∈ = ⊢-V
↑ₚ-preserve {p = ` x} {x = y} (⊢-` ∋) ∈ with x <? y
↑ₚ-preserve {p = ` x} {x = y} (⊢-` ∋) ∈ | yes x<y = ⊢-` (insert-> ∈ {!!} {!!})
↑ₚ-preserve {p = ` x} {x = y} (⊢-` ∋) ∈ | no  x≮y = ⊢-` {!!}
↑ₚ-preserve {p = ƛ e} (⊢-ƛ ⊢) ∈ = ⊢-ƛ (↑-preserve ⊢ (s≤s ∈))
↑ₚ-preserve {p = e₁ `· e₂} (⊢-· ⊢₁ ⊢₂) ∈ = ⊢-· (↑ₚ-preserve ⊢₁ ∈) (↑ₚ-preserve ⊢₂ ∈)
↑ₚ-preserve {p = # x} ⊢-# p = ⊢-#
↑ₚ-preserve {p = e₁ `+ e₂} (⊢-+ ⊢₁ ⊢₂) ∈ = ⊢-+ (↑ₚ-preserve ⊢₁ ∈) (↑ₚ-preserve ⊢₂ ∈)

remove-≤ : ∀ {Γ x y τ}
  → (∈ : x < length Γ)
  → x ≤ y
  → Γ ∋ (ℕ.suc y) ∶ τ
  → (remove ∈) ∋ y ∶ τ
remove-≤ {Γ ⸴ τ′} {ℕ.zero} {ℕ.zero} p x<y (∋-S ∋) = ∋
remove-≤ {Γ ⸴ τ′} {ℕ.zero} {ℕ.suc y} p x<y (∋-S ∋) = ∋
remove-≤ {Γ ⸴ τ′} {ℕ.suc x} {ℕ.suc y} (s≤s p) (s≤s x≤y) (∋-S ∋₂) = ∋-S (remove-≤ p x≤y ∋₂)

remove-> : ∀ {Γ x y τ₂}
  → (∈ : x < length Γ)
  → x > y
  → Γ ∋ y ∶ τ₂
  → (remove ∈) ∋ y ∶ τ₂
remove-> {Γ ⸴ τ′} {ℕ.suc x} {ℕ.zero} (s≤s p) (s≤s x>y) ∋-Z = ∋-Z
remove-> {Γ ⸴ τ′} {ℕ.suc x} {ℕ.suc y} (s≤s p) (s≤s x>y) (∋-S ∋₂) = ∋-S (remove-> p x>y ∋₂)

↓-preserve : ∀ {Γ e τₑ x}
  → Γ ⊢ e ∶ τₑ
  → (∈ : x < length Γ)
  → (remove ∈) ⊢ (↓ e from x) ∶ τₑ
↓ₚ-preserve : ∀ {Γ p τₑ x}
  → Γ ⊢ p ∻ τₑ
  → (∈ : x < length Γ)
  → (remove ∈) ⊢ (↓ₚ p from x) ∻ τₑ

↓-preserve {e = ` x} {x = y} (⊢-` ∋) ∈ with x <? y
↓-preserve {e = ` x} {x = y} (⊢-` ∋) ∈ | yes x<y = {!!}
↓-preserve {e = ` x} {x = y} (⊢-` ∋) ∈ | no  x≮y = {!!}
↓-preserve {e = ƛ e} (⊢-ƛ ⊢) ∈ = ⊢-ƛ {!!}
↓-preserve (⊢-· ⊢₁ ⊢₂) ∈ = ⊢-· (↓-preserve ⊢₁ ∈) (↓-preserve ⊢₂ ∈)
↓-preserve {e = # x} ⊢-# ∈ = ⊢-#
↓-preserve {e = e₁ `+ e₂} (⊢-+ ⊢₁ ⊢₂) ∈ = ⊢-+ (↓-preserve ⊢₁ ∈) (↓-preserve ⊢₂ ∈)
↓-preserve {e = φ f ⇒ e} (⊢-φ ⊢ₚ ⊢ₑ) ∈ = ⊢-φ (↓ₚ-preserve ⊢ₚ ∈) (↓-preserve ⊢ₑ ∈)
↓-preserve {e = δ r ⇒ e} (⊢-δ ⊢) ∈ = ⊢-δ (↓-preserve ⊢ ∈)

↓ₚ-preserve ⊢-E ∈ = ⊢-E
↓ₚ-preserve ⊢-V ∈ = ⊢-V
↓ₚ-preserve {p = ` ℕ.zero} {x = ℕ.zero} (⊢-` ∋) ∈ = ⊢-` (remove-≤ ∈ {!!} {!!})
↓ₚ-preserve {p = ` ℕ.zero} {x = ℕ.suc y} (⊢-` ∋) ∈ = ⊢-` (remove-≤ ∈ {!!} {!!})
↓ₚ-preserve {p = ` ℕ.suc x} {x = y} (⊢-` ∋) ∈ = {!!}
↓ₚ-preserve {p = ƛ e} (⊢-ƛ ⊢) ∈ = ⊢-ƛ (↓-preserve ⊢ (s≤s ∈))
↓ₚ-preserve {p = e₁ `· e₂} (⊢-· ⊢₁ ⊢₂) ∈ = ⊢-· (↓ₚ-preserve ⊢₁ ∈) (↓ₚ-preserve ⊢₂ ∈)
↓ₚ-preserve {p = # x} ⊢-# p = ⊢-#
↓ₚ-preserve {p = e₁ `+ e₂} (⊢-+ ⊢₁ ⊢₂) ∈ = ⊢-+ (↓ₚ-preserve ⊢₁ ∈) (↓ₚ-preserve ⊢₂ ∈)

↓↑-ℕ : ∀ {x n} → ↓-ℕ (↑-ℕ x n) n ≡ x
↓↑-ℕ {zero} {zero} = refl
↓↑-ℕ {zero} {suc n} = refl
↓↑-ℕ {suc x} {zero} = refl
↓↑-ℕ {suc x} {suc n} = cong suc ↓↑-ℕ

↓↑-exp : ∀ {e n} → ↓ (↑ e from n) from (n) ≡ e
↓↑-pat : ∀ {p n} → ↓ₚ (↑ₚ p from n) from (n) ≡ p

↓↑-exp {` x} {n} = cong `_ ↓↑-ℕ
↓↑-exp {ƛ e} = cong ƛ_ ↓↑-exp
↓↑-exp {e₁ `· e₂} = cong₂ _`·_ ↓↑-exp ↓↑-exp
↓↑-exp {# x} = refl
↓↑-exp {e₁ `+ e₂} = cong₂ _`+_ ↓↑-exp ↓↑-exp
↓↑-exp {φ p , a , g ⇒ e} = cong₂ (λ p e → φ (p , a , g) ⇒ e) ↓↑-pat ↓↑-exp
↓↑-exp {δ x ⇒ e} = cong (δ x ⇒_) ↓↑-exp

↓↑-pat {$e} {n} = refl
↓↑-pat {$v} {n} = refl
↓↑-pat {` x} {n} = cong `_ ↓↑-ℕ
↓↑-pat {ƛ x} {n} = cong ƛ_ ↓↑-exp
↓↑-pat {p `· p₁} {n} = cong₂ _`·_ ↓↑-pat ↓↑-pat
↓↑-pat {# x} {n} = refl
↓↑-pat {p `+ p₁} {n} = cong₂ _`+_ ↓↑-pat ↓↑-pat

update-≡ : ∀ {Γ v τₓ}
  → (p : v < length Γ)
  → (update p τₓ) ∋ v ∶ τₓ
update-≡ {Γ ⸴ τ} {v = ℕ.zero} (s≤s p) = ∋-Z
update-≡ {Γ ⸴ τ} {v = ℕ.suc v} (s≤s p) = ∋-S (update-≡ p)

update-< : ∀ {Γ x y τ₁ τ₂}
  → (p : x < length Γ)
  → x < y
  → (update p τ₁) ∋ y ∶ τ₂
  → Γ ∋ y ∶ τ₂
update-< {Γ ⸴ τ′} {ℕ.zero} {ℕ.suc y} (s≤s z≤n) x<y (∋-S ∋₂) = ∋-S ∋₂
update-< {Γ ⸴ τ′} {ℕ.suc x} {ℕ.suc y} (s≤s p) (s≤s x<y) (∋-S ∋₂) = ∋-S (update-< p x<y ∋₂)

update-> : ∀ {Γ x y τ₁ τ₂}
  → (p : x < length Γ)
  → x > y
  → (update p τ₁) ∋ y ∶ τ₂
  → Γ ∋ y ∶ τ₂
update-> {Γ ⸴ τ′} {ℕ.suc x} {ℕ.zero} (s≤s p) (s≤s x>y) ∋-Z = ∋-Z
update-> {Γ ⸴ τ′} {ℕ.suc x} {ℕ.suc y} (s≤s p) (s≤s x>y) (∋-S ∋₂) = ∋-S (update-> p x>y ∋₂)

update-≢ : ∀ {Γ x y τ₁ τ₂}
  → (p : x < length Γ)
  → y ≢ x
  → (update p τ₁) ∋ y ∶ τ₂
  → Γ ∋ y ∶ τ₂
update-≢ {Γ} {x} {y} p x≢y ∋₂ with Data.Nat.<-cmp x y
update-≢ {Γ} {x} {y} p x≢y ∋₂ | tri< x<y _ _  = update-< p x<y ∋₂
update-≢ {Γ} {x} {_} p x≢y ∋₂ | tri≈ _ refl _ = ⊥-elim (x≢y refl)
update-≢ {Γ} {x} {y} p x≢y ∋₂ | tri> _ _ x>y  = update-> p x>y ∋₂

∋⇒∈ : ∀ {Γ x τ}
  → Γ ∋ x ∶ τ
  → x < length Γ
∋⇒∈ ∋-Z = s≤s z≤n
∋⇒∈ (∋-S ∋) = s≤s (∋⇒∈ ∋)

↑-miss : ∀ {Γ e τ}
  → Γ ⊢ e ∶ τ
  → Γ ⊢ (↑ e from (length Γ)) ∶ τ
↑ₚ-miss : ∀ {Γ p τ}
  → Γ ⊢ p ∻ τ
  → Γ ⊢ (↑ₚ p from (length Γ)) ∻ τ

↑-miss {Γ} (⊢-` {x = x} ∋) with x <? length Γ
↑-miss {Γ} (⊢-` {x = x} ∋) | yes x∈Γ = ⊢-` {!!}
↑-miss {Γ} (⊢-` {x = x} ∋) | no  x∉Γ = ⊥-elim (x∉Γ (∋⇒∈ ∋))
↑-miss (⊢-ƛ ⊢) = ⊢-ƛ (↑-miss ⊢)
↑-miss (⊢-· ⊢₁ ⊢₂) = ⊢-· (↑-miss ⊢₁) (↑-miss ⊢₂)
↑-miss (⊢-+ ⊢₁ ⊢₂) = ⊢-+ (↑-miss ⊢₁) (↑-miss ⊢₂)
↑-miss ⊢-# = ⊢-#
↑-miss (⊢-φ ⊢ₚ ⊢ₑ) = ⊢-φ (↑ₚ-miss ⊢ₚ) (↑-miss ⊢ₑ)
↑-miss (⊢-δ ⊢) = ⊢-δ (↑-miss ⊢)

↑ₚ-miss ⊢-E = ⊢-E
↑ₚ-miss ⊢-V = ⊢-V
↑ₚ-miss {Γ} (⊢-` {x = x} ∋) with x <? length Γ
↑ₚ-miss (⊢-` ∋) | yes x∈Γ = ⊢-` {!!}
↑ₚ-miss (⊢-` ∋) | no  x∉Γ = ⊥-elim (x∉Γ (∋⇒∈ ∋))
↑ₚ-miss (⊢-ƛ ⊢) = ⊢-ƛ (↑-miss ⊢)
↑ₚ-miss (⊢-· ⊢₁ ⊢₂) = ⊢-· (↑ₚ-miss ⊢₁) (↑ₚ-miss ⊢₂)
↑ₚ-miss (⊢-+ ⊢₁ ⊢₂) = ⊢-+ (↑ₚ-miss ⊢₁) (↑ₚ-miss ⊢₂)
↑ₚ-miss ⊢-# = ⊢-#

patternize-preserve : ∀ {Γ e τ}
  → Γ ⊢ e ∶ τ
  → Γ ⊢ patternize e ∻ τ
patternize-preserve (⊢-` ∋) = ⊢-` ∋
patternize-preserve (⊢-ƛ ⊢) = ⊢-ƛ ⊢
patternize-preserve (⊢-· ⊢₁ ⊢₂) = ⊢-· (patternize-preserve ⊢₁) (patternize-preserve ⊢₂)
patternize-preserve (⊢-+ ⊢₁ ⊢₂) = ⊢-+ (patternize-preserve ⊢₁) (patternize-preserve ⊢₂)
patternize-preserve ⊢-# = ⊢-#
patternize-preserve (⊢-φ ⊢ₚ ⊢ₑ) = patternize-preserve ⊢ₑ
patternize-preserve (⊢-δ ⊢) = patternize-preserve ⊢

subst : ∀ {Γ v τᵥ e τₑ x}
  → (p : x < length Γ)
  → ∅ ⊢ v ∶ τᵥ
  → (update p τᵥ) ⊢ e ∶ τₑ
  → Γ ⊢ e [ x := v ] ∶ τₑ
substₚ : ∀ {Γ v τᵥ p τₚ x}
  → (∈ : x < length Γ)
  → ∅ ⊢ v ∶ τᵥ
  → (update ∈ τᵥ) ⊢ p ∻ τₚ
  → Γ ⊢ p ⟨ x := v ⟩ ∻ τₚ

subst {x = y} p ⊢ᵥ (⊢-` {x = x} ∋) with x Data.Nat.≟ y
subst {τᵥ = τᵥ} {τₑ = τₑ} {x = y} p ⊢ᵥ (⊢-` {x = x} ∋) | yes refl with ((∋-functional {τ₂ = τₑ} (update-≡ {τₓ = τᵥ} p)) ∋)
subst {τᵥ = τᵥ} {τₑ = τᵥ} {x = y} p ⊢ᵥ (⊢-` {x = y} ∋) | yes refl | refl = weaken ⊢ᵥ
subst {x = y} p ⊢ᵥ (⊢-` {x = x} ∋) | no x≢y = ⊢-` (update-≢ p x≢y ∋)
subst p ⊢ᵥ (⊢-ƛ ⊢ₑ) = ⊢-ƛ (subst (s≤s p) (↑-miss ⊢ᵥ) ⊢ₑ)
subst p ⊢ᵥ (⊢-· ⊢₁ ⊢₂) = ⊢-· (subst p ⊢ᵥ ⊢₁) (subst p ⊢ᵥ ⊢₂)
subst p ⊢ᵥ (⊢-+ ⊢₁ ⊢₂) = ⊢-+ (subst p ⊢ᵥ ⊢₁) (subst p ⊢ᵥ ⊢₂)
subst p ⊢ᵥ ⊢-# = ⊢-#
subst p ⊢ᵥ (⊢-φ ⊢ₚ ⊢ₑ) = ⊢-φ (substₚ p ⊢ᵥ ⊢ₚ) (subst p ⊢ᵥ ⊢ₑ)
subst p ⊢ᵥ (⊢-δ ⊢ₑ) = ⊢-δ (subst p ⊢ᵥ ⊢ₑ)

substₚ {p = $e} ∈ ⊢ = λ _ → ⊢-E
substₚ {p = $v} ∈ ⊢ = λ _ → ⊢-V
substₚ {x = y} p ⊢ᵥ (⊢-` {x = x} ∋) with x Data.Nat.≟ y
substₚ {τᵥ = τᵥ} {τₚ = τₚ} {x = y} p ⊢ᵥ (⊢-` {x = x} ∋) | yes refl with ((∋-functional {τ₂ = τₚ} (update-≡ {τₓ = τᵥ} p)) ∋)
substₚ {τᵥ = τᵥ} {τₚ = τᵥ} {x = y} p ⊢ᵥ (⊢-` {x = y} ∋) | yes refl | refl = patternize-preserve (weaken ⊢ᵥ)
substₚ {x = y} p ⊢ᵥ (⊢-` {x = x} ∋) | no x≢y = ⊢-` (update-≢ p x≢y ∋)
substₚ p ⊢ᵥ (⊢-ƛ ⊢ₑ) = ⊢-ƛ (subst (s≤s p) (↑-miss ⊢ᵥ) ⊢ₑ)
substₚ p ⊢ᵥ (⊢-· ⊢₁ ⊢₂) = ⊢-· (substₚ p ⊢ᵥ ⊢₁) (substₚ p ⊢ᵥ ⊢₂)
substₚ p ⊢ᵥ (⊢-+ ⊢₁ ⊢₂) = ⊢-+ (substₚ p ⊢ᵥ ⊢₁) (substₚ p ⊢ᵥ ⊢₂)
substₚ p ⊢ᵥ ⊢-# = ⊢-#

strip-preserve : ∀ {Γ e τ}
  → Γ ⊢ e ∶ τ
  → Γ ⊢ (strip e) ∶ τ
strip-preserve (⊢-` ∋-x)   = ⊢-` ∋-x
strip-preserve (⊢-ƛ x⊢e)   = ⊢-ƛ (strip-preserve x⊢e)
strip-preserve (⊢-· ⊢₁ ⊢₂) = ⊢-· (strip-preserve ⊢₁) (strip-preserve ⊢₂)
strip-preserve (⊢-+ ⊢₁ ⊢₂) = ⊢-+ (strip-preserve ⊢₁) (strip-preserve ⊢₂)
strip-preserve ⊢-#         = ⊢-#
strip-preserve (⊢-φ ⊢ₚ ⊢ₑ) = strip-preserve ⊢ₑ
strip-preserve (⊢-δ ⊢ₑ)    = strip-preserve ⊢ₑ

instr-preserve : ∀ {Γ e τ p a g l e′}
  → Γ ⊢ e ∶ τ
  → (p , a , g , l) ⊢ e ⇝ e′
  → Γ ⊢ e′ ∶ τ
instr-preserve ⊢ (I-V V) = ⊢
instr-preserve ⊢ (I-`-⊤ x) = ⊢-δ ⊢
instr-preserve ⊢ (I-`-⊥ x) = ⊢
instr-preserve (⊢-· ⊢ₗ ⊢ᵣ) (I-·-⊤ x Iₗ Iᵣ) = ⊢-δ (⊢-· (instr-preserve ⊢ₗ Iₗ) (instr-preserve ⊢ᵣ Iᵣ))
instr-preserve (⊢-· ⊢ₗ ⊢ᵣ) (I-·-⊥ x Iₗ Iᵣ) = ⊢-· (instr-preserve ⊢ₗ Iₗ) (instr-preserve ⊢ᵣ Iᵣ)
instr-preserve (⊢-+ ⊢ₗ ⊢ᵣ) (I-+-⊤ x Iₗ Iᵣ) = ⊢-δ (⊢-+ (instr-preserve ⊢ₗ Iₗ) (instr-preserve ⊢ᵣ Iᵣ))
instr-preserve (⊢-+ ⊢ₗ ⊢ᵣ) (I-+-⊥ x Iₗ Iᵣ) = ⊢-+ (instr-preserve ⊢ₗ Iₗ) (instr-preserve ⊢ᵣ Iᵣ)
instr-preserve (⊢-φ ⊢ₚ ⊢ₑ) (I-Φ I₀ I₁) = ⊢-φ ⊢ₚ (instr-preserve (instr-preserve ⊢ₑ I₀) I₁)
instr-preserve (⊢-δ ⊢) (I-Δ I) = ⊢-δ (instr-preserve ⊢ I)

uname : ∀ {Γ Δ}
  → (∀ {e τ} → Γ ⊢ e ∶ τ → Δ ⊢ e ∶ τ)
  → (∀ {x τ} → Γ ∋ x ∶ τ → Δ ∋ x ∶ τ)
uname ρ {x = x} ∋ with (ρ (⊢-` ∋))
... | ⊢-` x′ = x′

⊢-ƛ-inj : ∀ {Γ e τₓ τₑ}
  → Γ ⊢ ƛ e ∶ (τₓ ⇒ τₑ)
  → Γ ⸴ τₓ ⊢ e ∶ τₑ
⊢-ƛ-inj (⊢-ƛ ⊢) = ⊢

exts-exp : ∀ {Γ Δ}
  → (∀ {e τ}    → Γ      ⊢ e ∶ τ → Δ      ⊢ e ∶ τ)
  → (∀ {e τ τ′} → Γ ⸴ τ′ ⊢ e ∶ τ → Δ ⸴ τ′ ⊢ e ∶ τ)
exts-pat : ∀ {Γ Δ}
  → (∀ {e τ}    → Γ      ⊢ e ∶ τ → Δ      ⊢ e ∶ τ)
  → (∀ {p τ τ′} → Γ ⸴ τ′ ⊢ p ∻ τ → Δ ⸴ τ′ ⊢ p ∻ τ)

exts-exp ρ (⊢-` x) = ⊢-` (ext (uname ρ) x)
exts-exp ρ (⊢-ƛ ⊢) = ⊢-ƛ (exts-exp (λ { x → ⊢-ƛ-inj (ρ (⊢-ƛ x)) }) ⊢)
exts-exp ρ (⊢-· ⊢₁ ⊢₂) = ⊢-· (exts-exp ρ ⊢₁) (exts-exp ρ ⊢₂)
exts-exp ρ (⊢-+ ⊢₁ ⊢₂) = ⊢-+ (exts-exp ρ ⊢₁) (exts-exp ρ ⊢₂)
exts-exp ρ ⊢-# = ⊢-#
exts-exp ρ (⊢-φ ⊢ₚ ⊢ₑ) = ⊢-φ (exts-pat ρ ⊢ₚ) (exts-exp ρ ⊢ₑ)
exts-exp ρ (⊢-δ ⊢) = ⊢-δ (exts-exp ρ ⊢)

exts-pat ρ ⊢-E = ⊢-E
exts-pat ρ ⊢-V = ⊢-V
exts-pat ρ (⊢-` x) = ⊢-` (ext (uname ρ) x)
exts-pat ρ (⊢-ƛ ⊢) = ⊢-ƛ (exts-exp (λ x → ⊢-ƛ-inj (ρ (⊢-ƛ x))) ⊢)
exts-pat ρ (⊢-· ⊢₁ ⊢₂) = ⊢-· (exts-pat ρ ⊢₁) (exts-pat ρ ⊢₂)
exts-pat ρ ⊢-# = ⊢-#
exts-pat ρ (⊢-+ ⊢₁ ⊢₂) = ⊢-+ (exts-pat ρ ⊢₁) (exts-pat ρ ⊢₂)

≡-app : ∀ {A : Set₁} {x y : Set} → x ≡ y → x → y
≡-app refl x = x

cong-app : ∀ {A : Set} {x y : A} → (f : A → Set) → x ≡ y → f x → f y
cong-app f refl fx = fx

·-preserve : ∀ {Γ v e τᵥ τₑ n}
  → ∅ ⊢ v ∶ τᵥ
  → Γ ⸴ τᵥ ⊢ e ∶ τₑ
  → Γ ⊢ (↓ (e [ n := ↑ v ]) from n) ∶ τₑ
·-preserve {v = v} {τᵥ = τᵥ} {n = zero} ⊢ᵥ (⊢-` ∋-Z) = weaken (cong-app (λ x → ∅ ⊢ x ∶ τᵥ) (sym ↓↑-exp) ⊢ᵥ)
·-preserve {v = v} {τᵥ = τᵥ} {n = suc n} ⊢ᵥ (⊢-` ∋-Z) = weaken {!!}
·-preserve ⊢ᵥ (⊢-` (∋-S {x = ℕ.zero} ∋ₓ)) = {!!}
·-preserve ⊢ᵥ (⊢-` (∋-S {x = ℕ.suc x} ∋ₓ)) = {!!}
·-preserve ⊢ᵥ (⊢-ƛ ⊢ₑ) = ⊢-ƛ {!!}
·-preserve ⊢ᵥ (⊢-· ⊢ₑ ⊢ₑ₁) = {!!}
·-preserve ⊢ᵥ (⊢-+ ⊢ₑ ⊢ₑ₁) = {!!}
·-preserve ⊢ᵥ ⊢-# = {!!}
·-preserve ⊢ᵥ (⊢-φ x ⊢ₑ) = {!!}
·-preserve ⊢ᵥ (⊢-δ ⊢ₑ) = {!!}

—→-preserve : ∀ {Γ e τ e′}
  → Γ ⊢ e ∶ τ
  → e —→ e′
  → Γ ⊢ e′ ∶ τ
—→-preserve (⊢-· ⊢ₗ ⊢ᵣ) (T-β-· Vᵣ) = {!!}
—→-preserve (⊢-+ ⊢ ⊢₁) T = {!!}
—→-preserve (⊢-φ x ⊢) T = {!!}

data ⇒-Progress : Exp → Set where
  step : ∀ {e ε₀ e₀}
    → e ⇒ ε₀ ⟨ e₀ ⟩
    → ⇒-Progress e

  done : ∀ {v}
    → Value v
    → ⇒-Progress v

⇒-progress : ∀ {e τ}
  → ∅ ⊢ e ∶ τ
  → ⇒-Progress e
⇒-progress (⊢-ƛ ⊢) = done V-ƛ
⇒-progress (⊢-· ⊢₁ ⊢₂) with (⇒-progress ⊢₁) with (⇒-progress ⊢₂)
... | step ⇒₁ | _        = step (D-ξ-·-l ⇒₁)
... | done V₁  | step ⇒₂ = step (D-ξ-·-r V₁ ⇒₂)
... | done V₁  | done V₂  = step (D-β-· V₁ V₂)
⇒-progress (⊢-+ ⊢₁ ⊢₂) with (⇒-progress ⊢₁) with (⇒-progress ⊢₂)
... | step ⇒₁ | _        = step (D-ξ-+-l ⇒₁)
... | done V₁  | step ⇒₂ = step (D-ξ-+-r V₁ ⇒₂)
... | done V₁  | done V₂  = step (D-β-+ V₁ V₂)
⇒-progress ⊢-# = done V-#
⇒-progress (⊢-φ f ⊢) with (⇒-progress ⊢)
... | step ⇒ₑ = step (D-ξ-φ ⇒ₑ)
... | done Vₑ  = step (D-β-φ Vₑ) 
⇒-progress (⊢-δ ⊢) with (⇒-progress ⊢)
... | step ⇒ₑ = step (D-ξ-δ ⇒ₑ)
... | done Vₑ  = step (D-β-δ Vₑ)

⇝-progress : ∀ {p a g l e e′}
  → (p , a , g , l) ⊢ e ⇥ e′
  → ∃[ eᵢ ] (p , a , g , l) ⊢ e ⇝ eᵢ
⇝-progress (step {eᵢ = eᵢ} I _ _ _ _) = eᵢ , I
⇝-progress (skip {eᵢ = eᵢ} I _ _ _ _ _) = eᵢ , I
⇝-progress {e = e} (done V) = e , I-V V

data Progress_under_ : Exp → Pat × Act × Gas × ℕ → Set where
  P : ∀ {p a g l e e′}
    → (p , a , g , l) ⊢ e ⇥ e′
    → Progress e under (p , a , g , l)

progress : ∀ {p a g l e τ}
  → ∅ ⊢ e ∶ τ
  → Progress e under (p , a , g , l)
progress (⊢-ƛ ⊢) = P (done V-ƛ)
progress (⊢-· ⊢₁ ⊢₂) = {!!}
progress (⊢-+ ⊢ ⊢₁) = {!!}
progress ⊢-# = {!!}
progress (⊢-φ x ⊢) = {!!}
progress (⊢-δ ⊢) = {!!}
