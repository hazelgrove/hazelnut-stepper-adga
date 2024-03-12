open import Data.String using (String)
open import Data.Nat using (ℕ; _+_; _≤_; _>_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (Dec; yes; no; ¬_; _×-dec_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; _≢_)
open import Function using (_↔_)

data Act : Set where
  eval : Act
  pause : Act

_≟-act_ : (a₁ : Act) → (a₂ : Act) → Dec (a₁ ≡ a₂)
eval ≟-act eval = yes refl
eval ≟-act pause = no (λ ())
pause ≟-act eval = no (λ ())
pause ≟-act pause = yes refl

data Gas : Set where
  one : Gas
  all : Gas

_≟-gas_ : (a₁ : Gas) → (a₂ : Gas) → Dec (a₁ ≡ a₂)
one ≟-gas one = yes refl
one ≟-gas all = no (λ ())
all ≟-gas one = no (λ ())
all ≟-gas all = yes refl

Id : Set
Id = String

data Pat : Set
data Exp : Set

infix 5 ƛ_⇒_
infix 5 φ_⇒_
infix 5 δ_⇒_
infixl 7 _`+_
infixl 8 _`·_
infix 9 #_
infix 9 `_

_≟-pat_ : (p₁ : Pat) → (p₂ : Pat) → Dec (p₁ ≡ p₂)
_≟-exp_ : (e₁ : Exp) → (e₂ : Exp) → Dec (e₁ ≡ e₂)

data Pat where
  $e     : Pat
  $v     : Pat
  `_     : Id → Pat
  ƛ_⇒_  : Id → Exp → Pat
  _`·_   : Pat → Pat → Pat
  #_     : ℕ → Pat
  _`+_   : Pat → Pat → Pat

$e ≟-pat $e = yes refl
$e ≟-pat $v = no (λ ())
$e ≟-pat (` x) = no (λ ())
$e ≟-pat (ƛ x ⇒ x₁) = no (λ ())
$e ≟-pat (p₂ `· p₃) = no (λ ())
$e ≟-pat (# x) = no (λ ())
$e ≟-pat (p₂ `+ p₃) = no (λ ())
$v ≟-pat $e = no (λ ())
$v ≟-pat $v = yes refl
$v ≟-pat (` x) = no (λ ())
$v ≟-pat (ƛ x ⇒ x₁) = no (λ ())
$v ≟-pat (p₂ `· p₃) = no (λ ())
$v ≟-pat (# x) = no (λ ())
$v ≟-pat (p₂ `+ p₃) = no (λ ())
(` x) ≟-pat $e = no (λ ())
(` x) ≟-pat $v = no (λ ())
(` x) ≟-pat (` y) with (x Data.String.≟ y)
... | yes refl = yes refl
... | no ¬x≡y  = no λ { refl → ¬x≡y refl }
(` x) ≟-pat (ƛ x₁ ⇒ x₂) = no (λ ())
(` x) ≟-pat (p₂ `· p₃) = no (λ ())
(` x) ≟-pat (# x₁) = no (λ ())
(` x) ≟-pat (p₂ `+ p₃) = no (λ ())
(ƛ x ⇒ x₁) ≟-pat $e = no (λ ())
(ƛ x ⇒ x₁) ≟-pat $v = no (λ ())
(ƛ x ⇒ x₁) ≟-pat (` x₂) = no (λ ())
(ƛ x ⇒ p₁) ≟-pat (ƛ y ⇒ p₂) with (x Data.String.≟ y) ×-dec (p₁ ≟-exp p₂)
... | yes (refl , refl) = yes refl
... | no x≢y⊎p₁≢p₂ = no λ { refl → x≢y⊎p₁≢p₂ (refl , refl) }
(ƛ x ⇒ x₁) ≟-pat (p₂ `· p₃) = no (λ ())
(ƛ x ⇒ x₁) ≟-pat (# x₂) = no (λ ())
(ƛ x ⇒ x₁) ≟-pat (p₂ `+ p₃) = no (λ ())
(p₁ `· p₃) ≟-pat $e = no (λ ())
(p₁ `· p₃) ≟-pat $v = no (λ ())
(p₁ `· p₃) ≟-pat (` x) = no (λ ())
(p₁ `· p₃) ≟-pat (ƛ x ⇒ x₁) = no (λ ())
(p₁ `· p₃) ≟-pat (p₂ `· p₄) with (p₁ ≟-pat p₂) ×-dec (p₃ ≟-pat p₄)
... | yes (refl , refl) = yes refl
... | no ¬1≟-pat2⊎¬3≟-pat4 = no λ { refl → ¬1≟-pat2⊎¬3≟-pat4 (refl , refl) }
(p₁ `· p₃) ≟-pat (# x) = no (λ ())
(p₁ `· p₃) ≟-pat (p₂ `+ p₄) = no (λ ())
(# x) ≟-pat $e = no (λ ())
(# x) ≟-pat $v = no (λ ())
(# x) ≟-pat (` x₁) = no (λ ())
(# x) ≟-pat (ƛ x₁ ⇒ x₂) = no (λ ())
(# x) ≟-pat (p₂ `· p₃) = no (λ ())
(# x) ≟-pat (# y) with (x Data.Nat.≟ y)
... | yes refl = yes refl
... | no x≢y = no λ { refl → x≢y refl }
(# x) ≟-pat (p₂ `+ p₃) = no (λ ())
(p₁ `+ p₃) ≟-pat $e = no (λ ())
(p₁ `+ p₃) ≟-pat $v = no (λ ())
(p₁ `+ p₃) ≟-pat (` x) = no (λ ())
(p₁ `+ p₃) ≟-pat (ƛ x ⇒ x₁) = no (λ ())
(p₁ `+ p₃) ≟-pat (p₂ `· p₄) = no (λ ())
(p₁ `+ p₃) ≟-pat (# x) = no (λ ())
(p₁ `+ p₃) ≟-pat (p₂ `+ p₄) with (p₁ ≟-pat p₂) ×-dec (p₃ ≟-pat p₄)
... | yes (refl , refl) = yes refl
... | no ¬1≟-pat2⊎¬3≟-pat4 = no λ { refl → ¬1≟-pat2⊎¬3≟-pat4 (refl , refl) }

data Exp where
  `_     : Id → Exp
  ƛ_⇒_  : Id → Exp → Exp
  _`·_   : Exp → Exp → Exp
  #_     : ℕ → Exp
  _`+_   : Exp → Exp → Exp
  φ_⇒_  : Pat × Act × Gas → Exp → Exp
  δ_⇒_  : Act × Gas × ℕ   → Exp → Exp

(` x) ≟-exp (` y) with x Data.String.≟ y
... | yes refl = yes refl
... | no ¬x≟-expy = no λ { refl → ¬x≟-expy refl }
(` x) ≟-exp (ƛ x₁ ⇒ e₂) = no (λ ())
(` x) ≟-exp (e₂ `· e₃) = no (λ ())
(` x) ≟-exp (# x₁) = no (λ ())
(` x) ≟-exp (e₂ `+ e₃) = no (λ ())
(` x) ≟-exp (φ x₁ ⇒ e₂) = no (λ ())
(` x) ≟-exp (δ x₁ ⇒ e₂) = no (λ ())
(ƛ x ⇒ e₁) ≟-exp (` x₁) = no (λ ())
(ƛ x ⇒ e₁) ≟-exp (ƛ y ⇒ e₂) with (x Data.String.≟ y) ×-dec (e₁ ≟-exp e₂)
... | yes (refl , refl) = yes refl
... | no ¬x≟-expy⊎¬e₁≟-expe₂ = no λ { refl → ¬x≟-expy⊎¬e₁≟-expe₂ (refl , refl) }
(ƛ x ⇒ e₁) ≟-exp (e₂ `· e₃) = no (λ ())
(ƛ x ⇒ e₁) ≟-exp (# x₁) = no (λ ())
(ƛ x ⇒ e₁) ≟-exp (e₂ `+ e₃) = no (λ ())
(ƛ x ⇒ e₁) ≟-exp (φ x₁ ⇒ e₂) = no (λ ())
(ƛ x ⇒ e₁) ≟-exp (δ x₁ ⇒ e₂) = no (λ ())
(e₁ `· e₃) ≟-exp (` x) = no (λ ())
(e₁ `· e₃) ≟-exp (ƛ x ⇒ e₂) = no (λ ())
(e₁ `· e₃) ≟-exp (e₂ `· e₄) with (e₁ ≟-exp e₂) ×-dec (e₃ ≟-exp e₄)
... | yes (refl , refl) = yes refl
... | no ¬1≟-exp2⊎¬3≟-exp4 = no λ { refl → ¬1≟-exp2⊎¬3≟-exp4 (refl , refl) }
(e₁ `· e₃) ≟-exp (# x) = no (λ ())
(e₁ `· e₃) ≟-exp (e₂ `+ e₄) = no (λ ())
(e₁ `· e₃) ≟-exp (φ x ⇒ e₂) = no (λ ())
(e₁ `· e₃) ≟-exp (δ x ⇒ e₂) = no (λ ())
(# x) ≟-exp (` x₁) = no (λ ())
(# x) ≟-exp (ƛ x₁ ⇒ e₂) = no (λ ())
(# x) ≟-exp (e₂ `· e₃) = no (λ ())
(# x) ≟-exp (# y) with x Data.Nat.≟ y
... | yes refl = yes refl
... | no ¬x≟-expy = no λ { refl → ¬x≟-expy refl }
(# x) ≟-exp (e₂ `+ e₃) = no (λ ())
(# x) ≟-exp (φ x₁ ⇒ e₂) = no (λ ())
(# x) ≟-exp (δ x₁ ⇒ e₂) = no (λ ())
(e₁ `+ e₃) ≟-exp (` x) = no (λ ())
(e₁ `+ e₃) ≟-exp (ƛ x ⇒ e₂) = no (λ ())
(e₁ `+ e₃) ≟-exp (e₂ `· e₄) = no (λ ())
(e₁ `+ e₃) ≟-exp (# x) = no (λ ())
(e₁ `+ e₃) ≟-exp (e₂ `+ e₄) with (e₁ ≟-exp e₂) ×-dec (e₃ ≟-exp e₄)
... | yes (refl , refl) = yes refl
... | no ¬1≟-exp2⊎¬3≟-exp4 = no λ { refl → ¬1≟-exp2⊎¬3≟-exp4 (refl , refl) }
(e₁ `+ e₃) ≟-exp (φ x ⇒ e₂) = no (λ ())
(e₁ `+ e₃) ≟-exp (δ x ⇒ e₂) = no (λ ())
(φ x ⇒ e₁) ≟-exp (` x₁) = no (λ ())
(φ x ⇒ e₁) ≟-exp (ƛ x₁ ⇒ e₂) = no (λ ())
(φ x ⇒ e₁) ≟-exp (e₂ `· e₃) = no (λ ())
(φ x ⇒ e₁) ≟-exp (# x₁) = no (λ ())
(φ x ⇒ e₁) ≟-exp (e₂ `+ e₃) = no (λ ())
(φ (p₁ , a₁ , g₁) ⇒ e₁) ≟-exp (φ (p₂ , a₂ , g₂) ⇒ e₂) with (p₁ ≟-pat p₂) ×-dec (a₁ ≟-act a₂) ×-dec (g₁ ≟-gas g₂) ×-dec (e₁ ≟-exp e₂)
... | yes (refl , refl , refl , refl) = yes refl
... | no ¬≟ = no λ { refl → ¬≟ (refl , refl , refl , refl) }
(φ x ⇒ e₁) ≟-exp (δ x₁ ⇒ e₂) = no (λ ())
(δ x ⇒ e₁) ≟-exp (` x₁) = no (λ ())
(δ x ⇒ e₁) ≟-exp (ƛ x₁ ⇒ e₂) = no (λ ())
(δ x ⇒ e₁) ≟-exp (e₂ `· e₃) = no (λ ())
(δ x ⇒ e₁) ≟-exp (# x₁) = no (λ ())
(δ x ⇒ e₁) ≟-exp (e₂ `+ e₃) = no (λ ())
(δ x ⇒ e₁) ≟-exp (φ x₁ ⇒ e₂) = no (λ ())
(δ (a₁ , g₁ , l₁) ⇒ e₁) ≟-exp (δ (a₂ , g₂ , l₂) ⇒ e₂) with (a₁ ≟-act a₂) ×-dec (g₁ ≟-gas g₂) ×-dec (l₁ Data.Nat.≟ l₂) ×-dec (e₁ ≟-exp e₂)
... | yes (refl , refl , refl , refl) = yes refl
... | no ¬≟ = no λ { refl → ¬≟ (refl , refl , refl , refl) }

data Value : Exp → Set where
  V-# : ∀ {n : ℕ}
    → Value (# n)

  V-ƛ : ∀ {x L}
    → Value (ƛ x ⇒ L)

value? : ∀ (e : Exp) → Dec (Value e)
value? (` x) = no λ ()
value? (ƛ x ⇒ e) = yes V-ƛ
value? (e `· e₁) = no (λ ())
value? (# x) = yes V-#
value? (e `+ e₁) = no (λ ())
value? (φ x ⇒ e) = no (λ ())
value? (δ x ⇒ e) = no (λ ())

data Normal : Exp → Set where
  N-` : ∀ {x} → Normal (` x)
  N-ƛ : ∀ {x e} → Normal e → Normal (ƛ x ⇒ e)
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
filter? (ƛ x ⇒ e) = no λ ()
filter? (e `· e₁) = no λ ()
filter? (# x) = no λ ()
filter? (e `+ e₁) = no λ ()
filter? (φ x ⇒ e) = yes F-Φ
filter? (δ x ⇒ e) = yes F-Δ

data PatVal : Pat → Set where
  PV-# : ∀ {n}
    → PatVal (# n)

  PV-ƛ : ∀ {x e}
    → PatVal (ƛ x ⇒ e)

strip : Exp → Exp
strip (` x) = ` x
strip (ƛ x ⇒ L) = ƛ x ⇒ (strip L)
strip (L `· M) = (strip L) `· (strip M)
strip (# n) = # n
strip (L `+ M) = (strip L) `+ (strip M)
strip (φ x ⇒ L) = strip L
strip (δ x ⇒ L) = strip L

strip-normal : ∀ (e : Exp) → Normal (strip e)
strip-normal (` x) = N-`
strip-normal (ƛ x ⇒ e) = N-ƛ (strip-normal e)
strip-normal (e₁ `· e₂) = N-· (strip-normal e₁) (strip-normal e₂)
strip-normal (# x) = N-#
strip-normal (e₁ `+ e₂) = N-+ (strip-normal e₁) (strip-normal e₂)
strip-normal (φ x ⇒ e) = strip-normal e
strip-normal (δ x ⇒ e) = strip-normal e

patternize : Exp → Pat
patternize (` x) = ` x
patternize (ƛ x ⇒ L) = ƛ x ⇒ L
patternize (L `· M) = (patternize L) `· (patternize M)
patternize (# n) = # n
patternize (L `+ M) = (patternize L) `+ (patternize M)
patternize (φ x ⇒ L) = patternize L
patternize (δ x ⇒ L) = patternize L

_⟨_:=_⟩ : Pat → Id → Exp → Pat
_[_:=_] : Exp → Id → Exp → Exp

_⟨_:=_⟩ $e x V = $e
_⟨_:=_⟩ $v x V = $v
_⟨_:=_⟩ (` x) y V with (x Data.String.≟ y)
... | yes _ = patternize V
... | no  _ = (` x)
_⟨_:=_⟩ (ƛ x ⇒ L) y V with (x Data.String.≟ y)
... | yes _ = (ƛ x ⇒ L)
... | no  _ = (ƛ x ⇒ (L [ y := V ]))
_⟨_:=_⟩ (L `· M) x V = (L ⟨ x := V ⟩) `· (M ⟨ x := V ⟩)
_⟨_:=_⟩ (# n) x V = # n
_⟨_:=_⟩ (L `+ M) x V = (L ⟨ x := V ⟩) `+ (M ⟨ x := V ⟩)

_[_:=_] (` x) y V with (x Data.String.≟ y)
... | yes _ = V
... | no  _ = (` x)
_[_:=_] (ƛ x ⇒ L) y V with (x Data.String.≟ y)
... | yes _ = (ƛ x ⇒ L)
... | no  _ = (ƛ x ⇒ (L [ y := V ]))
_[_:=_] (L `· M) x V = (L [ x := V ]) `· (M [ x := V ])
_[_:=_] (# n) x V = # n
_[_:=_] (L `+ M) x V = (L [ x := V ]) `+ (M [ x := V ])
_[_:=_] (φ (p , a , g) ⇒ L) y V = φ (p ⟨ y := V ⟩) , a , g ⇒ L [ y := V ]
_[_:=_] (δ x ⇒ L) y V = δ x ⇒ L [ y := V ]

data _≡α_ : Exp → Exp → Set where
  ≡α-` : ∀ {x} → (` x) ≡α (` x)

  ≡α-ƛ : ∀ {x₁ e₁ x₂ e₂}
    → e₁ ≡α (e₂ [ x₂ := (` x₁) ])
    → (ƛ x₁ ⇒ e₁) ≡α (ƛ x₂ ⇒ e₂)

  ≡α-· : ∀ {e₁ e₂ e₃ e₄}
    → e₁ ≡α e₃
    → e₂ ≡α e₄
    → (e₁ `· e₂) ≡α (e₃ `· e₄)

  ≡α-# : ∀ {n} → (# n) ≡α (# n)

  ≡α-+ : ∀ {e₁ e₂ e₃ e₄}
    → e₁ ≡α e₃
    → e₂ ≡α e₄
    → (e₁ `+ e₂) ≡α (e₃ `+ e₄)

  ≡α-δ : ∀ {agl₁ e₁ agl₂ e₂}
    → agl₁ ≡ agl₂
    → e₁ ≡α e₂
    → (δ agl₁ ⇒ e₁) ≡α (δ agl₂ ⇒ e₂)

  ≡α-φ : ∀ {pag₁ e₁ pag₂ e₂}
    → pag₁ ≡ pag₂
    → e₁ ≡α e₂
    → (φ pag₁ ⇒ e₁) ≡α (φ pag₂ ⇒ e₂)

_≡α?_ : (e₁ : Exp) → (e₂ : Exp) → Dec (e₁ ≡α e₂)
(` x) ≡α? (` y) with x Data.String.≟ y
... | yes refl = yes ≡α-`
... | no ¬≟ = no λ { ≡α-` → ¬≟ refl }
(` x) ≡α? (ƛ x₁ ⇒ e₂) = no λ ()
(` x) ≡α? (e₂ `· e₃) = no λ ()
(` x) ≡α? (# x₁) = no λ ()
(` x) ≡α? (e₂ `+ e₃) = no λ ()
(` x) ≡α? (φ x₁ ⇒ e₂) = no λ ()
(` x) ≡α? (δ x₁ ⇒ e₂) = no λ ()
(ƛ x₁ ⇒ e₁) ≡α? (` x₂) = no λ ()
(ƛ x₁ ⇒ e₁) ≡α? (ƛ x₂ ⇒ e₂) with e₁ ≡α? (e₂ [ x₂ := (` x₁) ])
... | yes e₁≡αe₂ = yes (≡α-ƛ e₁≡αe₂)
... | no ¬e₁≡αe₂ = no λ { (≡α-ƛ e₁≡αe₂) → ¬e₁≡αe₂ e₁≡αe₂ }
(ƛ x₁ ⇒ e₁) ≡α? (e₂ `· e₃) = no λ ()
(ƛ x₁ ⇒ e₁) ≡α? (# x₂) = no λ ()
(ƛ x₁ ⇒ e₁) ≡α? (e₂ `+ e₃) = no λ ()
(ƛ x₁ ⇒ e₁) ≡α? (φ x₂ ⇒ e₂) = no λ ()
(ƛ x₁ ⇒ e₁) ≡α? (δ x₂ ⇒ e₂) = no λ ()
(e₁ `· e₂) ≡α? (` x) = no λ ()
(e₁ `· e₂) ≡α? (ƛ x ⇒ e₃) = no λ ()
(e₁ `· e₂) ≡α? (e₃ `· e₄) with e₁ ≡α? e₃
... | no ¬e₁≡αe₃ = no λ { (≡α-· e₁≡αe₃ _) → ¬e₁≡αe₃ e₁≡αe₃ }
... | yes e₁≡αe₃ with e₂ ≡α? e₄
... | no ¬e₂≡αe₄ = no λ { (≡α-· _ e₂≡αe₄) → ¬e₂≡αe₄ e₂≡αe₄ }
... | yes e₂≡αe₄ = yes (≡α-· e₁≡αe₃ e₂≡αe₄)
(e₁ `· e₂) ≡α? (# x) = no λ ()
(e₁ `· e₂) ≡α? (e₃ `+ e₄) = no λ ()
(e₁ `· e₂) ≡α? (φ x ⇒ e₃) = no λ ()
(e₁ `· e₂) ≡α? (δ x ⇒ e₃) = no λ ()
(# n₁) ≡α? (` x) = no λ ()
(# n₁) ≡α? (ƛ x ⇒ e₂) = no λ ()
(# n₁) ≡α? (e₂ `· e₃) = no λ ()
(# n₁) ≡α? (# n₂) with n₁ Data.Nat.≟ n₂
... | yes refl = yes ≡α-#
... | no ¬n₁≡n₂ = no λ { ≡α-# → ¬n₁≡n₂ refl }
(# n₁) ≡α? (e₂ `+ e₃) = no λ ()
(# n₁) ≡α? (φ x ⇒ e₂) = no λ ()
(# n₁) ≡α? (δ x ⇒ e₂) = no λ ()
(e₁ `+ e₂) ≡α? (` x) = no λ ()
(e₁ `+ e₂) ≡α? (ƛ x ⇒ e₃) = no λ ()
(e₁ `+ e₂) ≡α? (e₃ `· e₄) = no λ ()
(e₁ `+ e₂) ≡α? (# x) = no λ ()
(e₁ `+ e₂) ≡α? (e₃ `+ e₄) with e₁ ≡α? e₃
... | no ¬e₁≡αe₃ = no λ { (≡α-+ e₁≡αe₃ _) → ¬e₁≡αe₃ e₁≡αe₃ }
... | yes e₁≡αe₃ with e₂ ≡α? e₄
... | no ¬e₂≡αe₄ = no λ { (≡α-+ _ e₂≡αe₄) → ¬e₂≡αe₄ e₂≡αe₄ }
... | yes e₂≡αe₄ = yes (≡α-+ e₁≡αe₃ e₂≡αe₄)
(e₁ `+ e₂) ≡α? (φ x ⇒ e₃) = no λ ()
(e₁ `+ e₂) ≡α? (δ x ⇒ e₃) = no λ ()
(φ x ⇒ e₁) ≡α? (` x₁) = no λ ()
(φ x ⇒ e₁) ≡α? (ƛ x₁ ⇒ e₂) = no λ ()
(φ x ⇒ e₁) ≡α? (e₂ `· e₃) = no λ ()
(φ x ⇒ e₁) ≡α? (# x₁) = no λ ()
(φ x ⇒ e₁) ≡α? (e₂ `+ e₃) = no λ ()
(φ (p₁ , a₁ , g₁) ⇒ e₁) ≡α? (φ (p₂ , a₂ , g₂) ⇒ e₂) with (p₁ ≟-pat p₂)
... | no ¬p₁≡p₂ = no λ { (≡α-φ refl _) → ¬p₁≡p₂ refl }
... | yes refl with (a₁ ≟-act a₂)
... | no ¬a₁≡a₂ = no λ { (≡α-φ refl _) → ¬a₁≡a₂ refl }
... | yes refl with (g₁ ≟-gas g₂)
... | no ¬g₁≡g₂ = no λ { (≡α-φ refl _) → ¬g₁≡g₂ refl }
... | yes refl with (e₁ ≡α? e₂)
... | no ¬e₁≡αe₂ = no λ { (≡α-φ refl e₁≡αe₂) → ¬e₁≡αe₂ e₁≡αe₂ }
... | yes e₁≡αe₂ = yes (≡α-φ refl e₁≡αe₂)
(φ x ⇒ e₁) ≡α? (δ x₁ ⇒ e₂) = no λ ()
(δ x₁ ⇒ e₁) ≡α? (` x) = no λ ()
(δ x₁ ⇒ e₁) ≡α? (ƛ x ⇒ e₂) = no λ ()
(δ x₁ ⇒ e₁) ≡α? (e₂ `· e₃) = no λ ()
(δ x₁ ⇒ e₁) ≡α? (# x) = no λ ()
(δ x₁ ⇒ e₁) ≡α? (e₂ `+ e₃) = no λ ()
(δ x₁ ⇒ e₁) ≡α? (φ x ⇒ e₂) = no λ ()
(δ (a₁ , g₁ , l₁) ⇒ e₁) ≡α? (δ (a₂ , g₂ , l₂) ⇒ e₂)  with (a₁ ≟-act a₂)
... | no ¬a₁≡a₂ = no λ { (≡α-δ refl _) → ¬a₁≡a₂ refl }
... | yes refl with (g₁ ≟-gas g₂)
... | no ¬g₁≡g₂ = no λ { (≡α-δ refl _) → ¬g₁≡g₂ refl }
... | yes refl with (l₁ Data.Nat.≟ l₂)
... | no ¬l₁≡l₂ = no λ { (≡α-δ refl _) → ¬l₁≡l₂ refl }
... | yes refl with (e₁ ≡α? e₂)
... | no ¬e₁≡αe₂ = no λ { (≡α-δ refl e₁≡αe₂) → ¬e₁≡αe₂ e₁≡αe₂ }
... | yes e₁≡αe₂ = yes (≡α-δ refl e₁≡αe₂)

infix 4 _⊳_

data _⊳_ : Pat → Exp → Set where
  M-E : ∀ {e}
    → $e ⊳ e

  M-V : ∀ {v}
    → Value v
    → $v ⊳ v

  M-· : ∀ {pₗ pᵣ eₗ eᵣ}
    → pₗ ⊳ eₗ
    → pᵣ ⊳ eᵣ
    → (pₗ `· pᵣ) ⊳ (eₗ `· eᵣ)

  M-+ : ∀ {pₗ pᵣ eₗ eᵣ}
    → pₗ ⊳ eₗ
    → pᵣ ⊳ eᵣ
    → (pₗ `+ pᵣ) ⊳ (eₗ `+ eᵣ)

  M-ƛ : ∀ {x eₚ y eₑ}
    → (strip (ƛ x ⇒ eₚ)) ≡α (strip (ƛ y ⇒ eₑ))
    → (ƛ x ⇒ eₚ) ⊳ (ƛ y ⇒ eₑ)

_matches_ : Pat → Exp → Set
p matches e = p ⊳ e

_matches?_ : (p : Pat) → (e : Exp) → Dec (p ⊳ e)
$e matches? e = yes M-E
$v matches? v with (value? v)
... | yes V = yes (M-V V)
... | no ¬V = no λ { (M-V V) → ¬V V }
(` x) matches? e = no λ ()
(ƛ x ⇒ x₁) matches? (` x₂) = no (λ ())
(ƛ x ⇒ eₚ) matches? (ƛ y ⇒ eₑ) with ((strip (ƛ x ⇒ eₚ)) ≡α? (strip (ƛ y ⇒ eₑ)))
... | no NEQ = no λ { (M-ƛ EQ) → NEQ EQ }
... | yes EQ = yes (M-ƛ EQ)
(ƛ x ⇒ x₁) matches? (e `· e₁) = no (λ ())
(ƛ x ⇒ x₁) matches? (# x₂) = no (λ ())
(ƛ x ⇒ x₁) matches? (e `+ e₁) = no (λ ())
(ƛ x ⇒ x₁) matches? (φ x₂ ⇒ e) = no (λ ())
(ƛ x ⇒ x₁) matches? (δ x₂ ⇒ e) = no (λ ())
(p `· p₁) matches? (` x) = no (λ ())
(p `· p₁) matches? (ƛ x ⇒ e) = no (λ ())
(p₁ `· p₂) matches? (e₁ `· e₂) with (p₁ matches? e₁)
... | no ¬⊳ = no λ { (M-· ⊳ _) → ¬⊳ ⊳ }
... | yes ⊳₁ with (p₂ matches? e₂)
... | no ¬⊳ = no λ { (M-· _ ⊳) → ¬⊳ ⊳ }
... | yes ⊳₂ = yes (M-· ⊳₁ ⊳₂)
(p `· p₁) matches? (# x) = no (λ ())
(p `· p₁) matches? (e `+ e₁) = no (λ ())
(p `· p₁) matches? (φ x ⇒ e) = no (λ ())
(p `· p₁) matches? (δ x ⇒ e) = no (λ ())
(# x) matches? e = no (λ ())
(p `+ p₁) matches? (` x) = no (λ ())
(p `+ p₁) matches? (ƛ x ⇒ e) = no (λ ())
(p `+ p₁) matches? (e `· e₁) = no (λ ())
(p `+ p₁) matches? (# x) = no (λ ())
(p₁ `+ p₂) matches? (e₁ `+ e₂) with (p₁ matches? e₁)
... | no ¬⊳ = no λ { (M-+ ⊳ _) → ¬⊳ ⊳ }
... | yes ⊳₁ with (p₂ matches? e₂)
... | no ¬⊳ = no λ { (M-+ _ ⊳) → ¬⊳ ⊳ }
... | yes ⊳₂ = yes (M-+ ⊳₁ ⊳₂)
(p `+ p₁) matches? (φ x ⇒ e) = no (λ ())
(p `+ p₁) matches? (δ x ⇒ e) = no (λ ())

infix 0 _—→_

data _—→_ : Exp → Exp → Set where
  ξ-·ₗ : ∀ {eₗ eᵣ eₗ′}
    → eₗ —→ eₗ′
    → eₗ `· eᵣ —→ eₗ′ `· eᵣ

  ξ-·ᵣ : ∀ {eᵣ vₗ eᵣ′}
    → Value vₗ
    → eᵣ —→ eᵣ′
    → vₗ `· eᵣ —→ vₗ `· eᵣ′

  β-· : ∀ {vᵣ x eₓ}
    → Value vᵣ
    → (ƛ x ⇒ eₓ) `· vᵣ —→ (eₓ [ x := vᵣ ])

  ξ-+ₗ : ∀ {eₗ eᵣ eₗ′}
    → eₗ —→ eₗ′
    → eₗ `+ eᵣ —→ eₗ′ `+ eᵣ

  ξ-+ᵣ : ∀ {eᵣ vₗ eᵣ′}
    → Value vₗ
    → eᵣ —→ eᵣ′
    → vₗ `+ eᵣ —→ vₗ `+ eᵣ′

  β-+ : ∀ {vᵣ x eₓ}
    → Value vᵣ
    → (ƛ x ⇒ eₓ) `+ vᵣ —→ (eₓ [ x := vᵣ ])

  ξ-φ : ∀ {pag e e′}
    → e —→ e′
    → (φ pag ⇒ e) —→ (φ pag ⇒ e′)

  β-φ : ∀ {pag v}
    → Value v
    → (φ pag ⇒ v) —→ v

  ξ-δ : ∀ {agl e e′}
    → e —→ e′
    → (δ agl ⇒ e) —→ (δ agl ⇒ e′)

  β-δ : ∀ {agl v}
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

  D-ξ-·ₗ : ∀ {eₗ eᵣ ℰ eₗ′}
    → eₗ ⇒ ℰ ⟨ eₗ′ ⟩
    → (eₗ `· eᵣ) ⇒ (ℰ ·ₗ eᵣ) ⟨ eₗ′ ⟩

  D-ξ-·ᵣ : ∀ {eₗ eᵣ ℰ eᵣ′}
    → eᵣ ⇒ ℰ ⟨ eᵣ′ ⟩
    → (eₗ `· eᵣ) ⇒ (eₗ ·ᵣ ℰ) ⟨ eᵣ′ ⟩

  D-β-· : ∀ {vₗ vᵣ ℰ}
    → Value vₗ
    → Value vᵣ
    → (vₗ `· vᵣ) ⇒ ℰ ⟨ vₗ `· vᵣ ⟩

  D-ξ-+ₗ : ∀ {eₗ eᵣ ℰ eₗ′}
    → eₗ ⇒ ℰ ⟨ eₗ′ ⟩
    → (eₗ `+ eᵣ) ⇒ (ℰ +ₗ eᵣ) ⟨ eₗ′ ⟩

  D-ξ-+ᵣ : ∀ {eₗ eᵣ ℰ eᵣ′}
    → eᵣ ⇒ ℰ ⟨ eᵣ′ ⟩
    → (eₗ `+ eᵣ) ⇒ (eₗ +ᵣ ℰ) ⟨ eᵣ′ ⟩

  D-β-+ : ∀ {vₗ vᵣ ℰ}
    → Value vₗ
    → Value vᵣ
    → (vₗ `+ vᵣ) ⇒ ℰ ⟨ vₗ `+ vᵣ ⟩

  D-ξ-φ : ∀ {pag e ℰ e′}
    → e ⇒ ℰ ⟨ e′ ⟩
    → (φ pag ⇒ e) ⇒ (φ pag ⇒ ℰ) ⟨ e′ ⟩

  D-β-φ : ∀ {pag v ℰ}
    → Value v
    → (φ pag ⇒ v) ⇒ ℰ ⟨ φ pag ⇒ v ⟩

  D-ξ-δ : ∀ {agl e ℰ e′}
    → e ⇒ ℰ ⟨ e′ ⟩
    → (δ agl ⇒ e) ⇒ (δ agl ⇒ ℰ) ⟨ e′ ⟩

  D-β-δ : ∀ {agl v ℰ}
    → Value v
    → (δ agl ⇒ v) ⇒ ℰ ⟨ δ agl ⇒ v ⟩

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
    → p ⊳ (` x)
    → (p , a , g , l) ⊢ (` x) ⇝ (δ (a , g , l) ⇒ (` x))

  I-`-⊥ : ∀ {p a g l x}
    → ¬ (p ⊳ (` x))
    → (p , a , g , l) ⊢ (` x) ⇝ (` x)

  I-·-⊤ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → p ⊳ (eₗ `· eᵣ)
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ `· eᵣ) ⇝ (δ (a , g , l) ⇒ (eₗ′ `· eᵣ′))

  I-·-⊥ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → ¬ (p ⊳ (eₗ `· eᵣ))
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ `· eᵣ) ⇝ (eₗ′ `· eᵣ′)

  I-+-⊤ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → p ⊳ (eₗ `+ eᵣ)
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ `+ eᵣ) ⇝ (δ (a , g , l) ⇒ (eₗ′ `+ eᵣ′))

  I-+-⊥ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → ¬ (p ⊳ (eₗ `+ eᵣ))
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

data _⊢_⇝_⊣_ : Act × ℕ → Ctx → Ctx → Act → Set where
  A-∘ : ∀ {act lvl}
    → (act , lvl) ⊢ ∘ ⇝ ∘ ⊣ act

  A-·-l : ∀ {act lvl εₗ εₗ′ eᵣ act′}
    → (act , lvl) ⊢ εₗ ⇝ εₗ′ ⊣ act′
    → (act , lvl) ⊢ (εₗ ·ₗ eᵣ) ⇝ (εₗ′ ·ₗ eᵣ) ⊣ act′

  A-·-r : ∀ {act lvl eₗ εᵣ εᵣ′ act′}
    → (act , lvl) ⊢ εᵣ ⇝ εᵣ′ ⊣ act′
    → (act , lvl) ⊢ (eₗ ·ᵣ εᵣ) ⇝ (eₗ ·ᵣ εᵣ′) ⊣ act′

  A-+-l : ∀ {act lvl εₗ εₗ′ eᵣ act′}
    → (act , lvl) ⊢ εₗ ⇝ εₗ′ ⊣ act′
    → (act , lvl) ⊢ (εₗ +ₗ eᵣ) ⇝ (εₗ′ +ₗ eᵣ) ⊣ act′

  A-+-r : ∀ {act lvl eₗ εᵣ εᵣ′ act′}
    → (act , lvl) ⊢ εᵣ ⇝ εᵣ′ ⊣ act′
    → (act , lvl) ⊢ (eₗ +ᵣ εᵣ) ⇝ (eₗ +ᵣ εᵣ′) ⊣ act′

  A-Φ : ∀ {act lvl ε ε′ act′ pag}
    → (act , lvl) ⊢ ε ⇝ ε′ ⊣ act′
    → (act , lvl) ⊢ φ pag ⇒ ε ⇝ φ pag ⇒ ε′ ⊣ act′

  A-Δ-1-> : ∀ {act lvl ε ε′ act′ a l}
    → l > lvl
    → (a , l) ⊢ ε ⇝ ε′ ⊣ act′
    → (act , lvl) ⊢ δ (a , one , l) ⇒ ε ⇝ ε′ ⊣ act′

  A-Δ-1-≤ : ∀ {act lvl ε ε′ act′ a l}
    → l ≤ lvl
    → (act , lvl) ⊢ ε ⇝ ε′ ⊣ act′
    → (act , lvl) ⊢ δ (a , one , l) ⇒ ε ⇝ ε′ ⊣ act′

  A-Δ-∀-> : ∀ {act lvl ε ε′ act′ a l}
    → l > lvl
    → (a , l) ⊢ ε ⇝ ε′ ⊣ act′
    → (act , lvl) ⊢ δ (a , all , l) ⇒ ε ⇝ δ (a , all , l) ⇒ ε′ ⊣ act′

  A-Δ-∀-≤ : ∀ {act lvl ε ε′ act′ a l}
    → l ≤ lvl
    → (act , lvl) ⊢ ε ⇝ ε′ ⊣ act′
    → (act , lvl) ⊢ δ (a , all , l) ⇒ ε ⇝ δ (a , all , l) ⇒ ε′ ⊣ act′

data _⊢_⇝_⟨_⟩⊣_ : Pat × Act × Gas × ℕ → Exp → Ctx → Exp → Act → Set where
  T : ∀ {p a g l e eᵢ ε₀ ε₁ e₀ a₁}
    → (p , a , g , l) ⊢ e ⇝ eᵢ
    → eᵢ ⇒ ε₀ ⟨ e₀ ⟩
    → (a , l) ⊢ ε₀ ⇝ ε₁ ⊣ a₁
    → (p , a , g , l) ⊢ e ⇝ ε₁ ⟨ e₀ ⟩⊣ a₁

data _→*_ : Exp → Exp → Set where
  relf : ∀ {e}
    → e →* e

  Φ/Δ : ∀ {e e′ e₀ ε₁ a₁ eₜ e₁}
    → e →* e′
    → ($e , pause , one , 0) ⊢ e′ ⇝ ε₁ ⟨ e₀ ⟩⊣ a₁
    → Filter e₀
    → e₀ —→ eₜ
    → e₁ ⇐ ε₁ ⟨ eₜ ⟩
    → e →* e₁

  skip : ∀ {e e′ e₀ ε₁ e₁ eₜ}
    → e →* e′
    → ($e , pause , one , 0) ⊢ e′ ⇝ ε₁ ⟨ e₀ ⟩⊣ eval
    → e₀ —→ eₜ
    → e₁ ⇐ ε₁ ⟨ eₜ ⟩
    → e →* e₁

infix 0 _⇥_

data _⇥_ : Exp → Exp → Set where
  pause : ∀ {e e′ e₀ ε₁ e₁ eₜ}
    → e →* e′
    → ($e , pause , one , 0) ⊢ e′ ⇝ ε₁ ⟨ e₀ ⟩⊣ pause
    → e₀ —→ eₜ
    → e₁ ⇐ ε₁ ⟨ eₜ ⟩
    → e ⇥ e₁

infixr 7 _⇒_

data Typ : Set where
  _⇒_ : Typ → Typ → Typ
  `ℕ   : Typ

infixl 5 _,_∶_

data TypCtx : Set where
  ∅     : TypCtx
  _,_∶_ : TypCtx → Id → Typ → TypCtx

infix 4 _∋_∶_

data _∋_∶_ : TypCtx → Id → Typ → Set where
  Z : ∀ {Γ x τ}
    → Γ , x ∶ τ ∋ x ∶ τ

  S : ∀ {Γ x₁ x₂ τ₁ τ₂}
    → x₁ ≢ x₂
    → Γ ∋ x₁ ∶ τ₁
    → Γ , x₂ ∶ τ₂ ∋ x₁ ∶ τ₁

infix 4 _⊢_∶_
infix 5 _⊢_∻_

data _⊢_∶_ : TypCtx → Exp → Typ → Set
data _⊢_∻_ : TypCtx → Pat → Typ → Set

data _⊢_∶_ where
  ⊢-` : ∀ {Γ x τ}
    → Γ ∋ x ∶ τ
    → Γ ⊢ ` x ∶ τ

  ⊢-ƛ : ∀ {Γ x e τₓ τₑ}
    → Γ , x ∶ τₓ ⊢ e ∶ τₑ
    → Γ ⊢ (ƛ x ⇒ e) ∶ (τₓ ⇒ τₑ)

  ⊢-· : ∀ {Γ e₁ e₂ τ₁ τ₂}
    → Γ ⊢ e₁ ∶ (τ₂ ⇒ τ₁)
    → Γ ⊢ e₂ ∶ τ₂
    → Γ ⊢ (e₁ `· e₂) ∶ τ₁

  ⊢-# : ∀ {Γ n}
    → Γ ⊢ (# n) ∶ `ℕ

  ⊢-φ : ∀ {Γ p ag e τₑ}
    → Γ ⊢ e ∶ τₑ
    → Γ ⊢ φ (p , ag) ⇒ e ∶ τₑ

  ⊢-δ : ∀ {Γ agl e τ}
    → Γ ⊢ e ∶ τ
    → Γ ⊢ δ agl ⇒ e ∶ τ

data _⊢_∻_ where
  ⊢-e : ∀ {Γ τ}
    → Γ ⊢ $e ∻ τ

  ⊢-v : ∀ {Γ τ}
    → Γ ⊢ $v ∻ τ

  ⊢-` : ∀ {Γ x τ}
    → Γ ∋ x ∶ τ
    → Γ ⊢ ` x ∻ τ

  ⊢-ƛ : ∀ {Γ x e τₓ τₑ}
    → Γ , x ∶ τₓ ⊢ e ∶ τₑ
    → Γ ⊢ ƛ x ⇒ e ∻ (τₓ ⇒ τₑ)

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

-- match-types : ∀ {Γ p e τₚ τₑ} → p ⊳ e → (Γ ⊢ p ∻ τₚ)
-- match-types (M-Δ PM) = (match-types PM)
-- match-types (M-Φ PM) = (match-types PM)
-- match-types M-E = ⊢-e
-- match-types (M-V x) = ⊢-v
-- match-types (M-· (M-Δ PMₗ) PMᵣ) = ⊢-· (match-types {!!}) {!!}
-- match-types (M-· (M-Φ PMₗ) PMᵣ) = ⊢-· {!!} {!!}
-- match-types (M-· M-E PMᵣ) = ⊢-· ⊢-e (match-types PMᵣ)
-- match-types (M-· (M-V x) PMᵣ) = ⊢-· ⊢-v {!!}
-- match-types (M-· (M-· PMₗ PMₗ₁) PMᵣ) = ⊢-· {!!} {!!}
-- match-types (M-· (M-+ PMₗ PMₗ₁) PMᵣ) = ⊢-· {!!} {!!}
-- match-types (M-· (M-ƛ x x₁) PMᵣ) = ⊢-· {!!} {!!}
-- match-types (M-· (M-$ x) PMᵣ) = ⊢-· {!!} {!!}
-- match-types (M-+ PMₗ PMᵣ) = {!!}
-- match-types (M-ƛ x x₁) = {!!}
-- match-types (M-$ x) = {!!}
