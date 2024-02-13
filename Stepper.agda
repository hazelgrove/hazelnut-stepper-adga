open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; _+_; _>_; _≤_)
open import Data.Product using (_,_; _×_)
open import Data.List using (List; _∷_; [])
open import Relation.Nullary using (Dec; yes; no; ¬_; _×-dec_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; [_])
open Eq.≡-Reasoning

Id : Set
Id = String

Filter : Set

data Pat : Set
data Act : Set
data Gas : Set

infix  5 ƛ_⇒_
infix  5 μ_⇒_
infix  5 φ_⟨_⟩
infix  5 δ_⟨_⟩
infixl 7 _·_
infixl 7 _`+_
infix  9 #_
infix  9 `_

data Term : Set where
  `_    : Id → Term
  ƛ_⇒_ : Id → Term → Term
  _·_   : Term → Term → Term
  #_    : ℕ → Term
  _`+_  : Term → Term → Term
  φ_⟨_⟩ : Pat × Act × Gas → Term → Term
  δ_⟨_⟩ : Act × Gas × ℕ   → Term → Term

data Value : Term → Set where
  V-ƛ : ∀ {x N}
    → Value (ƛ x ⇒ N)

  V-# : ∀ {n}
    → Value (# n)

Value? : ∀ (L : Term) → Dec (Value L)
Value? (` x) = no λ ()
Value? (ƛ x ⇒ L) = yes V-ƛ
Value? (L · M) = no λ ()
Value? (φ pag ⟨ L ⟩) = no λ ()
Value? (δ ag ⟨ L ⟩) = no λ ()
Value? (# n) = yes V-#
Value? (L `+ M) = no λ ()

data Pat where
  `_  : Id → Pat
  `e    : Pat
  `v    : Pat
  ƛ_⇒_ : Id → Term → Pat
  _·_   : Pat → Pat → Pat
  #_    : ℕ → Pat
  _`+_  : Pat → Pat → Pat

infix 1 _matches_

data _matches_ : Pat → Term → Set where
  PM-e : ∀ {L}
    → `e matches L

  PM-v : ∀ {V}
    → Value V
    → `v matches V

  PM-· : ∀ {p₁ p₂ e₁ e₂}
    → p₁ matches e₁
    → p₂ matches e₂
    → p₁ · p₂ matches e₁ · e₂

  PM-# : ∀ {n}
    → # n matches # n

  PM-+ : ∀ {p₁ p₂ e₁ e₂}
    → p₁ matches e₁
    → p₂ matches e₂
    → p₁ `+ p₂ matches e₁ `+ e₂

_matches?_ : ∀ (P : Pat) (L : Term) → Dec (P matches L)
(` _) matches? _ = no λ ()
`e matches? L = yes PM-e
`v matches? L with Value? L
... | yes ValueL = yes (PM-v ValueL)
... | no  ¬ValueL = no λ { (PM-v ValueL) → ¬ValueL ValueL }

(ƛ _ ⇒ _) matches? _ = no λ ()

(Pₗ · Pᵣ) matches? (Lₗ · Lᵣ) with (Pₗ matches? Lₗ) ×-dec (Pᵣ matches? Lᵣ)
... | yes (PLₗ , PLᵣ) = yes (PM-· PLₗ PLᵣ)
... | no  ¬PLₗᵣ = no λ { (PM-· PLₗ PLᵣ) → ¬PLₗᵣ (PLₗ , PLᵣ) }
(_ · _) matches? (` _) = no λ ()
(_ · _) matches? (ƛ _ ⇒ _) = no λ ()
(_ · _) matches? (# _) = no λ ()
(_ · _) matches? (_ `+ _) = no λ ()
(_ · _) matches? (φ _ ⟨ L ⟩) = no λ ()
(_ · _) matches? (δ _ ⟨ _ ⟩) = no λ ()

(# P) matches? (# L) with P Data.Nat.≟ L
... | yes refl = yes PM-#
... | no  P≢P  = no λ { PM-# → P≢P refl }
(# _) matches? (` _) = no λ ()
(# _) matches? (ƛ _ ⇒ _) = no λ ()
(# _) matches? (_ · _) = no λ ()
(# _) matches? (_ `+ _) = no λ ()
(# _) matches? (φ _ ⟨ _ ⟩) = no λ ()
(# _) matches? (δ _ ⟨ _ ⟩) = no λ ()

(Pₗ `+ Pᵣ) matches? (Lₗ `+ Lᵣ) with (Pₗ matches? Lₗ) ×-dec (Pᵣ matches? Lᵣ)
... | yes (PLₗ , PLᵣ) = yes (PM-+ PLₗ PLᵣ)
... | no  ¬PLₗᵣ       = no λ { (PM-+ PLₗ PLᵣ) → ¬PLₗᵣ (PLₗ , PLᵣ) }
(_ `+ _) matches? (` _) = no λ ()
(_ `+ _) matches? (ƛ _ ⇒ _) = no λ ()
(_ `+ _) matches? (_ · _) = no λ ()
(_ `+ _) matches? (# _) = no λ ()
(_ `+ _) matches? (φ _ ⟨ _ ⟩) = no λ ()
(_ `+ _) matches? (δ _ ⟨ _ ⟩) = no λ ()

_ : (`v `+ `v matches # 1 `+ # 2)
_ = PM-+ (PM-v V-#) (PM-v V-#)

_ : (`e `+ `e matches ((ƛ "x" ⇒ ` "x") · # 3) `+ (# 1 `+ # 2))
_ = PM-+ PM-e PM-e

data Act where
  stop : Act
  skip : Act

data Gas where
  one : Gas
  all : Gas

Filter = Pat × Act × Gas

infix 9 _[_:=_]
infix 9 _[_:=_]ᶠ

patternize : Term → Pat
patternize (` x) = ` x
patternize (ƛ x ⇒ N) = ƛ x ⇒ N
patternize (L · M) = patternize L · patternize M
patternize (# n) = # n
patternize (L `+ M) = patternize L `+ patternize M
patternize (φ F ⟨ L ⟩) = patternize L
patternize (δ AG ⟨ L ⟩) = patternize L

_[_:=_]ᶠ : Pat → Id → Term → Pat
_[_:=_]  : Term → Id → Term → Term

(` x) [ y := V ]ᶠ with x ≟ y
... | yes _ = patternize V
... | no  _ = ` x
`e [ y := V ]ᶠ = `e
`v [ y := V ]ᶠ = `v
(ƛ x ⇒ N) [ y := V ]ᶠ = ƛ x ⇒ (N [ y := V ])
(Pₗ · Pᵣ) [ y := V ]ᶠ = Pₗ [ y := V ]ᶠ · Pᵣ [ y := V ]ᶠ
(# n) [ y := V ]ᶠ = # n
(Pₗ `+ Pᵣ) [ y := V ]ᶠ = Pₗ [ y := V ]ᶠ `+ Pᵣ [ y := V ]ᶠ

(` x) [ y := V ] with x ≟ y
... | yes _ = V
... | no  _ = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _         = ƛ x ⇒ N
... | no  _         = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]  = L [ y := V ] · M [ y := V ]
(# n) [ y := V ] = # n
(L `+ M) [ y := V ] = L [ y := V ] `+ M [ y := V ]
(φ (F , A,G) ⟨ N ⟩) [ y := V ] = φ (F [ y := V ]ᶠ , A,G) ⟨ (N [ y := V ]) ⟩
(δ A,G ⟨ N ⟩) [ y := V ] = δ A,G ⟨ (N [ y := V ]) ⟩

strip : Term → Term
strip (` x) = ` x
strip (ƛ x ⇒ L) = ƛ x ⇒ L
strip (L · M) = strip L · strip M
strip (# x) = # x
strip (L `+ M) = strip L `+ strip M
strip (φ x ⟨ L ⟩) = strip L
strip (δ x ⟨ L ⟩) = strip L

-- instr₀ : Filter → Term → Term
-- instr₀ (F , A,G) L with F matches? (strip L)
-- ... | no  _ = L
-- ... | yes _ with Value? (strip L)
-- ... | yes _ = L
-- ... | no  _ = δ A,G ⟨ L ⟩

-- instr : Filter → Term → Term
-- instr F (` x) = (` x)
-- instr F (ƛ x ⇒ L) = (ƛ x ⇒ L)
-- instr F (L · M) = instr₀ F ((instr F L) · (instr F M))
-- instr F (# x) = (# x)
-- instr F (L `+ M) = instr₀ F ((instr F L) `+ (instr F M))
-- instr F (Φ F' ⇐ L) = instr F' (instr F L)
-- instr F (φ x ← L) = instr F L

data Eval-Context : Set where
  ∘    : Eval-Context
  _·ₗ_ : Eval-Context → Term → Eval-Context
  _·ᵣ_ : Term → Eval-Context → Eval-Context
  _+ₗ_ : Eval-Context → Term → Eval-Context
  _+ᵣ_ : Term → Eval-Context → Eval-Context
  φ_⟨_⟩ : Filter → Eval-Context → Eval-Context
  δ_⟨_⟩ : Act × Gas × ℕ → Eval-Context → Eval-Context

infix 2 _⟨_⟩

data Object : Set where
  _⟨_⟩ : Eval-Context → Term → Object

infix 1 _＝_

data _＝_ : Term → Object → Set where
  DC-∘ : ∀ {e}
    → e ＝ ∘ ⟨ e ⟩

  DC-·ₗ : ∀ {e₁ e₂ ε e₁′}
    → e₁ ＝ ε ⟨ e₁′ ⟩
    → e₁ · e₂ ＝ (ε ·ₗ e₂) ⟨ e₁′ ⟩

  DC-·ᵣ : ∀ {e₁ e₂ ε e₂′}
    → e₂ ＝ ε ⟨ e₂′ ⟩
    → e₁ · e₂ ＝ (e₁ ·ᵣ ε) ⟨ e₂′ ⟩

  DC-φ : ∀ {a g l e ε e′}
    → e ＝ ε ⟨ e′ ⟩
    → (δ (a , g , l) ⟨ e ⟩) ＝ (δ (a , g , l) ⟨ ε ⟩) ⟨ e′ ⟩

  DC-+ₗ : ∀ {e₁ e₂ ε e₁′}
    → e₁ ＝ ε ⟨ e₁′ ⟩
    → e₁ `+ e₂ ＝ (ε +ₗ e₂) ⟨ e₁′ ⟩

  DC-+ᵣ : ∀ {e₁ e₂ ε e₂′}
    → e₂ ＝ ε ⟨ e₂′ ⟩
    → e₁ `+ e₂ ＝ (e₁ +ᵣ ε) ⟨ e₂′ ⟩

infix 1 _⊢_＝_⊣_

data _⊢_＝_⊣_ : Act × Gas × ℕ → Term → Object → Act × Gas → Set where
  FC-∘ : ∀ {a g l e} → (a , g , l) ⊢ e ＝ ∘ ⟨ e ⟩ ⊣ (a , g)

  FC-·ₗ : ∀ {a g e₁ e₂ e₁′ ε a′ g′}
    → (a , g) ⊢ e₁ ＝ ε ⟨ e₁′ ⟩ ⊣ (a′ , g′)
    → (a , g) ⊢ (e₁ · e₂) ＝ (ε ·ₗ e₂) ⟨ e₁′ ⟩ ⊣ (a′ , g′)

  FC-·ᵣ : ∀ {a g e₁ e₂ e₂′ ε a′ g′}
    → Value e₁
    → (a , g) ⊢ e₂ ＝ ε ⟨ e₂′ ⟩ ⊣ (a′ , g′)
    → (a , g) ⊢ (e₁ · e₂) ＝ (e₁ ·ᵣ ε) ⟨ e₂′ ⟩ ⊣ (a′ , g′)

  FC-+ₗ : ∀ {a g e₁ e₂ e₁′ ε a′ g′}
    → (a , g) ⊢ e₁ ＝ ε ⟨ e₁′ ⟩ ⊣ (a′ , g′)
    → (a , g) ⊢ (e₁ `+ e₂) ＝ (ε +ₗ e₂) ⟨ e₁′ ⟩ ⊣ (a′ , g′)

  FC-+ᵣ : ∀ {a g e₁ e₂ e₂′ ε a′ g′}
    → (a , g) ⊢ e₂ ＝ ε ⟨ e₂′ ⟩ ⊣ (a′ , g′)
    → (a , g) ⊢ (e₁ `+ e₂) ＝ (e₁ +ᵣ ε) ⟨ e₂′ ⟩ ⊣ (a′ , g′)

  FC-Φ : ∀ {a g f e ε e′ a′ g′}
    → (a , g) ⊢ e ＝ ε ⟨ e′ ⟩ ⊣ (a′ , g′)
    → (a , g) ⊢ (φ f ⟨ e ⟩) ＝ (φ f ⟨ ε ⟩) ⟨ e′ ⟩ ⊣ (a′ , g′)

  FC-Δ₁-> : ∀ {a₀ g₀ l₀ a l e ε e′ a′ g′}
    → l > l₀
    → (a , one , l) ⊢ e ＝ ε ⟨ e′ ⟩ ⊣ (a′ , g′)
    → (a₀ , g₀ , l₀) ⊢ (δ (a , one , l) ⟨ e ⟩) ＝ ε ⟨ e′ ⟩ ⊣ (a′ , g′)

  FC-Δ₁-≤ : ∀ {a₀ g₀ l₀ a l e ε e′ a′ g′}
    → l ≤ l₀
    → (a₀ , one , l₀) ⊢ e ＝ ε ⟨ e′ ⟩ ⊣ (a′ , g′)
    → (a₀ , g₀ , l₀) ⊢ (δ (a , one , l) ⟨ e ⟩) ＝ ε ⟨ e′ ⟩ ⊣ (a′ , g′)

  FC-Δₙ-> : ∀ {a₀ g₀ l₀ a l e ε e′ a′ g′}
    → l > l₀
    → (a , all , l) ⊢ e ＝ ε ⟨ e′ ⟩ ⊣ (a′ , g′)
    → (a₀ , g₀ , l₀) ⊢ (δ (a , all , l) ⟨ e ⟩) ＝ (δ (a , all , l) ⟨ ε ⟩) ⟨ e′ ⟩ ⊣ (a′ , g′)

  FC-Δₙ-≤ : ∀ {a₀ g₀ l₀ a l e ε e′ a′ g′}
    → l ≤ l₀
    → (a₀ , all , l₀) ⊢ e ＝ ε ⟨ e′ ⟩ ⊣ (a′ , g′)
    → (a₀ , g₀ , l₀) ⊢ (δ (a , all , l) ⟨ e ⟩) ＝ ε ⟨ e′ ⟩ ⊣ (a′ , g′)

-- data _⊢_＝_⇝_⊣_ : Act × Gas → Term → Object → Object → Act × Gas → Set where
--   FC-∘ : ∀ {a g e} → (a , g) ⊢ e ＝ ∘ ⟨ e ⟩ ⇝ φ (a , g) ← ∘ ⟨ e ⟩ ⊣ (a , g)

--   FC-·ₗ : ∀ {a g e₁ e₂ e₁′ ε ε′ a′ g′}
--     → (a , g) ⊢ e₁ ＝ ε ⟨ e₁′ ⟩ ⇝ ε′ ⟨ e₁′ ⟩ ⊣ (a′ , g′)
--     → (a , g) ⊢ (e₁ · e₂) ＝ (ε ·ₗ e₂) ⟨ e₁′ ⟩ ⇝ (ε′ ·ₗ e₂) ⟨ e₁′ ⟩ ⊣ (a′ , g′)

--   FC-·ᵣ : ∀ {a g e₁ e₂ e₂′ ε a′ g′}
--     → Value e₁
--     → (a , g) ⊢ e₂ ＝ ε ⟨ e₂′ ⟩ (a′ , g′)
--     → (a , g) ⊢ (e₁ · e₂) ＝ (e₁ ·ᵣ ε) ⟨ e₂′ ⟩ (a′ , g′)

--   FC-+ₗ : ∀ {a g e₁ e₂ e₁′ ε a′ g′}
--     → (a , g) ⊢ e₁ ＝ ε ⟨ e₁′ ⟩ (a′ , g′)
--     → (a , g) ⊢ (e₁ `+ e₂) ＝ (ε +ₗ e₂) ⟨ e₁′ ⟩ (a′ , g′)

--   FC-+ᵣ : ∀ {a g e₁ e₂ e₂′ ε a′ g′}
--     → (a , g) ⊢ e₁ ＝ ε ⟨ e₂′ ⟩ (a′ , g′)
--     → (a , g) ⊢ (e₁ `+ e₂) ＝ (e₁ +ᵣ ε) ⟨ e₂′ ⟩ (a′ , g′)

--   FC-Φ : ∀ {a g f e ε e′ a′ g′}
--     → (a , g) ⊢ e ＝ ε ⟨ e′ ⟩ (a′ , g′)
--     → (a , g) ⊢ (Φ f ⇐ e) ＝ (Φ f ⇐ ε) ⟨ e′ ⟩ (a′ , g′)

--   FC-φ-one : ∀ {a₀ g₀ a e ε e′ a′ g′}
--     → (a , one) ⊢ e ＝ ε ⟨ e′ ⟩ (a′ , g′)
--     → (a₀ , g₀) ⊢ (φ (a , one) ← e) ＝ ε ⟨ e′ ⟩ (a′ , g′)

--   FC-φ-all : ∀ {a₀ g₀ a e ε e′ a′ g′}
--     → (a , all) ⊢ e ＝ ε ⟨ e′ ⟩ (a′ , g′)
--     → (a₀ , g₀) ⊢ (φ (a , all) ← e) ＝ (φ (a , all) ← ε) ⟨ e′ ⟩ (a′ , g′)


infix 4 _—→_

data _—→_ : Term → Term → Set where
  ξ-·ₗ : ∀ {L L′ M}
    → L —→ L′
    → L · M —→ L′ · M

  ξ-·ᵣ : ∀ {V M M′}
    → Value V
    → M —→ M′
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-Φ : ∀ {F L L′}
    → L —→ L′
    → φ F ⟨ L ⟩ —→ φ F ⟨ L′ ⟩

  β-Φ : ∀ {F V}
    → Value V
    → φ F ⟨ V ⟩ —→ V

  ξ-φ : ∀ {A,G L L′}
    → L —→ L′
    → (δ A,G ⟨ L ⟩) —→ L′

  β-φ : ∀ {A,G V}
    → Value V
    → (δ A,G ⟨ V ⟩) —→ V

  β-+ : ∀ {n₁ n₂}
    → (# n₁) `+ (# n₂) —→ # (n₁ + n₂)

data _⊢_⇝_ : Pat × Act × Gas × ℕ → Term → Term → Set where
  FI-V : ∀ {p a g l v}
    → Value v
    → (p , a , g , l) ⊢ v ⇝ v

  FI-`-⊤ : ∀ {p a g l x e}
    → ` x —→ e
    → p matches (` x)
    → (p , a , g , l) ⊢ (` x) ⇝ (δ (a , g , l) ⟨ ` x ⟩)

  FI-`-⊥ : ∀ {p a g x e}
    → ` x —→ e
    → ¬ (p matches (` x))
    → (p , a , g) ⊢ (` x) ⇝ (` x)

  FI-Φ : ∀ {p₀ a₀ g₀ l₀ p a g e e′ e″ eₜ}
    → e —→ eₜ
    → (p₀ , a₀ , g₀ , l₀) ⊢ e ⇝ e′
    → (p , a , g , (l₀ + 1)) ⊢ e′ ⇝ e″
    → (p₀ , a₀ , g₀ , l₀) ⊢ φ (p , a , g) ⟨ e ⟩ ⇝ φ (p , a , g) ⟨ e″ ⟩

  FI-Δ : ∀ {p₀ a₀ g₀ a g e eₜ e′}
    → e —→ eₜ
    → (p₀ , a₀ , g₀) ⊢ e ⇝ e′
    → (p₀ , a₀ , g₀) ⊢ δ (a , g) ⟨ e ⟩ ⇝ (δ (a , g) ⟨ e′ ⟩)

  FI-·-⊤ : ∀ {p a g eₗ eᵣ eₗ′ eᵣ′}
    → p matches (eₗ · eᵣ)
    → (p , a , g) ⊢ eₗ ⇝ eₗ′
    → (p , a , g) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g) ⊢ (eₗ · eᵣ) ⇝ δ (a , g) ⟨ (eₗ′ · eᵣ′) ⟩

  FI-·-⊥ : ∀ {p a g eₗ eᵣ eₗ′ eᵣ′}
    → ¬ (p matches (eₗ · eᵣ))
    → (p , a , g) ⊢ eₗ ⇝ eₗ′
    → (p , a , g) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g) ⊢ (eₗ · eᵣ) ⇝ (eₗ′ · eᵣ′)

  FI-+-⊤ : ∀ {p a g eₗ eᵣ eₗ′ eᵣ′}
    → p matches (eₗ `+ eᵣ)
    → (p , a , g) ⊢ eₗ ⇝ eₗ′
    → (p , a , g) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g) ⊢ (eₗ `+ eᵣ) ⇝ δ (a , g) ⟨ (eₗ′ `+ eᵣ′) ⟩

  FI-+-⊥ : ∀ {p a g eₗ eᵣ eₗ′ eᵣ′}
    → ¬ (p matches (eₗ `+ eᵣ))
    → (p , a , g) ⊢ eₗ ⇝ eₗ′
    → (p , a , g) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g) ⊢ (eₗ `+ eᵣ) ⇝ (eₗ′ `+ eᵣ′)

data _⊢_→*_ : Filter → Term → Term → Set where
  refl : ∀ {p a g e}
    → (p , a , g) ⊢ e →* e
    
  skip : ∀ {p a g e eᵢ e₀ e₀′ ε e′ e″ g₀}
    → (p , a , g , 0) ⊢ e ⇝ eᵢ
    → (a , g , 0) ⊢ eᵢ ＝ ε ⟨ e₀ ⟩ ⊣ (skip , g₀)
    → e₀ —→ e₀′
    → e′ ＝ ε ⟨ e₀′ ⟩
    → (p , a , g) ⊢ e′ →* e″
    → (p , a , g) ⊢ e →* e″

-- _ : (`e , skip , all) ⊢ ((# 1) `+ (# 2) `+ (# 3) `+ (# 4)) →* (# 10)
-- _ = skip (FI-+-⊤ PM-e (FI-+-⊤ PM-e (FI-+-⊤ PM-e (FI-V V-#) (FI-V V-#)) (FI-V V-#)) (FI-V V-#)) (FC-δ-all (FC-+ₗ (FC-δ-all (FC-+ₗ (FC-δ-all FC-∘))))) β-+ {!DC-!} {!!}
--     skip (FI-+ (FI-+ (FI-E FI-refl PM-e) FI-refl) FI-refl) (FC-+ₗ (FC-+ₗ (FC-φ-all FC-∘))) β-+ (DC-+ₗ (DC-+ₗ (DC-φ DC-∘)))
--     (skip (FI-+ (FI-E FI-refl PM-e) FI-refl) (FC-+ₗ (FC-φ-all FC-∘)) β-+ (DC-+ₗ (DC-φ DC-∘))
--     (skip (FI-E FI-refl PM-e) (FC-φ-all FC-∘) β-+ (DC-φ DC-∘) refl))

-- _ : (`e , skip , all) ⊢ φ (# 1 `+ # 2 , stop , one) ⇒ (# 1 `+ # 2) `+ (# 3 `+ # 4) →* ((# 1 `+ # 2) `+ # 7)
-- _ =
--   skip
--   (FI-+ (FI-E (FI-I (FI-E FI-refl PM-e) (FI-φ (FI-E FI-refl (PM-+ PM-# PM-#)))) PM-e) (FI-E FI-refl PM-e))
--   (FC-+ᵣ (FC-φ-all FC-∘)) β-+ (DC-+ᵣ (DC-φ DC-∘))
--   refl

data _⊢_↦_ : Filter → Term → Term → Set where
  step : ∀ {p a g e eᵢ e₀ e₀′ ε e′ e″ g₀}
    → (p , a , g) ⊢ e′ →* e″
    → (p , a , g , 0) ⊢ e ⇝ eᵢ
    → (a , g , 0) ⊢ eᵢ ＝ ε ⟨ e₀ ⟩ ⊣ (stop , g₀)
    → e₀ —→ e₀′
    → e′ ＝ ε ⟨ e₀′ ⟩
    → (p , a , g) ⊢ e ↦ e″

data Type : Set where
  _⇒_ : Type → Type → Type

data Context : Set where
  ∅ : Context
  _,_∶_ : Context → Id → Type → Context

