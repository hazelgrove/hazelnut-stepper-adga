open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; _+_; _≤_; _>_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
import Data.Irrelevant
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; _≢_)
open import Function using (_↔_)

data Act : Set where
  eval : Act
  pause : Act

data Gas : Set where
  one : Gas
  all : Gas

Id : Set
Id = String

data Pat : Set
data Exp : Set

infix 5 ƛ_⇒_
infix 5 ƛ$x⇒_
infix 5 φ_⇒_
infix 5 δ_⇒_
infixl 7 _`+_
infixl 8 _`·_
infix 9 #_
infix 9 `_

data Pat where
  $e     : Pat
  $v     : Pat
  `_     : Id → Pat
  ƛ_⇒_  : Id → Exp → Pat
  ƛ$x⇒_ : Exp → Pat
  _`·_   : Pat → Pat → Pat
  #_     : ℕ → Pat
  _`+_   : Pat → Pat → Pat

data Exp where
  `_     : Id → Exp
  ƛ_⇒_  : Id → Exp → Exp
  _`·_   : Exp → Exp → Exp
  #_     : ℕ → Exp
  _`+_   : Exp → Exp → Exp
  φ_⇒_  : Pat × Act × Gas → Exp → Exp
  δ_⇒_  : Act × Gas × ℕ   → Exp → Exp

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

  PV-$ : ∀ {e}
    → PatVal (ƛ$x⇒ e)

strip : Exp → Exp
strip (` x) = ` x
strip (ƛ x ⇒ L) = ƛ x ⇒ (strip L)
strip (L `· M) = (strip L) `· (strip M)
strip (# n) = # n
strip (L `+ M) = (strip L) `+ (strip M)
strip (φ x ⇒ L) = strip L
strip (δ x ⇒ L) = strip L

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
_⟨_:=_⟩ (` x) y V with (x ≟ y)
... | yes _ = patternize V
... | no  _ = (` x)
_⟨_:=_⟩ (ƛ x ⇒ L) y V with (x ≟ y)
... | yes _ = (ƛ x ⇒ L)
... | no  _ = (ƛ x ⇒ (L [ y := V ]))
_⟨_:=_⟩ (ƛ$x⇒ L) x V = ƛ$x⇒ (L [ x := V ])
_⟨_:=_⟩ (L `· M) x V = (L ⟨ x := V ⟩) `· (M ⟨ x := V ⟩)
_⟨_:=_⟩ (# n) x V = # n
_⟨_:=_⟩ (L `+ M) x V = (L ⟨ x := V ⟩) `+ (M ⟨ x := V ⟩)

_[_:=_] (` x) y V with (x ≟ y)
... | yes _ = V
... | no  _ = (` x)
_[_:=_] (ƛ x ⇒ L) y V with (x ≟ y)
... | yes _ = (ƛ x ⇒ L)
... | no  _ = (ƛ x ⇒ (L [ y := V ]))
_[_:=_] (L `· M) x V = (L [ x := V ]) `· (M [ x := V ])
_[_:=_] (# n) x V = # n
_[_:=_] (L `+ M) x V = (L [ x := V ]) `+ (M [ x := V ])
_[_:=_] (φ (p , a , g) ⇒ L) y V = φ (p ⟨ y := V ⟩) , a , g ⇒ L [ y := V ]
_[_:=_] (δ x ⇒ L) y V = δ x ⇒ L [ y := V ]

infix 4 _⊳_

data _⊳_ : Pat → Exp → Set where
  M-Δ : ∀ {p agl e}
    → p ⊳ e
    → p ⊳ (δ agl ⇒ e)

  M-Φ : ∀ {p pag e}
    → p ⊳ e
    → p ⊳ (φ pag ⇒ e)

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

  M-ƛ : ∀ {xₚ eₚ xₑ eₑ}
    → xₚ ≡ xₑ
    → strip eₚ ≡ strip eₑ
    → (ƛ xₚ ⇒ eₚ) ⊳ (ƛ xₑ ⇒ eₑ)

  M-$ : ∀ {eₚ xₑ eₑ}
    → eₚ ≡ eₑ
    → (ƛ$x⇒ eₚ) ⊳ (ƛ xₑ ⇒ eₑ)

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

  ⊢-φ : ∀ {Γ p τₚ ag e τₑ}
    → Γ ⊢ p ∻ τₚ
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

  ⊢-$ : ∀ {Γ τₓ e τₑ}
    → Γ ⊢ e ∶ τₑ
    → Γ ⊢ ƛ$x⇒ e ∻ (τₓ ⇒ τₑ)

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

match-is-well-typed : ∀ {Γ p e τₚ τₑ} → p ⊳ e → (Γ ⊢ p ∻ τₚ) × (Γ ⊢ e ∶ τₑ)
match-is-well-typed (M-Δ PM) = proj₁ (match-is-well-typed PM) , ⊢-δ (proj₂ (match-is-well-typed PM))
match-is-well-typed (M-Φ PM) = proj₁ (match-is-well-typed PM) , ⊢-φ {!!} {!!}
match-is-well-typed M-E = {!!} , {!!}
match-is-well-typed (M-V x) = {!!} , {!!}
match-is-well-typed (M-· PM PM₁) = {!!} , {!!}
match-is-well-typed (M-+ PM PM₁) = {!!} , {!!}
match-is-well-typed (M-ƛ x x₁) = {!!} , {!!}
match-is-well-typed (M-$ x) = {!!} , {!!}
