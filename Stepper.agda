open import Data.String using (String)
open import Data.Nat using (ℕ; _+_; _≤_; _>_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_; _×-dec_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; _≢_)
open import Function using (_↔_)

data Act : Set where
  eval : Act
  pause : Act

data Gas : Set where
  𝟙 : Gas
  ⋆ : Gas

Id : Set
Id = ℕ

data Pat : Set
data Exp : Set

infix 5 ƛ_⇒_
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

data Exp where
  `_    : Id → Exp
  ƛ_    : Exp → Exp
  _`·_  : Exp → Exp → Exp
  #_    : ℕ → Exp
  _`+_  : Exp → Exp → Exp
  φ_⇒_ : Pat × Act × Gas → Exp → Exp
  δ_⇒_ : Act × Gas × ℕ   → Exp → Exp

data Value : Exp → Set where
  V-# : ∀ {n : ℕ}
    → Value (# n)

  V-ƛ : ∀ {x e}
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
  N-ƛ : ∀ {x e} → Normal e → Normal (ƛ e)
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

  PV-ƛ : ∀ {x e}
    → PatVal (ƛ e)

strip : Exp → Exp
strip (` x) = ` x
strip (ƛ L) = ƛ (strip L)
strip (L `· M) = (strip L) `· (strip M)
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

_[_:=_] : Exp → ℕ → Exp → Exp
_⟨_:=_⟩ : Pat → ℕ → Exp → Pat

$e ⟨ _ := _ ⟩ = $e
$v ⟨ _ := _ ⟩ = $v
(` x) ⟨ y := v ⟩ with (x Data.Nat.≟ y)
... | yes refl = patternize v
... | no ¬x≡y = (` x)
(ƛ x) ⟨ y := v ⟩ = ƛ (x [ (ℕ.suc y) := v ])
(p₁ `· p₂) ⟨ x := v ⟩ = (p₁ ⟨ x := v ⟩) `· (p₂ ⟨ x := v ⟩)
(# n) ⟨ _ := _ ⟩ = # n
(p₁ `+ p₂) ⟨ x := v ⟩ = (p₁ ⟨ x := v ⟩) `+ (p₂ ⟨ x := v ⟩)

(` x) [ y := v ] with (x Data.Nat.≟ y)
... | yes refl = v
... | no ¬x≡y  = (` x)
(ƛ e) [ x := v ] = ƛ (e [ (ℕ.suc x) := v ])
(e₁ `· e₂) [ x := v ] = (e₁ [ x := v ]) `· (e₂ [ x := v ])
(# n) [ x := v ] = # n
(e₁ `+ e₂) [ x := v ] = (e₁ [ x := v ]) `+ (e₂ [ x := v ])
(φ pag ⇒ e) [ x := v ] = φ pag ⇒ e [ x := v ]
(δ agl ⇒ e) [ x := v ] = δ agl ⇒ e [ x := v ]

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

  M-ƛ : ∀ {eₚ eₑ}
    → (strip eₚ) ≡ (strip eₑ)
    → (ƛ eₚ) ⊳ (ƛ eₑ)

  M-# : ∀ {n}
    → (# n) ⊳ (# n)

infix 0 _—→_

data _—→_ : Exp → Exp → Set where
  -- ξ-·ₗ : ∀ {eₗ eᵣ eₗ′}
  --   → eₗ —→ eₗ′
  --   → eₗ `· eᵣ —→ eₗ′ `· eᵣ

  -- ξ-·ᵣ : ∀ {eᵣ vₗ eᵣ′}
  --   → Value vₗ
  --   → eᵣ —→ eᵣ′
  --   → vₗ `· eᵣ —→ vₗ `· eᵣ′

  β-· : ∀ {vᵣ x eₓ}
    → Value vᵣ
    → (ƛ eₓ) `· vᵣ —→ (eₓ [ x := vᵣ ])

  -- ξ-+ₗ : ∀ {eₗ eᵣ eₗ′}
  --   → eₗ —→ eₗ′
  --   → eₗ `+ eᵣ —→ eₗ′ `+ eᵣ

  -- ξ-+ᵣ : ∀ {eᵣ vₗ eᵣ′}
  --   → Value vₗ
  --   → eᵣ —→ eᵣ′
  --   → vₗ `+ eᵣ —→ vₗ `+ eᵣ′

  β-+ : ∀ {vᵣ x eₓ}
    → Value vᵣ
    → (ƛ eₓ) `+ vᵣ —→ (eₓ [ x := vᵣ ])

  -- ξ-φ : ∀ {pag e e′}
  --   → e —→ e′
  --   → (φ pag ⇒ e) —→ (φ pag ⇒ e′)

  β-φ : ∀ {pag v}
    → Value v
    → (φ pag ⇒ v) —→ v

  -- ξ-δ : ∀ {agl e e′}
  --   → e —→ e′
  --   → (δ agl ⇒ e) —→ (δ agl ⇒ e′)

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

  D-ξ-·ᵣ : ∀ {vₗ eᵣ ℰ eᵣ′}
    → Value vₗ
    → eᵣ ⇒ ℰ ⟨ eᵣ′ ⟩
    → (vₗ `· eᵣ) ⇒ (vₗ ·ᵣ ℰ) ⟨ eᵣ′ ⟩

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
    → (act , lvl) ⊢ δ (a , 𝟙 , l) ⇒ ε ⇝ ε′ ⊣ act′

  A-Δ-1-≤ : ∀ {act lvl ε ε′ act′ a l}
    → l ≤ lvl
    → (act , lvl) ⊢ ε ⇝ ε′ ⊣ act′
    → (act , lvl) ⊢ δ (a , 𝟙 , l) ⇒ ε ⇝ ε′ ⊣ act′

  A-Δ-∀-> : ∀ {act lvl ε ε′ act′ a l}
    → l > lvl
    → (a , l) ⊢ ε ⇝ ε′ ⊣ act′
    → (act , lvl) ⊢ δ (a , ⋆ , l) ⇒ ε ⇝ δ (a , ⋆ , l) ⇒ ε′ ⊣ act′

  A-Δ-∀-≤ : ∀ {act lvl ε ε′ act′ a l}
    → l ≤ lvl
    → (act , lvl) ⊢ ε ⇝ ε′ ⊣ act′
    → (act , lvl) ⊢ δ (a , ⋆ , l) ⇒ ε ⇝ δ (a , ⋆ , l) ⇒ ε′ ⊣ act′

-- data _⊢_⇝_⟨_⟩⊣_ : Pat × Act × Gas × ℕ → Exp → Ctx → Exp → Act → Set where
--   T : ∀ {p a g l e eᵢ ε₀ ε₁ e₀ a₁}
--     → (p , a , g , l) ⊢ e ⇝ eᵢ
--     → eᵢ ⇒ ε₀ ⟨ e₀ ⟩
--     → (a , l) ⊢ ε₀ ⇝ ε₁ ⊣ a₁
--     → (p , a , g , l) ⊢ e ⇝ ε₁ ⟨ e₀ ⟩⊣ a₁

-- data _↠_ : Exp → Exp → Set where
--   init : ∀ {e}
--     → e ↠ e

--   Φ/Δ : ∀ {e″ e e′ e₀ e₀′ ε a}
--     → e″ ↠ e
--     → ($e , pause , 𝟙 , 0) ⊢ e ⇝ ε ⟨ e₀ ⟩⊣ a
--     → Filter e₀
--     → e₀ —→ e₀′
--     → e′ ⇐ ε ⟨ e₀′ ⟩
--     → e ↠ e′

--   skip : ∀ {e″ e e′ e₀ e₀′ ε}
--     → e″ ↠ e
--     → ($e , pause , 𝟙 , 0) ⊢ e ⇝ ε ⟨ e₀ ⟩⊣ eval
--     → e₀ —→ e₀′
--     → e′ ⇐ ε ⟨ e₀′ ⟩
--     → e ↠ e′

infix 0 _⇥_

data _⇥_ : Exp → Exp → Set where
  step : ∀ {e e′ eᵢ e₀ e₀′ ε ε₀ a}
    → ($e , pause , 𝟙 , 0) ⊢ e ⇝ eᵢ
    → eᵢ ⇒ ε₀ ⟨ e₀ ⟩
    → (pause , 0) ⊢ ε₀ ⇝ ε ⊣ pause
    → e₀ —→ e₀′
    → e′ ⇐ ε ⟨ e₀′ ⟩
    → e ⇥ e′

  Φ/Δ : ∀ {e e′ e″ eᵢ e₀ e₀′ ε ε₀ a}
    -- → ($e , pause , 𝟙 , 0) ⊢ e ⇝ eᵢ
    → eᵢ ⇒ ε₀ ⟨ e₀ ⟩
    -- → (pause , 0) ⊢ ε₀ ⇝ ε ⊣ a
    → Filter e₀
    → e₀ —→ e₀′
    → e′ ⇐ ε ⟨ e₀′ ⟩
    → e′ ⇥ e″
    → e ⇥ e″

  skip : ∀ {e e′ e″ eᵢ e₀ e₀′ ε ε₀ a}
    -- → ($e , pause , 𝟙 , 0) ⊢ e ⇝ eᵢ
    → eᵢ ⇒ ε₀ ⟨ e₀ ⟩
    -- → (pause , 0) ⊢ ε₀ ⇝ ε ⊣ eval
    → e₀ —→ e₀′
    → e′ ⇐ ε ⟨ e₀′ ⟩
    → e′ ⇥ e″
    → e ⇥ e″

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
    → Γ ⊢ (ƛ e) ∶ (τₓ ⇒ τₑ)

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

  ⊢-ƛ : ∀ {Γ x e τₓ τₑ}
    → Γ , x ∶ τₓ ⊢ e ∶ τₑ
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
  → (∀ {x A}     →         Γ ∋ x ∶ A →         Δ ∋ x ∶ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ∶ B ∋ x ∶ A → Δ , y ∶ B ∋ x ∶ A)
ext ρ Z           =  Z
ext ρ (S x≢y ∋x)  =  S x≢y (ρ ∋x)

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
rename-exp ρ (⊢-φ p e)     = ⊢-φ (rename-pat ρ p) (rename-exp ρ e)
rename-exp ρ (⊢-δ Γ-⊢)   = ⊢-δ (rename-exp ρ Γ-⊢)

rename-pat ρ ⊢-E         = ⊢-E
rename-pat ρ ⊢-V         = ⊢-V
rename-pat ρ (⊢-` ∋-x)   = ⊢-` (ρ ∋-x)
rename-pat ρ (⊢-ƛ x⊢e)   = ⊢-ƛ (rename-exp (ext ρ) x⊢e)
rename-pat ρ (⊢-· e₁ e₂) = ⊢-· (rename-pat ρ e₁) (rename-pat ρ e₂)
rename-pat ρ ⊢-#         = ⊢-#
rename-pat ρ (⊢-+ e₁ e₂) = ⊢-+ (rename-pat ρ e₁) (rename-pat ρ e₂)

∋-functional : ∀ {Γ x τ₁ τ₂} → (Γ ∋ x ∶ τ₁) → (Γ ∋ x ∶ τ₂) → τ₁ ≡ τ₂
∋-functional Z Z = refl
∋-functional Z (S x≢x _) = ⊥-elim (x≢x refl)
∋-functional (S x≢x _) Z = ⊥-elim (x≢x refl)
∋-functional (S x₁≢ ∋-x₁) (S x₂≢ ∋-x₂) = ∋-functional ∋-x₁ ∋-x₂

data Progress : Exp → Set where
  step : ∀ {e₀ e₁}
    → e₀ ⇥ e₁
    → Progress e₀

  done : ∀ {v}
    → Value v
    → Progress v

progress : ∀ {e τ}
  → ∅ ⊢ e ∶ τ
  → Progress e
progress (⊢-ƛ e) = done V-ƛ
progress (⊢-· ⊢₁ ⊢₂) with (progress ⊢₁)
... | step (step {eᵢ = eᵢ₁} I₁ D₁ A₁ T₁ C₁) with (progress ⊢₂)
... | step (step {eᵢ = eᵢ₂} I₂ D₂ A₂ T₂ C₂) with (value? eᵢ₁)
... | yes V-ƛ with (value? eᵢ₂)
... | yes V₂ = step (step (I-·-⊤ M-E I₁ I₂) (D-ξ-δ (D-β-· V-ƛ V₂)) (A-Δ-1-≤ _≤_.z≤n A₁) (β-· V₂) {!C₁!})
-- ... | step (step I D A T C) = step (step (I-·-⊤ M-E I {!!}) {!!} {!!} T C)
-- ... | step (Φ/Δ x x₁ x₂ x₃ x₄) = step {!!}
-- ... | step (skip x x₁ x₂ x₃) = step {!!}
-- ... | done x = {!!}
progress (⊢-+ e e₁) = {!!}
progress ⊢-# = done V-#
progress (⊢-φ x e) = {!!}
progress (⊢-δ e) = {!!}
