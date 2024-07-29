module Dynamics where

open import Base
open import Substitution
open import Match
open import Data.Integer using (+_)
open import Data.Nat using (ℕ; _≤?_; _>_; _≤_; zero; suc; <-cmp; pred; s≤s; _<′_; _+_; _≤′_; ≤′-step; ≤′-refl)
open import Data.Nat.Induction using (<′-wellFounded)
open import Data.Nat.Properties using (≰⇒>; _>?_; +-comm)
open import Data.Product using (∃-syntax)
open import Relation.Binary using (tri<; tri>; tri≈)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≡_; cong; cong₂; subst; subst₂; sym; trans)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (id; _on_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (¬_; yes; no)
open import Induction using (RecStruct)
open import Induction.WellFounded using (WellFounded; Acc; WfRec)
open import Relation.Binary.Construct.On using (wellFounded)
open import Induction.WellFounded using (WellFounded)

applyₙ : (i : ℕ) → (x : ℕ) → (v : Exp) → Exp
applyₙ i x v with <-cmp i x
applyₙ i x v | tri< a ¬b ¬c = ` i
applyₙ i x v | tri≈ ¬a b ¬c = v
applyₙ (suc i) x v | tri> ¬a ¬b (s≤s >) = ` i

applyₑ : Exp → ℕ → Exp → Exp
applyₚ : Pat → ℕ → Exp → Pat

applyₑ (` i) x v = applyₙ i x v
applyₑ (ƛ e) x v = ƛ (applyₑ e (suc x) (↑ₑ 0 1 v))
applyₑ (eₗ `· eᵣ) x v = applyₑ eₗ x v `· applyₑ eᵣ x v
applyₑ (# n) x v = # n
applyₑ (eₗ `+ eᵣ) x v = applyₑ eₗ x v `+ applyₑ eᵣ x v
applyₑ (φ (p , ag) e) x v = φ ((applyₚ p x v) , ag) (applyₑ e x v)
applyₑ (δ r e) x v = δ r (applyₑ e x v)
applyₑ (μ e) x v = μ (applyₑ e (suc x) (↑ₑ 0 1 v))

applyₚ $e x v = $e
applyₚ $v x v = $v
applyₚ (` i) x v = patternize (applyₙ i x v)
applyₚ (ƛ e) x v = patternize (applyₑ (ƛ e) x v)
applyₚ (pₗ `· pᵣ) x v = applyₚ pₗ x v `· applyₚ pᵣ x v
applyₚ (# n) x v = # n
applyₚ (pₗ `+ pᵣ) x v = applyₚ pₗ x v `+ applyₚ pᵣ x v
applyₚ (μ e) x v = patternize (applyₑ (μ e) x v)

infix 0 _—→_

data _—→_ : Exp → Exp → Set where
  T-β-· : ∀ {v e}
    → (V : v value)
    → (ƛ e) `· v —→ applyₑ e 0 v

  T-β-+ : ∀ {nₗ nᵣ : ℕ}
    → (# nₗ) `+ (# nᵣ) —→ # (nₗ Data.Nat.+ nᵣ)

  T-β-φ : ∀ {f v}
    → (V : v value)
    → (φ f v) —→ v

  T-β-δ : ∀ {r v}
    → (V : v value)
    → (δ r v) —→ v

data _* (_R_ : Exp → Exp → Set) : Exp → Exp → Set where
  init : ∀ {e}
    → (_R_ *) e e

  next : ∀ {e e′ e″}
    → e R e′
    → (_R_ *) e′ e″
    → (_R_ *) e e″

_—→*_ : Exp → Exp → Set
_—→*_ = _—→_ *

data Ctx : Set where
  ∘    : Ctx
  _·ₗ_ : Ctx → Exp → Ctx
  _·ᵣ_ : Exp → Ctx → Ctx
  _+ₗ_ : Ctx → Exp → Ctx
  _+ᵣ_ : Exp → Ctx → Ctx
  φ    : Filter  → Ctx → Ctx
  δ    : Residue → Ctx → Ctx

infix  0 _⇒_
infixr 1 _⟨_⟩

data Obj : Set where
  _⟨_⟩ : Ctx → Exp → Obj

data _⇒_ : Exp → Obj → Set where
  D-ξ-·ₗ : ∀ {eₗ eᵣ ℰ eₗ′}
    → (D : eₗ ⇒ ℰ ⟨ eₗ′ ⟩)
    → (eₗ `· eᵣ) ⇒ (ℰ ·ₗ eᵣ) ⟨ eₗ′ ⟩

  D-ξ-·ᵣ : ∀ {vₗ eᵣ ℰ eᵣ′}
    → (V : vₗ value)
    → (D : eᵣ ⇒ ℰ ⟨ eᵣ′ ⟩)
    → (vₗ `· eᵣ) ⇒ (vₗ ·ᵣ ℰ) ⟨ eᵣ′ ⟩

  D-β-· : ∀ {vₗ vᵣ}
    → (Vₗ : vₗ value)
    → (Vᵣ : vᵣ value)
    → (vₗ `· vᵣ) ⇒ ∘ ⟨ vₗ `· vᵣ ⟩

  D-ξ-+ₗ : ∀ {eₗ eᵣ ℰ eₗ′}
    → (D : eₗ ⇒ ℰ ⟨ eₗ′ ⟩)
    → (eₗ `+ eᵣ) ⇒ (ℰ +ₗ eᵣ) ⟨ eₗ′ ⟩

  D-ξ-+ᵣ : ∀ {vₗ eᵣ ℰ eᵣ′}
    → (V : vₗ value)
    → (D : eᵣ ⇒ ℰ ⟨ eᵣ′ ⟩)
    → (vₗ `+ eᵣ) ⇒ (vₗ +ᵣ ℰ) ⟨ eᵣ′ ⟩

  D-β-+ : ∀ {vₗ vᵣ}
    → (Vₗ : vₗ value)
    → (Vᵣ : vᵣ value)
    → (vₗ `+ vᵣ) ⇒ ∘ ⟨ vₗ `+ vᵣ ⟩

  D-ξ-φ : ∀ {f e ℰ e′}
    → (D : e ⇒ ℰ ⟨ e′ ⟩)
    → (φ f e) ⇒ (φ f ℰ) ⟨ e′ ⟩

  D-β-φ : ∀ {f v}
    → (V : v value)
    → (φ f v) ⇒ ∘ ⟨ φ f v ⟩

  D-ξ-δ : ∀ {r e ℰ e′}
    → (D : e ⇒ ℰ ⟨ e′ ⟩)
    → (δ r e) ⇒ (δ r ℰ) ⟨ e′ ⟩

  D-β-δ : ∀ {r v}
    → (V : v value)
    → (δ r v) ⇒ ∘ ⟨ δ r v ⟩

infix 0 _⇐_

data _⇐_ : Exp → Obj → Set where
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

  C-φ : ∀ {f ε e e′}
    → e′ ⇐ ε ⟨ e ⟩
    → (φ f e′) ⇐ (φ f ε) ⟨ e ⟩

  C-δ : ∀ {r ε e e′}
    → e′ ⇐ ε ⟨ e ⟩
    → (δ r e′) ⇐ (δ r ε) ⟨ e ⟩

compose : Ctx → Exp → Exp
compose ∘ e = e
compose (c ·ₗ x) e = (compose c e) `· x
compose (x ·ᵣ c) e = x `· (compose c e)
compose (c +ₗ x) e = (compose c e) `+ x
compose (x +ᵣ c) e = x `+ (compose c e)
compose (φ x c) e = φ x (compose c e)
compose (δ x c) e = δ x (compose c e)

compose-⇐ : ∀ (c : Ctx) (e : Exp)
  → compose c e ⇐ c ⟨ e ⟩
compose-⇐ ∘ e = C-∘
compose-⇐ (c ·ₗ x) e = C-·ₗ (compose-⇐ c e)
compose-⇐ (x ·ᵣ c) e = C-·ᵣ (compose-⇐ c e)
compose-⇐ (c +ₗ x) e = C-+ₗ (compose-⇐ c e)
compose-⇐ (x +ᵣ c) e = C-+ᵣ (compose-⇐ c e)
compose-⇐ (φ x c) e = C-φ (compose-⇐ c e)
compose-⇐ (δ x c) e = C-δ (compose-⇐ c e)

data _⊢_⇝_ : Pat × Act × Gas × ℕ → Exp → Exp → Set where
  I-V : ∀ {p a g l v}
    → (V : v value)
    → (p , a , g , l) ⊢ v ⇝ v

  I-` : ∀ {p a g l x}
    → (p , a , g , l) ⊢ (` x) ⇝ (` x)

  I-·-⊤ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → (M : p matches (eₗ `· eᵣ))
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ `· eᵣ) ⇝ (δ (a , g , l) (eₗ′ `· eᵣ′))

  I-·-⊥ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → (¬M : ¬ (p matches (eₗ `· eᵣ)))
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ `· eᵣ) ⇝ (eₗ′ `· eᵣ′)

  I-+-⊤ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → (M : p matches (eₗ `+ eᵣ))
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ `+ eᵣ) ⇝ (δ (a , g , l) (eₗ′ `+ eᵣ′))

  I-+-⊥ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → (¬M : ¬ (p matches (eₗ `+ eᵣ)))
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ `+ eᵣ) ⇝ (eₗ′ `+ eᵣ′)

  I-φ : ∀ {pat act gas lvl p a g e e′ e″}
    → (pat , act , gas , lvl) ⊢ e ⇝ e′
    → (p , a , g , ℕ.suc lvl) ⊢ e′ ⇝ e″
    → (pat , act , gas , lvl) ⊢ (φ (p , a , g) e) ⇝ (φ (p , a , g) e″)

  I-δ : ∀ {pat act gas lvl a g l e e′}
    → (pat , act , gas , lvl) ⊢ e ⇝ e′
    → (pat , act , gas , lvl) ⊢ (δ (a , g , l) e) ⇝ (δ (a , g , l) e′)

  I-μ-⊤ : ∀ {p a g l e e′}
    → (M : p matches (μ e))
    → (p , a , g , l) ⊢ e ⇝ e′
    → (p , a , g , l) ⊢ (μ e) ⇝ (δ (a , g , l) (μ e′))

  I-μ-⊥ : ∀ {p a g l e e′}
    → (¬M : ¬ (p matches (μ e)))
    → (p , a , g , l) ⊢ e ⇝ e′
    → (p , a , g , l) ⊢ (μ e) ⇝ (μ e′)

_⇝_ : Exp → Exp → Set
e ⇝ eᵢ = ($e , ∥ , 𝟙 , 0) ⊢ e ⇝ eᵢ

⇝-strip : ∀ {p a g l e e′}
  → (p , a , g , l) ⊢ e ⇝ e′
  → (strip e) ≡ (strip e′)
⇝-strip (I-V V) = refl
⇝-strip (I-`) = refl
⇝-strip (I-·-⊤ M Iₗ Iᵣ) rewrite ⇝-strip Iₗ rewrite ⇝-strip Iᵣ = refl
⇝-strip (I-·-⊥ M Iₗ Iᵣ) rewrite ⇝-strip Iₗ rewrite ⇝-strip Iᵣ = refl
⇝-strip (I-+-⊤ M Iₗ Iᵣ) rewrite ⇝-strip Iₗ rewrite ⇝-strip Iᵣ = refl
⇝-strip (I-+-⊥ M Iₗ Iᵣ) rewrite ⇝-strip Iₗ rewrite ⇝-strip Iᵣ = refl
⇝-strip (I-φ I₀ I₁) rewrite ⇝-strip I₀ rewrite ⇝-strip I₁ = refl
⇝-strip (I-δ I) = ⇝-strip I
⇝-strip (I-μ-⊤ M I) rewrite ⇝-strip I = refl
⇝-strip (I-μ-⊥ M I) rewrite ⇝-strip I = refl

count-φ : Exp → ℕ
count-φ (` i) = 0
count-φ (ƛ e) = count-φ e
count-φ (eₗ `· eᵣ) = count-φ eₗ Data.Nat.+ count-φ eᵣ
count-φ (# n) = 0
count-φ (eₗ `+ eᵣ) = count-φ eₗ Data.Nat.+ count-φ eᵣ
count-φ (φ f e) = suc (count-φ e)
count-φ (δ r e) = count-φ e
count-φ (μ e) = count-φ e

length : Exp → ℕ
length (` i) = 1
length (ƛ e) = suc (length e)
length (eₗ `· eᵣ) = suc ((length eₗ) + (length eᵣ))
length (# n) = 1
length (eₗ `+ eᵣ) = suc ((length eₗ) + (length eᵣ))
length (φ f e) = suc (length e)
length (δ r e) = suc (length e)
length (μ e) = suc (length e)

_<-#_ : Rel (Exp) _
_<-#_ = _<′_ on length

<-#-wellFounded : WellFounded _<-#_
<-#-wellFounded = wellFounded length <′-wellFounded

_<-#φ_ : Rel (Exp) _
_<-#φ_ = Data.Nat._<′_ on count-φ

<-#φ-wellFounded : WellFounded _<-#φ_
<-#φ-wellFounded = wellFounded count-φ <′-wellFounded

open import Level using (Level; 0ℓ)

data _<-exp_ : Rel (Exp) 0ℓ where
  <-·ₗ : ∀ {eₗ eᵣ}
    → eₗ <-exp (eₗ `· eᵣ)

  <-·ᵣ : ∀ {eₗ eᵣ}
    → eᵣ <-exp (eₗ `· eᵣ)

  <-+ₗ : ∀ {eₗ eᵣ}
    → eₗ <-exp (eₗ `+ eᵣ)

  <-+ᵣ : ∀ {eₗ eᵣ}
    → eᵣ <-exp (eₗ `+ eᵣ)

  <-φ : ∀ {f e}
    → e <-exp (φ f e)

  <-δ : ∀ {r e}
    → e <-exp (δ r e)

  <-μ : ∀ {e}
    → e <-exp (μ e)

<-exp-Rec : {ℓ : Level} → RecStruct Exp ℓ ℓ
<-exp-Rec = WfRec _<-exp_

<-exp-wellFounded : WellFounded _<-exp_
<-exp-wellFounded′ : ∀ e → (<-exp-Rec (Acc _<-exp_) e)

<-exp-wellFounded e = Acc.acc (<-exp-wellFounded′ e)

<-exp-wellFounded′ (eₗ `· eᵣ) <-·ₗ = <-exp-wellFounded eₗ
<-exp-wellFounded′ (eₗ `· eᵣ) <-·ᵣ = <-exp-wellFounded eᵣ
<-exp-wellFounded′ (eₗ `+ eᵣ) <-+ₗ = <-exp-wellFounded eₗ
<-exp-wellFounded′ (eₗ `+ eᵣ) <-+ᵣ = <-exp-wellFounded eᵣ
<-exp-wellFounded′ (φ f e)    <-φ  = <-exp-wellFounded e
<-exp-wellFounded′ (δ r e)    <-δ  = <-exp-wellFounded e
<-exp-wellFounded′ (μ e)      <-μ  = <-exp-wellFounded e

open import Data.Product.Relation.Binary.Lex.Strict  using (×-Lex; ×-wellFounded')

_<-#φ-exp_ : Rel (Exp × Exp) 0ℓ
_<-#φ-exp_ = ×-Lex (Eq._≡_ on count-φ) _<-#φ_ _<-exp_

<-#φ-respects-≡φ : _<-#φ_ Relation.Binary.Respectsʳ (_≡_ on count-φ)
<-#φ-respects-≡φ {x = x} {y} {z} ≡φ <φ with count-φ y with count-φ z
... | φy | φz = subst ((suc (count-φ x)) Data.Nat.≤′_) ≡φ <φ

<-#φ-exp-wellFounded : WellFounded _<-#φ-exp_
<-#φ-exp-wellFounded = ×-wellFounded' Eq.trans (λ { {x = x} {y} {z} ≡φ <φ → subst ((suc (count-φ x)) Data.Nat.≤′_) ≡φ <φ }) <-#φ-wellFounded <-exp-wellFounded

open Induction.WellFounded.All (<-#φ-wellFounded) renaming (wfRec to <-#φ-rec)

sm≤′m+sr : ∀ {m r} → suc m Data.Nat.≤′ (m + suc r)
sm≤′m+sr {m} {zero} rewrite Data.Nat.Properties.+-comm m 1 = Data.Nat.≤′-refl
sm≤′m+sr {m} {suc r} rewrite Data.Nat.Properties.+-comm m (suc (suc r)) rewrite Data.Nat.Properties.+-comm (suc r) m = Data.Nat.≤′-step sm≤′m+sr

sm≤′sm+r : ∀ {m r} → suc m Data.Nat.≤′ (suc r) + m
sm≤′sm+r {m} {zero} = Data.Nat.Properties.s≤′s Data.Nat.≤′-refl
sm≤′sm+r {m} {suc r} = Data.Nat.≤′-step sm≤′sm+r

<-#φ-exp-·ₗ : ∀ {eₗ} {eᵣ} → (eₗ , eₗ) <-#φ-exp (eₗ `· eᵣ , eₗ `· eᵣ)
<-#φ-exp-·ₗ {eₗ} {eᵣ} with count-φ eᵣ
<-#φ-exp-·ₗ {eₗ} {eᵣ} | zero = inj₂ (Data.Nat.Properties.+-comm 0 (count-φ eₗ) , <-·ₗ)
<-#φ-exp-·ₗ {eₗ} {eᵣ} | suc φᵣ = inj₁ sm≤′m+sr

<-#φ-exp-·ᵣ : ∀ {eₗ} {eᵣ} → (eᵣ , eᵣ) <-#φ-exp (eₗ `· eᵣ , eₗ `· eᵣ)
<-#φ-exp-·ᵣ {eₗ} {eᵣ} with count-φ eₗ
<-#φ-exp-·ᵣ {eₗ} {eᵣ} | zero = inj₂ (refl , <-·ᵣ)
<-#φ-exp-·ᵣ {eₗ} {eᵣ} | suc φₗ = inj₁ sm≤′sm+r

<-#φ-exp-+ₗ : ∀ {eₗ} {eᵣ} → (eₗ , eₗ) <-#φ-exp (eₗ `+ eᵣ , eₗ `+ eᵣ)
<-#φ-exp-+ₗ {eₗ} {eᵣ} with count-φ eᵣ
<-#φ-exp-+ₗ {eₗ} {eᵣ} | zero = inj₂ (Data.Nat.Properties.+-comm 0 (count-φ eₗ) , <-+ₗ)
<-#φ-exp-+ₗ {eₗ} {eᵣ} | suc φᵣ = inj₁ sm≤′m+sr

<-#φ-exp-+ᵣ : ∀ {eₗ} {eᵣ} → (eᵣ , eᵣ) <-#φ-exp (eₗ `+ eᵣ , eₗ `+ eᵣ)
<-#φ-exp-+ᵣ {eₗ} {eᵣ} with count-φ eₗ
<-#φ-exp-+ᵣ {eₗ} {eᵣ} | zero = inj₂ (refl , <-+ᵣ)
<-#φ-exp-+ᵣ {eₗ} {eᵣ} | suc φₗ = inj₁ sm≤′sm+r

<-#φ-exp-μ : ∀ {e} → (e , e) <-#φ-exp (μ e , μ e)
<-#φ-exp-μ {e} = inj₂ (refl , <-μ)

instr′ : (p : Pat) (a : Act) (g : Gas) (l : ℕ) (e : Exp) → Acc _<-#φ-exp_ (e , e) → ∃[ e′ ](count-φ e ≡ count-φ e′ × (p , a , g , l) ⊢ e ⇝ e′)
instr′ p a g l (` i) (Acc.acc rs) = (` i) , refl , I-`
instr′ p a g l (ƛ e) (Acc.acc rs) = ƛ e , refl , I-V V-ƛ
instr′ p a g l (eₗ `· eᵣ) (Acc.acc rs) with (p matches? (eₗ `· eᵣ)) with instr′ p a g l eₗ (rs <-#φ-exp-·ₗ) with instr′ p a g l eᵣ (rs <-#φ-exp-·ᵣ)
instr′ p a g l (eₗ `· eᵣ) (Acc.acc rs) | yes M | eₗ′ , ≡ₗ , Iₗ | eᵣ′ , ≡ᵣ , Iᵣ rewrite ≡ₗ rewrite ≡ᵣ = (δ (a , g , l) (eₗ′ `· eᵣ′)) , refl , (I-·-⊤ M Iₗ Iᵣ)
instr′ p a g l (eₗ `· eᵣ) (Acc.acc rs) | no ¬M | eₗ′ , ≡ₗ , Iₗ | eᵣ′ , ≡ᵣ , Iᵣ rewrite ≡ₗ rewrite ≡ᵣ = eₗ′ `· eᵣ′ , refl , I-·-⊥ ¬M Iₗ Iᵣ
instr′ p a g l (# n) (Acc.acc rs) = # n , refl , I-V V-#
instr′ p a g l (eₗ `+ eᵣ) (Acc.acc rs) with (p matches? (eₗ `+ eᵣ)) with instr′ p a g l eₗ (rs <-#φ-exp-+ₗ) with instr′ p a g l eᵣ (rs <-#φ-exp-+ᵣ)
instr′ p a g l (eₗ `+ eᵣ) (Acc.acc rs) | yes M | eₗ′ , ≡ₗ , Iₗ | eᵣ′ , ≡ᵣ , Iᵣ rewrite ≡ₗ rewrite ≡ᵣ = (δ (a , g , l) (eₗ′ `+ eᵣ′)) , refl , I-+-⊤ M Iₗ Iᵣ
instr′ p a g l (eₗ `+ eᵣ) (Acc.acc rs) | no ¬M | eₗ′ , ≡ₗ , Iₗ | eᵣ′ , ≡ᵣ , Iᵣ  rewrite ≡ₗ rewrite ≡ᵣ = eₗ′ `+ eᵣ′ , refl , I-+-⊥ ¬M Iₗ Iᵣ
instr′ p a g l (φ (p₀ , a₀ , g₀) e) (Acc.acc rs) with instr′ p a g l e (rs (inj₁ Data.Nat.≤′-refl))
instr′ p a g l (φ (p₀ , a₀ , g₀) e) (Acc.acc rs) | e′ , e≡φe′ , I′ with instr′ p₀ a₀ g₀ (Data.Nat.ℕ.suc l) e′ (rs (inj₁ (<-#φ-subst {e} {e′} {(p₀ , a₀ , g₀)} e≡φe′)))
  where
    <-#φ-subst : ∀ {e e′ f}
      → count-φ e ≡ count-φ e′
      → e′ <-#φ φ f e
    <-#φ-subst {e = e} {f = f} e≡φe′ = subst (_<′ Data.Nat.ℕ.suc (count-φ e)) e≡φe′ Data.Nat.≤′-refl
instr′ p a g l (φ (p₀ , a₀ , g₀) e) (Acc.acc rs) | e′ , e≡φe′ , I′ | e″ , e′≡φe″ , I″ = (φ (p₀ , a₀ , g₀) e″) , cong Data.Nat.ℕ.suc (trans e≡φe′ e′≡φe″) , I-φ I′ I″
instr′ p a g l (δ r e) (Acc.acc rs) with instr′ p a g l e (rs (inj₂ (refl , <-δ)))
instr′ p a g l (δ r e) (Acc.acc rs) | e′ , e≡e′ , I′ = δ r e′ , e≡e′ , I-δ I′
instr′ p a g l (μ e) (Acc.acc rs) with (p matches? (μ e)) with instr′ p a g l e (rs <-#φ-exp-μ)
instr′ p a g l (μ e) (Acc.acc rs) | yes M | e′ , ≡ , I rewrite ≡ = δ (a , g , l) (μ e′) , refl , I-μ-⊤ M I
instr′ p a g l (μ e) (Acc.acc rs) | no ¬M | e′ , ≡ , I rewrite ≡ = μ e′ , refl , I-μ-⊥ ¬M I

instr : (p : Pat) (a : Act) (g : Gas) (lvl : ℕ) (e : Exp) → Exp
instr p a g l e with instr′ p a g l e (<-#φ-exp-wellFounded (e , e))
instr p a g l e | e′ , ≡φ = e′

⇝-instr : ∀ p a g l e
  → (p , a , g , l) ⊢ e ⇝ (instr p a g l e)
⇝-instr p a g l e with instr′ p a g l e (<-#φ-exp-wellFounded (e , e))
⇝-instr p a g l e | e′ , ≡φ , I = I

decay : Ctx → Ctx
decay ∘ = ∘
decay (ε ·ₗ e) = (decay ε) ·ₗ e
decay (e ·ᵣ ε) = e ·ᵣ (decay ε)
decay (ε +ₗ e) = (decay ε) +ₗ e
decay (e +ᵣ ε) = e +ᵣ (decay ε)
decay (φ f  ε) = φ f (decay ε)
decay (δ (a , 𝟙 , l) ε) = (decay ε)
decay (δ (a , ⋆ , l) ε) = δ (a , ⋆ , l) (decay ε)

select : Act → ℕ → Ctx → Act
select act lvl ∘ = act
select act lvl (c ·ₗ e) = select act lvl c
select act lvl (e ·ᵣ c) = select act lvl c
select act lvl (c +ₗ e) = select act lvl c
select act lvl (e +ᵣ c) = select act lvl c
select act lvl (φ f c) = select act lvl c
select act lvl (δ (a , g , l) c) with l ≤? lvl
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

  A-φ : ∀ {act lvl ε act′ pag}
    → (act , lvl) ⊢ ε ⊣ act′
    → (act , lvl) ⊢ φ pag ε ⊣ act′

  A-Δ-> : ∀ {act lvl ε act′ a g l}
    → l > lvl
    → (a , l) ⊢ ε ⊣ act′
    → (act , lvl) ⊢ δ (a , g , l)  ε ⊣ act′

  A-Δ-≤ : ∀ {act lvl ε act′ a g l}
    → l ≤ lvl
    → (act , lvl) ⊢ ε ⊣ act′
    → (act , lvl) ⊢ δ (a , g , l)  ε ⊣ act′

_⊣_ : Ctx → Act → Set
c ⊣ a = (∥ , 0) ⊢ c ⊣ a

⊢⊣-select : ∀ {a l ε}
  → (a , l) ⊢ ε ⊣ (select a l ε)
⊢⊣-select {ε = ∘} = A-∘
⊢⊣-select {ε = ε ·ₗ e} = A-·ₗ ⊢⊣-select
⊢⊣-select {ε = e ·ᵣ ε} = A-·-r ⊢⊣-select
⊢⊣-select {ε = ε +ₗ e} = A-+-l ⊢⊣-select
⊢⊣-select {ε = e +ᵣ ε} = A-+-r ⊢⊣-select
⊢⊣-select {ε = φ f  ε} = A-φ ⊢⊣-select
⊢⊣-select {a = act} {l = lvl} {ε = δ (a , _ , l)  ε} with (l ≤? lvl)
... | yes ≤ = (A-Δ-≤ ≤) ⊢⊣-select
... | no  ≰ = A-Δ-> (≰⇒> ≰) ⊢⊣-select

data _⊢_⇥_ : Pat × Act × Gas × ℕ → Exp → Exp → Set where
  step : ∀ {p a g l e eᵢ e′ e₀ e₀′ ε₀}
    → (I : (p , a , g , l) ⊢ e ⇝ eᵢ)
    → (D : eᵢ ⇒ ε₀ ⟨ e₀ ⟩)
    → (A : (¬ (e₀ filter)) × (a , l) ⊢ ε₀ ⊣ ∥)
    → (T : e₀ —→ e₀′)
    → (C : e′ ⇐ (decay ε₀) ⟨ e₀′ ⟩)
    → (p , a , g , l) ⊢ e ⇥ e′

  skip : ∀ {p a g l e eᵢ e′ e″ e₀ e₀′ ε₀}
    → (I : (p , a , g , l) ⊢ e ⇝ eᵢ)
    → (D : eᵢ ⇒ ε₀ ⟨ e₀ ⟩)
    → (A : e₀ filter ⊎ (a , l) ⊢ ε₀ ⊣ ⊳)
    → (T : e₀ —→ e₀′)
    → (C : e′ ⇐ (decay ε₀) ⟨ e₀′ ⟩)
    → (R : (p , a , g , l) ⊢ e′ ⇥ e″)
    → (p ,  a ,  g ,  l) ⊢ e ⇥ e″

  done : ∀ {p a g l v}
    → (V : v value)
    → (p , a , g , l) ⊢ v ⇥ v

_⇥_ : Exp → Exp → Set
e₀ ⇥ e₁ = ($e , ∥ , 𝟙 , 0) ⊢ e₀ ⇥ e₁

data _↦_ : Exp → Exp → Set where
  step : ∀ {e c e₀ e₀′ e′}
    → (D : e ⇒ c ⟨ e₀ ⟩)
    → (T : e₀ —→ e₀′)
    → (C : e′ ⇐ c ⟨ e₀′ ⟩)
    → e ↦ e′

_↦*_ : Exp → Exp → Set
_↦*_ = _↦_ *

_⇥*_ : Exp → Exp → Set
_⇥*_ = _⇥_ *

↦*-cong-·ᵣ : ∀ {e₀ e₁ : Exp} {eᵣ : Exp}
  → e₀ ↦* e₁
  → (e₀ `· eᵣ) ↦* (e₁ `· eᵣ)
↦*-cong-·ᵣ init = init
↦*-cong-·ᵣ (next (step D T C) K) = next (step (D-ξ-·ₗ D) T (C-·ₗ C)) (↦*-cong-·ᵣ K)

↦*-cong-·ₗ : ∀ {e₀ e₁ eₗ : Exp}
  → eₗ value
  → e₀ ↦* e₁
  → (eₗ `· e₀) ↦* (eₗ `· e₁)
↦*-cong-·ₗ V init = init
↦*-cong-·ₗ V (next (step D T C) K) = next (step (D-ξ-·ᵣ V D) T (C-·ᵣ C)) (↦*-cong-·ₗ V K)

↦*-cong-+ᵣ : ∀ {e₀ e₁ : Exp} {eᵣ : Exp}
  → e₀ ↦* e₁
  → (e₀ `+ eᵣ) ↦* (e₁ `+ eᵣ)
↦*-cong-+ᵣ init = init
↦*-cong-+ᵣ (next (step D T C) K) = next (step (D-ξ-+ₗ D) T (C-+ₗ C)) (↦*-cong-+ᵣ K)

↦*-cong-+ₗ : ∀ {e₀ e₁ eₗ : Exp}
  → eₗ value
  → e₀ ↦* e₁
  → (eₗ `+ e₀) ↦* (eₗ `+ e₁)
↦*-cong-+ₗ V init = init
↦*-cong-+ₗ V (next (step D T C) K) = next (step (D-ξ-+ᵣ V D) T (C-+ᵣ C)) (↦*-cong-+ₗ V K)

compose-∘ : ∀ {e o}
  → e ⇒ ∘ ⟨ o ⟩
  → e ≡ o
compose-∘ (D-β-· Vₗ Vᵣ) = refl
compose-∘ (D-β-+ Vₗ Vᵣ) = refl
compose-∘ (D-β-φ V) = refl
compose-∘ (D-β-δ V) = refl

↑ₑ-strip : ∀ (c : ℕ) (d : ℕ) (e : Exp)
  → ↑ₑ c d (strip e) ≡ strip (↑ₑ c d e)
↑ₑ-strip c d (` i) = refl
↑ₑ-strip c d (ƛ e) = cong ƛ_ (↑ₑ-strip (suc c) d e)
↑ₑ-strip c d (eₗ `· eᵣ) = cong₂ _`·_ (↑ₑ-strip c d eₗ) (↑ₑ-strip c d eᵣ)
↑ₑ-strip c d (# n) = refl
↑ₑ-strip c d (eₗ `+ eᵣ) = cong₂ _`+_ (↑ₑ-strip c d eₗ) (↑ₑ-strip c d eᵣ)
↑ₑ-strip c d (φ f e) = ↑ₑ-strip c d e
↑ₑ-strip c d (δ r e) = ↑ₑ-strip c d e
↑ₑ-strip c d (μ e) = cong μ_ (↑ₑ-strip (suc c) d e)

applyₙ-strip : ∀ (i x : ℕ) (v : Exp)
  → applyₙ i x (strip v) ≡ strip (applyₙ i x v)
applyₙ-strip i x v with <-cmp i x
applyₙ-strip i x v | tri< a ¬b ¬c = refl
applyₙ-strip i x v | tri≈ ¬a b ¬c = refl
applyₙ-strip (suc i) x v | tri> ¬a ¬b (s≤s c) = refl

applyₑ-strip : ∀ (e : Exp) (x : ℕ) (v : Exp)
  → applyₑ (strip e) x (strip v) ≡ strip (applyₑ e x v)
applyₑ-strip (` i) x v = applyₙ-strip i x v
applyₑ-strip (ƛ e) x v rewrite ↑ₑ-strip 0 1 v = cong ƛ_ (applyₑ-strip e (suc x) (↑ₑ 0 1 v))
applyₑ-strip (eₗ `· eᵣ) x v = cong₂ _`·_ (applyₑ-strip eₗ x v) (applyₑ-strip eᵣ x v)
applyₑ-strip (# n) x v = refl
applyₑ-strip (eₗ `+ eᵣ) x v = cong₂ _`+_ (applyₑ-strip eₗ x v) (applyₑ-strip eᵣ x v)
applyₑ-strip (φ f e) x v = applyₑ-strip e x v
applyₑ-strip (δ r e) x v = applyₑ-strip e x v
applyₑ-strip (μ e) x v rewrite ↑ₑ-strip 0 1 v = cong μ_ (applyₑ-strip e (suc x) (↑ₑ 0 1 v))

stripₖ : Ctx → Ctx
stripₖ ∘ = ∘
stripₖ (c ·ₗ x) = (stripₖ c) ·ₗ (strip x)
stripₖ (x ·ᵣ c) = (strip x) ·ᵣ (stripₖ c)
stripₖ (c +ₗ x) = (stripₖ c) +ₗ (strip x)
stripₖ (x +ᵣ c) = (strip x) +ᵣ (stripₖ c)
stripₖ (φ x c) = stripₖ c
stripₖ (δ x c) = stripₖ c

strip-value : ∀ {v : Exp}
  → v value
  → strip v value
strip-value V-ƛ = V-ƛ
strip-value V-# = V-#

-- →-strip : ∀ {e e′}
--   → e —→ e′
--   → (strip e) —→ (strip e′)
-- →-strip (T-β-· {v = v} {e = e} V) rewrite sym (applyₑ-strip e 0 v) = T-β-· (strip-value V)
-- →-strip T-β-+ = T-β-+
-- →-strip (T-β-φ V) = {!!}
-- →-strip (T-β-δ V) = {!!}

⇐-strip : ∀ {e c o}
  → e ⇐ c ⟨ o ⟩
  → strip e ⇐ (stripₖ c) ⟨ strip o ⟩
⇐-strip C-∘ = C-∘
⇐-strip (C-·ₗ C) = C-·ₗ (⇐-strip C)
⇐-strip (C-·ᵣ C) = C-·ᵣ (⇐-strip C)
⇐-strip (C-+ₗ C) = C-+ₗ (⇐-strip C)
⇐-strip (C-+ᵣ C) = C-+ᵣ (⇐-strip C)
⇐-strip (C-φ C) = ⇐-strip C
⇐-strip (C-δ C) = ⇐-strip C

-- data _⇴_ : Exp → Exp → Set where
--   O-` : ∀ {i}
--     → (` i) ⇴ (` i)

--   O-ƛ : ∀ {e}
--     → (ƛ e) ⇴ (ƛ e)

--   O-· : ∀ {eₗ eᵣ eₗ′ eᵣ′}
--     → eₗ ⇴ eₗ′
--     → eᵣ ⇴ eᵣ′
--     → (eₗ `· eᵣ) ⇴ (eₗ′ `· eᵣ′)

--   O-# : ∀ {n}
--     → (# n) ⇴ (# n)

--   O-+ : ∀ {eₗ eᵣ eₗ′ eᵣ′}
--     → eₗ ⇴ eₗ′
--     → eᵣ ⇴ eᵣ′
--     → (eₗ `+ eᵣ) ⇴ (eₗ′ `+ eᵣ′)

--   O-φ : ∀ {f e e′}
--     → e ⇴ e′
--     → φ f e ⇴ φ f e′

--   O-δ-δ : ∀ {aₒ gₒ lₒ aᵢ gᵢ lᵢ e e′}
--     → e ⇴ e′
--     → (lᵢ > lₒ)
--     → δ (aᵢ , gᵢ , lᵢ) e′
--     → (δ (aₒ , gₒ , lₒ) (δ (aᵢ , gᵢ , lᵢ) e)) ⇴ δ (aᵢ , gᵢ , lᵢ) e′

m≤′m+n : ∀ {m n} → m ≤′ m + n
m≤′m+n {m} {zero} rewrite +-comm m 0 = ≤′-refl
m≤′m+n {m} {suc n} rewrite +-comm m (suc n) rewrite +-comm n m = ≤′-step m≤′m+n

≤′-cong : ∀ {m n} → m ≤′ n → (suc m) ≤′ (suc n)
≤′-cong {m} {.m} ≤′-refl = ≤′-refl
≤′-cong {m} {.(suc _)} (≤′-step m≤′n) = ≤′-step (≤′-cong m≤′n)

<-#-·ₗ : ∀ {eₗ} {eᵣ} → eₗ <-# (eₗ `· eᵣ)
<-#-·ₗ {eₗ} {eᵣ} with length eₗ with length eᵣ
<-#-·ₗ {eₗ} {eᵣ} | nₗ | nᵣ = ≤′-cong m≤′m+n

<-#-·ᵣ : ∀ {eₗ} {eᵣ} → eᵣ <-# (eₗ `· eᵣ)
<-#-·ᵣ {eₗ} {eᵣ} with length eₗ with length eᵣ
<-#-·ᵣ {eₗ} {eᵣ} | nₗ | nᵣ rewrite +-comm nₗ nᵣ = ≤′-cong m≤′m+n

<-#-+ₗ : ∀ {eₗ} {eᵣ} → eₗ <-# (eₗ `+ eᵣ)
<-#-+ₗ {eₗ} {eᵣ} with length eₗ with length eᵣ
<-#-+ₗ {eₗ} {eᵣ} | nₗ | nᵣ = ≤′-cong m≤′m+n

<-#-+ᵣ : ∀ {eₗ} {eᵣ} → eᵣ <-# (eₗ `+ eᵣ)
<-#-+ᵣ {eₗ} {eᵣ} with length eₗ with length eᵣ
<-#-+ᵣ {eₗ} {eᵣ} | nₗ | nᵣ rewrite +-comm nₗ nᵣ = ≤′-cong m≤′m+n

optimize′ : (e : Exp) → Acc _<-#_ e → Exp
optimize′ (` i) (Acc.acc rs) = ` i
optimize′ (ƛ e) (Acc.acc rs) = ƛ e
optimize′ (eₗ `· eᵣ) (Acc.acc rs) = (optimize′ eₗ (rs <-#-·ₗ)) `· (optimize′ eᵣ (rs <-#-·ᵣ))
optimize′ (# n) (Acc.acc rs) = # n
optimize′ (eₗ `+ eᵣ) (Acc.acc rs) = (optimize′ eₗ (rs <-#-+ₗ)) `+ (optimize′ eᵣ (rs <-#-+ᵣ))
optimize′ (φ f e) (Acc.acc rs) = φ f (optimize′ e (rs ≤′-refl))
optimize′ (δ r (` i)) (Acc.acc rs) = δ r (` i)
optimize′ (δ r (ƛ e)) (Acc.acc rs) = δ r (optimize′ (ƛ e) (rs ≤′-refl))
optimize′ (δ r (eₗ `· eᵣ)) (Acc.acc rs) = δ r (optimize′ (eₗ `· eᵣ) (rs ≤′-refl))
optimize′ (δ r (# n)) (Acc.acc rs) = δ r (# n)
optimize′ (δ r (eₗ `+ eᵣ)) (Acc.acc rs) = δ r (optimize′ (eₗ `+ eᵣ) (rs ≤′-refl))
optimize′ (δ r (φ f e)) (Acc.acc rs) = δ r (optimize′ (φ f e) (rs ≤′-refl))
optimize′ (δ (aₒ , gₒ , lₒ) (δ (aᵢ , gᵢ , lᵢ) e)) (Acc.acc rs) with lᵢ >? lₒ
optimize′ (δ (aₒ , gₒ , lₒ) (δ (aᵢ , gᵢ , lᵢ) e)) (Acc.acc rs) | yes lᵢ>lₒ = optimize′ (δ (aᵢ , gᵢ , lᵢ) e) (rs ≤′-refl)
optimize′ (δ (aₒ , gₒ , lₒ) (δ (aᵢ , gᵢ , lᵢ) e)) (Acc.acc rs) | no lᵢ≤lₒ  = optimize′ (δ (aₒ , gₒ , lₒ) e) (rs ≤′-refl)
optimize′ (δ r (μ e)) (Acc.acc rs) = δ r (μ (optimize′ e (rs (≤′-step ≤′-refl))))
optimize′ (μ e) (Acc.acc rs) = μ (optimize′ e (rs ≤′-refl))

optimize : Exp → Exp
optimize e = optimize′ e (<-#-wellFounded e)
