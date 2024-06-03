module Dynamics where

open import Base
open import Substitution
open import Match
open import Data.Integer using (+_)
open import Data.Nat using (ℕ; _≤?_; _>_; _≤_; zero; suc; <-cmp; pred; s≤s; _<′_)
open import Data.Nat.Induction using (<′-wellFounded)
open import Data.Nat.Properties using (≰⇒>)
open import Data.Product using (∃-syntax)
open import Relation.Binary using (tri<; tri>; tri≈)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≡_; cong; cong₂; subst; subst₂; sym; trans)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (id; _on_)
open import Data.Product using (_×_; _,_)
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
applyₑ (eₗ · eᵣ) x v = applyₑ eₗ x v · applyₑ eᵣ x v
applyₑ (# n) x v = # n
applyₑ (eₗ + eᵣ) x v = applyₑ eₗ x v + applyₑ eᵣ x v
applyₑ (φ (p , ag) e) x v = φ ((applyₚ p x v) , ag) (applyₑ e x v)
applyₑ (δ r e) x v = δ r (applyₑ e x v)

applyₚ $e x v = $e
applyₚ $v x v = $v
applyₚ (` i) x v = patternize (applyₙ i x v)
applyₚ (ƛ e) x v = patternize (applyₑ (ƛ e) x v)
applyₚ (pₗ · pᵣ) x v = applyₚ pₗ x v · applyₚ pᵣ x v
applyₚ (# n) x v = # n
applyₚ (pₗ + pᵣ) x v = applyₚ pₗ x v + applyₚ pᵣ x v

infix 0 _—→_

data _—→_ : Exp → Exp → Set where
  T-β-· : ∀ {v e}
    → v value
    → (ƛ e) · v —→ applyₑ e 0 v

  T-β-φ : ∀ {f v}
    → v value
    → (φ f v) —→ v

  T-β-δ : ∀ {r v}
    → v value
    → (δ r v) —→ v

data Ctx : Set where
  ∘    : Ctx
  _·ₗ_ : Ctx → Exp → Ctx
  _·ᵣ_ : Exp → Ctx → Ctx
  _+ₗ_ : Ctx → Exp → Ctx
  _+ᵣ_ : Exp → Ctx → Ctx
  φ    : Filter  → Ctx → Ctx
  δ    : Residue → Ctx → Ctx

data _⇒_⟨_⟩ : Exp → Ctx → Exp → Set where
  D-β-` : ∀ {x}
    → (` x) ⇒ ∘ ⟨ (` x) ⟩

  D-ξ-·-l : ∀ {eₗ eᵣ ℰ eₗ′}
    → (D : eₗ ⇒ ℰ ⟨ eₗ′ ⟩)
    → (eₗ · eᵣ) ⇒ (ℰ ·ₗ eᵣ) ⟨ eₗ′ ⟩

  D-ξ-·-r : ∀ {vₗ eᵣ ℰ eᵣ′}
    → (V : vₗ value)
    → (D : eᵣ ⇒ ℰ ⟨ eᵣ′ ⟩)
    → (vₗ · eᵣ) ⇒ (vₗ ·ᵣ ℰ) ⟨ eᵣ′ ⟩

  D-β-· : ∀ {vₗ vᵣ}
    → (Vₗ : vₗ value)
    → (Vᵣ : vᵣ value)
    → (vₗ · vᵣ) ⇒ ∘ ⟨ vₗ · vᵣ ⟩

  D-ξ-+-l : ∀ {eₗ eᵣ ℰ eₗ′}
    → (D : eₗ ⇒ ℰ ⟨ eₗ′ ⟩)
    → (eₗ + eᵣ) ⇒ (ℰ +ₗ eᵣ) ⟨ eₗ′ ⟩

  D-ξ-+-r : ∀ {vₗ eᵣ ℰ eᵣ′}
    → (V : vₗ value)
    → (D : eᵣ ⇒ ℰ ⟨ eᵣ′ ⟩)
    → (vₗ + eᵣ) ⇒ (vₗ +ᵣ ℰ) ⟨ eᵣ′ ⟩

  D-β-+ : ∀ {vₗ vᵣ}
    → (Vₗ : vₗ value)
    → (Vᵣ : vᵣ value)
    → (vₗ + vᵣ) ⇒ ∘ ⟨ vₗ + vᵣ ⟩

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

data _⇐_⟨_⟩ : Exp → Ctx → Exp → Set where
  C-∘ : ∀ {e}
    → e ⇐ ∘ ⟨ e ⟩

  C-·-l : ∀ {εₗ eᵣ eₗ e}
    → eₗ ⇐ εₗ ⟨ e ⟩
    → (eₗ · eᵣ) ⇐ (εₗ ·ₗ eᵣ) ⟨ e ⟩

  C-·-r : ∀ {eₗ εᵣ eᵣ e}
    → eᵣ ⇐ εᵣ ⟨ e ⟩
    → (eₗ · eᵣ) ⇐ (eₗ ·ᵣ εᵣ) ⟨ e ⟩

  C-+-l : ∀ {εₗ eᵣ eₗ e}
    → eₗ ⇐ εₗ ⟨ e ⟩
    → (eₗ + eᵣ) ⇐ (εₗ +ₗ eᵣ) ⟨ e ⟩

  C-+-r : ∀ {eₗ εᵣ eᵣ e}
    → eᵣ ⇐ εᵣ ⟨ e ⟩
    → (eₗ + eᵣ) ⇐ (eₗ +ᵣ εᵣ) ⟨ e ⟩

  C-φ : ∀ {pag ε e e′}
    → e′ ⇐ ε ⟨ e ⟩
    → (φ pag  e′) ⇐ (φ pag  ε) ⟨ e ⟩

  C-δ : ∀ {agl ε e e′}
    → e′ ⇐ ε ⟨ e ⟩
    → (δ agl  e′) ⇐ (δ agl  ε) ⟨ e ⟩

data _⊢_⇝_ : Pat × Act × Gas × ℕ → Exp → Exp → Set where
  I-V : ∀ {pagl v}
    → v value
    → pagl ⊢ v ⇝ v

  I-`-⊤ : ∀ {p a g l x}
    → p matches (` x)
    → (p , a , g , l) ⊢ (` x) ⇝ (δ (a , g , l) (` x))

  I-`-⊥ : ∀ {p a g l x}
    → ¬ (p matches (` x))
    → (p , a , g , l) ⊢ (` x) ⇝ (` x)

  I-·-⊤ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → p matches (eₗ · eᵣ)
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ · eᵣ) ⇝ (δ (a , g , l) (eₗ′ · eᵣ′))

  I-·-⊥ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → ¬ (p matches (eₗ · eᵣ))
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ · eᵣ) ⇝ (eₗ′ · eᵣ′)

  I-+-⊤ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → p matches (eₗ + eᵣ)
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ + eᵣ) ⇝ (δ (a , g , l) (eₗ′ + eᵣ′))

  I-+-⊥ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
    → ¬ (p matches (eₗ + eᵣ))
    → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
    → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
    → (p , a , g , l) ⊢ (eₗ + eᵣ) ⇝ (eₗ′ + eᵣ′)

  I-φ : ∀ {pat act gas lvl p a g e e′ e″}
    → (pat , act , gas , lvl) ⊢ e ⇝ e′
    → (p , a , g , ℕ.suc lvl) ⊢ e′ ⇝ e″
    → (pat , act , gas , lvl) ⊢ (φ (p , a , g) e) ⇝ (φ (p , a , g) e″)

  I-δ : ∀ {pat act gas lvl a g l e e′}
    → (pat , act , gas , lvl) ⊢ e ⇝ e′
    → (pat , act , gas , lvl) ⊢ (δ (a , g , l) e) ⇝ (δ (a , g , l) e′)

count-φ : Exp → ℕ
count-φ (` i) = 0
count-φ (ƛ e) = count-φ e
count-φ (eₗ · eᵣ) = count-φ eₗ Data.Nat.+ count-φ eᵣ
count-φ (# n) = 0
count-φ (eₗ + eᵣ) = count-φ eₗ Data.Nat.+ count-φ eᵣ
count-φ (φ f e) = suc (count-φ e)
count-φ (δ r e) = count-φ e

_<-φ_ : Rel (Exp) _
_<-φ_ = Data.Nat._<′_ on count-φ

<-φ-wellFounded : WellFounded _<-φ_
<-φ-wellFounded = wellFounded count-φ <′-wellFounded

open import Level using (Level; 0ℓ)

data _<-exp_ : Rel (Exp) 0ℓ where
  <-·ₗ : ∀ {eₗ eᵣ}
    → eₗ <-exp (eₗ · eᵣ)

  <-·ᵣ : ∀ {eₗ eᵣ}
    → eᵣ <-exp (eₗ · eᵣ)

  <-+ₗ : ∀ {eₗ eᵣ}
    → eₗ <-exp (eₗ + eᵣ)

  <-+ᵣ : ∀ {eₗ eᵣ}
    → eᵣ <-exp (eₗ + eᵣ)

  <-δ : ∀ {r e}
    → e <-exp (δ r e)

<-exp-Rec : {ℓ : Level} → RecStruct Exp ℓ ℓ
<-exp-Rec = WfRec _<-exp_

<-exp-wellFounded : WellFounded _<-exp_
<-exp-wellFounded′ : ∀ e → (<-exp-Rec (Acc _<-exp_) e)

<-exp-wellFounded e = Acc.acc (<-exp-wellFounded′ e)

<-exp-wellFounded′ (eₗ · eᵣ) <-·ₗ = <-exp-wellFounded eₗ
<-exp-wellFounded′ (eₗ · eᵣ) <-·ᵣ = <-exp-wellFounded eᵣ
<-exp-wellFounded′ (eₗ + eᵣ) <-+ₗ = <-exp-wellFounded eₗ
<-exp-wellFounded′ (eₗ + eᵣ) <-+ᵣ = <-exp-wellFounded eᵣ
<-exp-wellFounded′ (δ r e)   <-δ  = <-exp-wellFounded e

open import Data.Product.Relation.Binary.Lex.Strict  using (×-Lex; ×-wellFounded')

_<-φ-exp_ : Rel (Exp × Exp) 0ℓ
_<-φ-exp_ = ×-Lex (Eq._≡_ on count-φ) _<-φ_ _<-exp_

<-φ-respects-≡φ : _<-φ_ Relation.Binary.Respectsʳ (_≡_ on count-φ)
<-φ-respects-≡φ {x = x} {y} {z} ≡φ <φ with count-φ y with count-φ z
... | φy | φz = subst ((suc (count-φ x)) Data.Nat.≤′_) ≡φ <φ

<-φ-exp-wellFounded : WellFounded _<-φ-exp_
<-φ-exp-wellFounded = ×-wellFounded' Eq.trans (λ { {x = x} {y} {z} ≡φ <φ → subst ((suc (count-φ x)) Data.Nat.≤′_) ≡φ <φ }) <-φ-wellFounded <-exp-wellFounded

open Induction.WellFounded.All (<-φ-wellFounded) renaming (wfRec to <-φ-rec)

sm≤′m+sr : ∀ {m r} → suc m Data.Nat.≤′ (m Data.Nat.+ suc r)
sm≤′m+sr {m} {zero} rewrite Data.Nat.Properties.+-comm m 1 = Data.Nat.≤′-refl
sm≤′m+sr {m} {suc r} rewrite Data.Nat.Properties.+-comm m (suc (suc r)) rewrite Data.Nat.Properties.+-comm (suc r) m = Data.Nat.≤′-step sm≤′m+sr

sm≤′sm+r : ∀ {m r} → suc m Data.Nat.≤′ (suc r) Data.Nat.+ m
sm≤′sm+r {m} {zero} = Data.Nat.Properties.s≤′s Data.Nat.≤′-refl
sm≤′sm+r {m} {suc r} = Data.Nat.≤′-step sm≤′sm+r

<-φ-exp-·ₗ : ∀ {eₗ} {eᵣ} → (eₗ , eₗ) <-φ-exp (eₗ · eᵣ , eₗ · eᵣ)
<-φ-exp-·ₗ {eₗ} {eᵣ} with count-φ eᵣ
<-φ-exp-·ₗ {eₗ} {eᵣ} | zero = inj₂ (Data.Nat.Properties.+-comm 0 (count-φ eₗ) , <-·ₗ)
<-φ-exp-·ₗ {eₗ} {eᵣ} | suc φᵣ = inj₁ sm≤′m+sr

<-φ-exp-·ᵣ : ∀ {eₗ} {eᵣ} → (eᵣ , eᵣ) <-φ-exp (eₗ · eᵣ , eₗ · eᵣ)
<-φ-exp-·ᵣ {eₗ} {eᵣ} with count-φ eₗ
<-φ-exp-·ᵣ {eₗ} {eᵣ} | zero = inj₂ (refl , <-·ᵣ)
<-φ-exp-·ᵣ {eₗ} {eᵣ} | suc φₗ = inj₁ sm≤′sm+r

<-φ-exp-+ₗ : ∀ {eₗ} {eᵣ} → (eₗ , eₗ) <-φ-exp (eₗ + eᵣ , eₗ + eᵣ)
<-φ-exp-+ₗ {eₗ} {eᵣ} with count-φ eᵣ
<-φ-exp-+ₗ {eₗ} {eᵣ} | zero = inj₂ (Data.Nat.Properties.+-comm 0 (count-φ eₗ) , <-+ₗ)
<-φ-exp-+ₗ {eₗ} {eᵣ} | suc φᵣ = inj₁ sm≤′m+sr

<-φ-exp-+ᵣ : ∀ {eₗ} {eᵣ} → (eᵣ , eᵣ) <-φ-exp (eₗ + eᵣ , eₗ + eᵣ)
<-φ-exp-+ᵣ {eₗ} {eᵣ} with count-φ eₗ
<-φ-exp-+ᵣ {eₗ} {eᵣ} | zero = inj₂ (refl , <-+ᵣ)
<-φ-exp-+ᵣ {eₗ} {eᵣ} | suc φₗ = inj₁ sm≤′sm+r

instr′ : (p : Pat) (a : Act) (g : Gas) (l : ℕ) (e : Exp) → Acc _<-φ-exp_ (e , e) → ∃[ e′ ](count-φ e ≡ count-φ e′ × (p , a , g , l) ⊢ e ⇝ e′)
instr′ p a g l (` i) (Acc.acc rs) with (p matches? (` i))
instr′ p a g l (` i) (Acc.acc rs) | yes M = δ (a , g , l) (` i) , refl , I-`-⊤ M
instr′ p a g l (` i) (Acc.acc rs) | no ¬M = (` i) , refl , I-`-⊥ ¬M
instr′ p a g l (ƛ e) (Acc.acc rs) = ƛ e , refl , I-V V-ƛ
instr′ p a g l (eₗ · eᵣ) (Acc.acc rs) with (p matches? (eₗ · eᵣ)) with instr′ p a g l eₗ (rs <-φ-exp-·ₗ) with instr′ p a g l eᵣ (rs <-φ-exp-·ᵣ)
instr′ p a g l (eₗ · eᵣ) (Acc.acc rs) | yes M | eₗ′ , ≡ₗ , Iₗ | eᵣ′ , ≡ᵣ , Iᵣ rewrite ≡ₗ rewrite ≡ᵣ = (δ (a , g , l) (eₗ′ · eᵣ′)) , refl , (I-·-⊤ M Iₗ Iᵣ)
instr′ p a g l (eₗ · eᵣ) (Acc.acc rs) | no ¬M | eₗ′ , ≡ₗ , Iₗ | eᵣ′ , ≡ᵣ , Iᵣ rewrite ≡ₗ rewrite ≡ᵣ = eₗ′ · eᵣ′ , refl , I-·-⊥ ¬M Iₗ Iᵣ
instr′ p a g l (# n) (Acc.acc rs) = (# n) , refl , I-V V-#
instr′ p a g l (eₗ + eᵣ) (Acc.acc rs) with (p matches? (eₗ + eᵣ)) with instr′ p a g l eₗ (rs <-φ-exp-+ₗ) with instr′ p a g l eᵣ (rs <-φ-exp-+ᵣ)
instr′ p a g l (eₗ + eᵣ) (Acc.acc rs) | yes M | eₗ′ , ≡ₗ , Iₗ | eᵣ′ , ≡ᵣ , Iᵣ rewrite ≡ₗ rewrite ≡ᵣ = (δ (a , g , l) (eₗ′ + eᵣ′)) , refl , I-+-⊤ M Iₗ Iᵣ
instr′ p a g l (eₗ + eᵣ) (Acc.acc rs) | no ¬M | eₗ′ , ≡ₗ , Iₗ | eᵣ′ , ≡ᵣ , Iᵣ  rewrite ≡ₗ rewrite ≡ᵣ = eₗ′ + eᵣ′ , refl , I-+-⊥ ¬M Iₗ Iᵣ
instr′ p a g l (φ (p₀ , a₀ , g₀) e) (Acc.acc rs) with instr′ p a g l e (rs (inj₁ Data.Nat.≤′-refl))
instr′ p a g l (φ (p₀ , a₀ , g₀) e) (Acc.acc rs) | e′ , e≡φe′ , I′ with instr′ p₀ a₀ g₀ (Data.Nat.ℕ.suc l) e′ (rs (inj₁ (<-φ-subst {e} {e′} {(p₀ , a₀ , g₀)} e≡φe′)))
  where
    <-φ-subst : ∀ {e e′ f}
      → count-φ e ≡ count-φ e′
      → e′ <-φ φ f e
    <-φ-subst {e = e} {f = f} e≡φe′ = subst (_<′ Data.Nat.ℕ.suc (count-φ e)) e≡φe′ Data.Nat.≤′-refl
instr′ p a g l (φ (p₀ , a₀ , g₀) e) (Acc.acc rs) | e′ , e≡φe′ , I′ | e″ , e′≡φe″ , I″ = (φ (p₀ , a₀ , g₀) e″) , cong Data.Nat.ℕ.suc (trans e≡φe′ e′≡φe″) , I-φ I′ I″
instr′ p a g l (δ r e) (Acc.acc rs) with instr′ p a g l e (rs (inj₂ (refl , <-δ)))
instr′ p a g l (δ r e) (Acc.acc rs) | e′ , e≡e′ , I′ = δ r e′ , e≡e′ , I-δ I′

instr : (p : Pat) (a : Act) (g : Gas) (lvl : ℕ) (e : Exp) → Exp
instr p a g l e with instr′ p a g l e (<-φ-exp-wellFounded (e , e))
instr p a g l e | e′ , ≡φ = e′

⇝-instr : ∀ p a g l e
  → (p , a , g , l) ⊢ e ⇝ (instr p a g l e)
⇝-instr p a g l e with instr′ p a g l e (<-φ-exp-wellFounded (e , e))
⇝-instr p a g l e | e′ , ≡φ , I = I

-- decay ε
-- Decays 
decay : Ctx → Ctx
decay ∘ = ∘
decay (ε ·ₗ e) = (decay ε) ·ₗ e
decay (e ·ᵣ ε) = e ·ᵣ (decay ε)
decay (ε +ₗ e) = (decay ε) +ₗ e
decay (e +ᵣ ε) = e +ᵣ (decay ε)
decay (φ f  ε) = decay ε
decay (δ r  ε) = decay ε

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

  A-·-l : ∀ {act lvl εₗ eᵣ act′}
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

⊢⊣-select : ∀ {a l ε}
  → (a , l) ⊢ ε ⊣ (select a l ε)
⊢⊣-select {ε = ∘} = A-∘
⊢⊣-select {ε = ε ·ₗ e} = A-·-l ⊢⊣-select
⊢⊣-select {ε = e ·ᵣ ε} = A-·-r ⊢⊣-select
⊢⊣-select {ε = ε +ₗ e} = A-+-l ⊢⊣-select
⊢⊣-select {ε = e +ᵣ ε} = A-+-r ⊢⊣-select
⊢⊣-select {ε = φ f  ε} = A-φ ⊢⊣-select
⊢⊣-select {a = act} {l = lvl} {ε = δ (a , _ , l)  ε} with (l ≤? lvl)
... | yes ≤ = (A-Δ-≤ ≤) ⊢⊣-select
... | no  ≰ = A-Δ-> (≰⇒> ≰) ⊢⊣-select

data _⊢_⇥_ : Pat × Act × Gas × ℕ → Exp → Exp → Set where
  step : ∀ {p a g l e e′ e₀ e₀′ ε₀}
    → (D : instr p a g l e ⇒ ε₀ ⟨ e₀ ⟩)
    → (A : (a , l) ⊢ ε₀ ⊣ ∥)
    → (T : e₀ —→ e₀′)
    → (C : e′ ⇒ (decay ε₀) ⟨ e₀′ ⟩)
    → (p , a , g , l) ⊢ e ⇥ e′

  skip : ∀ {p a g l e e′ e″ e₀ e₀′ ε₀}
    → (D : instr p a g l e ⇒ ε₀ ⟨ e₀ ⟩)
    → (A : e₀ filter-like ⊎ (a , l) ⊢ ε₀ ⊣ ⊳)
    → (T : e₀ —→ e₀′)
    → (C : e′ ⇒ (decay ε₀) ⟨ e₀′ ⟩)
    → (R : (p , a , g , l) ⊢ e′ ⇥ e″)
    → (p , a , g , l) ⊢ e ⇥ e″

  done : ∀ {p a g l v}
    → v value
    → (p , a , g , l) ⊢ v ⇥ v
