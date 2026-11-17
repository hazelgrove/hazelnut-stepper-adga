module Simulation where

open import Base
open import Ctx
open import Match using (strip; _matches?_)
open import Decompose
open import Substitution using (↑ₑ; applyₙ; applyₑ)
open import Transition
open import Step
open import Data.List using ([]; _∷_; length)
open import Data.Nat using (suc; <-cmp; _≤?_; s≤s)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_; _◅◅_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; subst; sym; trans)
open import Relation.Nullary using (yes; no)

infix 0 _⊢_⇒_

data _⊢_⇒_ : Ctx → Exp → Obj → Set where
  D-ξ-·ₗ : ∀ {C eₗ eᵣ o} → (C ·ₗ eᵣ) ⊢ eₗ ⇒ o → C ⊢ eₗ `· eᵣ ⇒ o
  D-ξ-·ᵣ : ∀ {C eₗ eᵣ o} → (eₗ ·ᵣ C) ⊢ eᵣ ⇒ o → C ⊢ eₗ `· eᵣ ⇒ o
  D-β-·  : ∀ {C vₗ vᵣ} → vₗ value → vᵣ value → C ⊢ vₗ `· vᵣ ⇒ C ⟨ vₗ `· vᵣ ⟩
  D-ξ-+ₗ : ∀ {C eₗ eᵣ o} → (C +ₗ eᵣ) ⊢ eₗ ⇒ o → C ⊢ eₗ `+ eᵣ ⇒ o
  D-ξ-+ᵣ : ∀ {C eₗ eᵣ o} → (eₗ +ᵣ C) ⊢ eᵣ ⇒ o → C ⊢ eₗ `+ eᵣ ⇒ o
  D-β-+  : ∀ {C vₗ vᵣ} → vₗ value → vᵣ value → C ⊢ vₗ `+ vᵣ ⇒ C ⟨ vₗ `+ vᵣ ⟩
  D-β-μ  : ∀ {C e} → C ⊢ μ e ⇒ C ⟨ μ e ⟩

infix 0 _⊢_↦_

data _⊢_↦_ : Ctx → Exp → Exp → Set where
  J-Step : ∀ {K e C r r′}
    → (D : K ⊢ e ⇒ C ⟨ r ⟩)
    → (T : r —→ r′)
    → K ⊢ e ↦ compose C r′

infix 0 _↦_ _↦*_

_↦_ : Exp → Exp → Set
e ↦ e′ = ∘ ⊢ e ↦ e′

_↦*_ : Exp → Exp → Set
_↦*_ = Star _↦_

stripᶜ : Ctx → Ctx
stripᶜ ∘        = ∘
stripᶜ (c ·ₗ r) = stripᶜ c ·ₗ strip r
stripᶜ (l ·ᵣ c) = strip l ·ᵣ stripᶜ c
stripᶜ (c +ₗ r) = stripᶜ c +ₗ strip r
stripᶜ (l +ᵣ c) = strip l +ᵣ stripᶜ c
stripᶜ (φ f c)  = stripᶜ c
stripᶜ (δ r c)  = stripᶜ c

strip-compose : ∀ C e → strip (compose C e) ≡ compose (stripᶜ C) (strip e)
strip-compose ∘        e = refl
strip-compose (c ·ₗ r) e = strip-compose c _
strip-compose (l ·ᵣ c) e = strip-compose c _
strip-compose (c +ₗ r) e = strip-compose c _
strip-compose (l +ᵣ c) e = strip-compose c _
strip-compose (φ f c)  e = strip-compose c _
strip-compose (δ r c)  e = strip-compose c _

strip-value : ∀ {v} → v value → strip v value
strip-value V-ƛ = V-ƛ
strip-value V-# = V-#

↑ₑ-strip : ∀ c d e → strip (↑ₑ c d e) ≡ ↑ₑ c d (strip e)
↑ₑ-strip c d (` x)    = refl
↑ₑ-strip c d (ƛ e)    = cong ƛ_ (↑ₑ-strip (suc c) d e)
↑ₑ-strip c d (l `· r) = cong₂ _`·_ (↑ₑ-strip c d l) (↑ₑ-strip c d r)
↑ₑ-strip c d (# n)    = refl
↑ₑ-strip c d (l `+ r) = cong₂ _`+_ (↑ₑ-strip c d l) (↑ₑ-strip c d r)
↑ₑ-strip c d (φ f e)  = ↑ₑ-strip c d e
↑ₑ-strip c d (δ r e)  = ↑ₑ-strip c d e
↑ₑ-strip c d (μ e)    = cong μ (↑ₑ-strip (suc c) d e)

applyₙ-strip : ∀ i x v → strip (applyₙ i x v) ≡ applyₙ i x (strip v)
applyₙ-strip i x v with <-cmp i x
applyₙ-strip i       x v | tri< _ _ _       = refl
applyₙ-strip i       x v | tri≈ _ _ _       = refl
applyₙ-strip (suc i) x v | tri> _ _ (s≤s _) = refl

applyₑ-strip : ∀ e x v → strip (applyₑ e x v) ≡ applyₑ (strip e) x (strip v)
applyₑ-strip (` i)    x v = applyₙ-strip i x v
applyₑ-strip (ƛ e)    x v =
  cong ƛ_ (trans (applyₑ-strip e (suc x) (↑ₑ 0 1 v))
                 (cong (applyₑ (strip e) (suc x)) (↑ₑ-strip 0 1 v)))
applyₑ-strip (l `· r) x v = cong₂ _`·_ (applyₑ-strip l x v) (applyₑ-strip r x v)
applyₑ-strip (# n)    x v = refl
applyₑ-strip (l `+ r) x v = cong₂ _`+_ (applyₑ-strip l x v) (applyₑ-strip r x v)
applyₑ-strip (φ f e)  x v = applyₑ-strip e x v
applyₑ-strip (δ r e)  x v = applyₑ-strip e x v
applyₑ-strip (μ e)    x v =
  cong μ (trans (applyₑ-strip e (suc x) (↑ₑ 0 1 v))
                (cong (applyₑ (strip e) (suc x)) (↑ₑ-strip 0 1 v)))

lookup-stripᶜ : ∀ Φ e s → stripᶜ (ctx (lookup Φ e s)) ≡ stripᶜ (ctx s)
lookup-stripᶜ [] e s = refl
lookup-stripᶜ ((p , b , g) ∷ Φ) e (state a l i C) with suc (length Φ) ≤? i
... | yes _ = refl
... | no  _ with p matches? e
...   | no  _ = lookup-stripᶜ Φ e (state a l i C)
...   | yes _ with g | bump (a , l) (b , suc (length Φ))
...     | 𝟙 | (a′ , l′) = lookup-stripᶜ Φ e (state a′ l′ i C)
...     | ⋆ | (a′ , l′) = refl

lookup-stripᶜ′ : ∀ Φ {e s s′}
  → lookup Φ e s ≡ s′ → stripᶜ (ctx s′) ≡ stripᶜ (ctx s)
lookup-stripᶜ′ Φ {e} {s} L =
  subst (λ C′ → stripᶜ C′ ≡ stripᶜ (ctx s)) (cong ctx L) (lookup-stripᶜ Φ e s)

keep-stripᶜ : ∀ i r C → stripᶜ (keep i r C) ≡ stripᶜ C
keep-stripᶜ i (b , n) C with n ≤? i
... | yes _ = refl
... | no  _ = refl

Sim : Ctx → Exp → Exp → Set
Sim K e e′ = (e′ ≡ compose K e) ⊎ (K ⊢ e ↦ e′)

private
  retarget : ∀ {K K′ e e′} → K ≡ K′ → Sim K e e′ → Sim K′ e e′
  retarget refl s = s

  under-·ₗ : ∀ {K e r e′} → Sim (K ·ₗ r) e e′ → Sim K (e `· r) e′
  under-·ₗ (inj₁ eq) = inj₁ eq
  under-·ₗ (inj₂ (J-Step D T)) = inj₂ (J-Step (D-ξ-·ₗ D) T)

  under-·ᵣ : ∀ {K l e e′} → Sim (l ·ᵣ K) e e′ → Sim K (l `· e) e′
  under-·ᵣ (inj₁ eq) = inj₁ eq
  under-·ᵣ (inj₂ (J-Step D T)) = inj₂ (J-Step (D-ξ-·ᵣ D) T)

  under-+ₗ : ∀ {K e r e′} → Sim (K +ₗ r) e e′ → Sim K (e `+ r) e′
  under-+ₗ (inj₁ eq) = inj₁ eq
  under-+ₗ (inj₂ (J-Step D T)) = inj₂ (J-Step (D-ξ-+ₗ D) T)

  under-+ᵣ : ∀ {K l e e′} → Sim (l +ᵣ K) e e′ → Sim K (l `+ e) e′
  under-+ᵣ (inj₁ eq) = inj₁ eq
  under-+ᵣ (inj₂ (J-Step D T)) = inj₂ (J-Step (D-ξ-+ᵣ D) T)

  β-· : ∀ {K e v} → v value → Sim K (strip (ƛ e) `· strip v) (compose K (strip (applyₑ e 0 v)))
  β-· {K} {e} {v} V =
    inj₂ (subst (λ x → K ⊢ strip (ƛ e) `· strip v ↦ compose K x)
      (sym (applyₑ-strip e 0 v))
      (J-Step (D-β-· V-ƛ (strip-value V)) (T-β-· {e = strip e} (strip-value V))))

  β-μ : ∀ {K e} → Sim K (μ (strip e)) (compose K (strip (applyₑ e 0 (μ e))))
  β-μ {K} {e} =
    inj₂ (subst (λ x → K ⊢ μ (strip e) ↦ compose K x)
      (sym (applyₑ-strip e 0 (μ e)))
      (J-Step D-β-μ (T-β-μ {e = strip e})))

⇛-sim : ∀ {Φ s e C′ r r′ t}
  → (Φ , s) ⊢ e ⇛ C′ ⟨ r ⟩ ⊣ t
  → r —→ r′
  → Sim (stripᶜ (ctx s)) (strip e) (compose (stripᶜ C′) (strip r′))
⇛-sim {Φ} (D-ξ-·ₗ {eᵣ = eᵣ} L D) T =
  under-·ₗ (retarget (cong (_·ₗ strip eᵣ) (lookup-stripᶜ′ Φ L)) (⇛-sim D T))
⇛-sim {Φ} (D-ξ-·ᵣ {eₗ = eₗ} L D) T =
  under-·ᵣ (retarget (cong (strip eₗ ·ᵣ_) (lookup-stripᶜ′ Φ L)) (⇛-sim D T))
⇛-sim {Φ} (D-β-· _ _ L) (T-β-· {e = e} V) =
  retarget (lookup-stripᶜ′ Φ L) (β-· {e = e} V)
⇛-sim {Φ} (D-ξ-+ₗ {eᵣ = eᵣ} L D) T =
  under-+ₗ (retarget (cong (_+ₗ strip eᵣ) (lookup-stripᶜ′ Φ L)) (⇛-sim D T))
⇛-sim {Φ} (D-ξ-+ᵣ {eₗ = eₗ} L D) T =
  under-+ᵣ (retarget (cong (strip eₗ +ᵣ_) (lookup-stripᶜ′ Φ L)) (⇛-sim D T))
⇛-sim {Φ} (D-β-+ _ _ L) T-β-+ =
  retarget (lookup-stripᶜ′ Φ L) (inj₂ (J-Step (D-β-+ V-# V-#) T-β-+))
⇛-sim (D-ξ-φ D) T = ⇛-sim D T
⇛-sim (D-β-φ _) (T-β-φ _) = inj₁ refl
⇛-sim {s = s} (D-ξ-δ {b = b} {n = n} _ D) T =
  retarget (keep-stripᶜ (ins-lvl s) (b , n) (ctx s)) (⇛-sim D T)
⇛-sim (D-β-δ _ _) (T-β-δ _) = inj₁ refl
⇛-sim {Φ} (D-β-μ {e = e} L) T-β-μ = retarget (lookup-stripᶜ′ Φ L) (β-μ {e = e})

transition-sim : ∀ {e C r r′ t}
  → top ⊢ e ⇛ C ⟨ r ⟩ ⊣ t
  → r —→ r′
  → strip e ↦* strip (compose C r′)
transition-sim {C = C} {r′ = r′} D T
  rewrite strip-compose C r′
  with ⇛-sim D T
... | inj₁ eq rewrite eq = ε
... | inj₂ S = S ◅ ε

sim : ∀ {e e′} → e ⇥ e′ → strip e ↦* strip e′
sim (S-Step D _ T) = transition-sim D T
sim (S-Skip D T S) = transition-sim D T ◅◅ sim S
sim (S-Value _) = ε
