module Preservation where

open import Base
open import Ctx using (compose; ∘; _·ₗ_; _·ᵣ_; _+ₗ_; _+ᵣ_; φ; δ)
open import Decompose using (ctx; _⊢_⇛_⊣_; _⟨_⟩)
open import Match using (strip-δ)
open import Recompose using (recompose)
open import Statics
open import Step
open import Substitution
open import Transition
open import Data.Nat using (ℕ; zero; suc; pred; _<_; _>_; <-cmp; s≤s; z≤n)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

insert : Ctx → ℕ → Typ → Ctx
insert Γ       zero    τ₀ = Γ ⸴ τ₀
insert ∅       (suc n) τ₀ = ∅
insert (Γ ⸴ τ) (suc n) τ₀ = insert Γ n τ₀ ⸴ τ

↑ₙ-preserve : ∀ {Γ τ₀ x c τ}
  → Γ ∋ x ∶ τ
  → insert Γ c τ₀ ∋ ↑ₙ c 1 x ∶ τ
↑ₙ-preserve {c = zero}  ∋       = ∋-S ∋
↑ₙ-preserve {c = suc c} ∋-Z     = ∋-Z
↑ₙ-preserve {c = suc c} (∋-S ∋) = ∋-S (↑ₙ-preserve ∋)

↑ₑ-preserve : ∀ {Γ e c τₑ τ₀}
  → Γ ⊢[ e ]∶ τₑ
  → insert Γ c τ₀ ⊢[ ↑ₑ c 1 e ]∶ τₑ
↑ₚ-preserve : ∀ {Γ p c τₚ τ₀}
  → Γ ⊢< p >∶ τₚ
  → insert Γ c τ₀ ⊢< ↑ₚ c 1 p >∶ τₚ

↑ₑ-preserve (⊢-` ∋)     = ⊢-` (↑ₙ-preserve ∋)
↑ₑ-preserve (⊢-ƛ ⊢ₑ)    = ⊢-ƛ (↑ₑ-preserve ⊢ₑ)
↑ₑ-preserve (⊢-· ⊢ₗ ⊢ᵣ) = ⊢-· (↑ₑ-preserve ⊢ₗ) (↑ₑ-preserve ⊢ᵣ)
↑ₑ-preserve (⊢-+ ⊢ₗ ⊢ᵣ) = ⊢-+ (↑ₑ-preserve ⊢ₗ) (↑ₑ-preserve ⊢ᵣ)
↑ₑ-preserve ⊢-#         = ⊢-#
↑ₑ-preserve (⊢-φ ⊢ₚ ⊢ₑ) = ⊢-φ (↑ₚ-preserve ⊢ₚ) (↑ₑ-preserve ⊢ₑ)
↑ₑ-preserve (⊢-δ ⊢ₑ)    = ⊢-δ (↑ₑ-preserve ⊢ₑ)
↑ₑ-preserve (⊢-μ ⊢ₑ)    = ⊢-μ (↑ₑ-preserve ⊢ₑ)

↑ₚ-preserve ⊢-E         = ⊢-E
↑ₚ-preserve ⊢-V         = ⊢-V
↑ₚ-preserve (⊢-` ∋)     = ⊢-` (↑ₙ-preserve ∋)
↑ₚ-preserve (⊢-ƛ ⊢ₚ)    = ⊢-ƛ (↑ₚ-preserve ⊢ₚ)
↑ₚ-preserve (⊢-· ⊢ₗ ⊢ᵣ) = ⊢-· (↑ₚ-preserve ⊢ₗ) (↑ₚ-preserve ⊢ᵣ)
↑ₚ-preserve ⊢-#         = ⊢-#
↑ₚ-preserve (⊢-+ ⊢ₗ ⊢ᵣ) = ⊢-+ (↑ₚ-preserve ⊢ₗ) (↑ₚ-preserve ⊢ᵣ)
↑ₚ-preserve (⊢-μ ⊢ₚ)    = ⊢-μ (↑ₚ-preserve ⊢ₚ)

insert-preserve-< : ∀ {Γ x τᵥ i τᵢ}
  → i < x
  → insert Γ x τᵥ ∋ i ∶ τᵢ
  → Γ ∋ i ∶ τᵢ
insert-preserve-< {Γ ⸴ τ₀} {x = suc x} {i = zero} (s≤s z≤n) ∋-Z = ∋-Z
insert-preserve-< {Γ ⸴ τ₀} {x = suc (suc x)} {i = suc i} (s≤s (s≤s <)) (∋-S ∋) =
  ∋-S (insert-preserve-< (s≤s <) ∋)

insert-preserve-≡ : ∀ {Γ τᵥ i τᵢ}
  → insert Γ i τᵥ ∋ i ∶ τᵢ
  → τᵥ ≡ τᵢ
insert-preserve-≡ {∅}     {i = zero}  ∋-Z     = refl
insert-preserve-≡ {Γ ⸴ τ} {i = zero}  ∋-Z     = refl
insert-preserve-≡ {Γ ⸴ τ} {i = suc i} (∋-S ∋) = insert-preserve-≡ ∋

insert-preserve-> : ∀ {Γ x τᵥ i τᵢ}
  → i > x
  → insert Γ x τᵥ ∋ i ∶ τᵢ
  → Γ ∋ pred i ∶ τᵢ
insert-preserve-> {Γ} {x = zero} {i = suc i} (s≤s z≤n) (∋-S ∋) = ∋
insert-preserve-> {Γ ⸴ τ₀} {x = suc x} {i = suc (suc i)} (s≤s (s≤s >)) (∋-S ∋) =
  ∋-S (insert-preserve-> (s≤s >) ∋)

applyₙ-preserve : ∀ {Γ v i x τᵥ τᵢ}
  → Γ ⊢[ v ]∶ τᵥ
  → insert Γ x τᵥ ∋ i ∶ τᵢ
  → Γ ⊢[ applyₙ i x v ]∶ τᵢ
applyₙ-preserve {i = i} {x = x} ⊢ᵥ ∋ with <-cmp i x
... | tri< i<x _ _ = ⊢-` (insert-preserve-< i<x ∋)
... | tri≈ _ refl _ rewrite insert-preserve-≡ ∋ = ⊢ᵥ
applyₙ-preserve ⊢ᵥ ∋ | tri> _ _ (s≤s i>x) = ⊢-` (insert-preserve-> (s≤s i>x) ∋)

patternize-preserve : ∀ {Γ e τ}
  → Γ ⊢[ e ]∶ τ
  → Γ ⊢< patternize e >∶ τ
patternize-preserve (⊢-` ∋)     = ⊢-` ∋
patternize-preserve (⊢-ƛ ⊢ₑ)    = ⊢-ƛ (patternize-preserve ⊢ₑ)
patternize-preserve (⊢-· ⊢ₗ ⊢ᵣ) = ⊢-· (patternize-preserve ⊢ₗ) (patternize-preserve ⊢ᵣ)
patternize-preserve (⊢-+ ⊢ₗ ⊢ᵣ) = ⊢-+ (patternize-preserve ⊢ₗ) (patternize-preserve ⊢ᵣ)
patternize-preserve ⊢-#         = ⊢-#
patternize-preserve (⊢-φ _ ⊢ₑ)  = patternize-preserve ⊢ₑ
patternize-preserve (⊢-δ ⊢ₑ)    = patternize-preserve ⊢ₑ
patternize-preserve (⊢-μ ⊢ₑ)    = ⊢-μ (patternize-preserve ⊢ₑ)

applyₑ-preserve : ∀ {Γ e v x τᵥ τ}
  → Γ ⊢[ v ]∶ τᵥ
  → insert Γ x τᵥ ⊢[ e ]∶ τ
  → Γ ⊢[ applyₑ e x v ]∶ τ
applyₚ-preserve : ∀ {Γ p v x τᵥ τ}
  → Γ ⊢[ v ]∶ τᵥ
  → insert Γ x τᵥ ⊢< p >∶ τ
  → Γ ⊢< applyₚ p x v >∶ τ

applyₑ-preserve ⊢ᵥ (⊢-` ∋)     = applyₙ-preserve ⊢ᵥ ∋
applyₑ-preserve ⊢ᵥ (⊢-ƛ ⊢ₑ)    = ⊢-ƛ (applyₑ-preserve (↑ₑ-preserve {c = 0} ⊢ᵥ) ⊢ₑ)
applyₑ-preserve ⊢ᵥ (⊢-· ⊢ₗ ⊢ᵣ) = ⊢-· (applyₑ-preserve ⊢ᵥ ⊢ₗ) (applyₑ-preserve ⊢ᵥ ⊢ᵣ)
applyₑ-preserve ⊢ᵥ (⊢-+ ⊢ₗ ⊢ᵣ) = ⊢-+ (applyₑ-preserve ⊢ᵥ ⊢ₗ) (applyₑ-preserve ⊢ᵥ ⊢ᵣ)
applyₑ-preserve ⊢ᵥ ⊢-#         = ⊢-#
applyₑ-preserve ⊢ᵥ (⊢-φ ⊢ₚ ⊢ₑ) = ⊢-φ (applyₚ-preserve ⊢ᵥ ⊢ₚ) (applyₑ-preserve ⊢ᵥ ⊢ₑ)
applyₑ-preserve ⊢ᵥ (⊢-δ ⊢ₑ)    = ⊢-δ (applyₑ-preserve ⊢ᵥ ⊢ₑ)
applyₑ-preserve ⊢ᵥ (⊢-μ ⊢ₑ)    = ⊢-μ (applyₑ-preserve (↑ₑ-preserve {c = 0} ⊢ᵥ) ⊢ₑ)

applyₚ-preserve ⊢ᵥ ⊢-E         = ⊢-E
applyₚ-preserve ⊢ᵥ ⊢-V         = ⊢-V
applyₚ-preserve ⊢ᵥ (⊢-` ∋)     = patternize-preserve (applyₙ-preserve ⊢ᵥ ∋)
applyₚ-preserve ⊢ᵥ (⊢-ƛ ⊢ₚ)    = ⊢-ƛ (applyₚ-preserve (↑ₑ-preserve {c = 0} ⊢ᵥ) ⊢ₚ)
applyₚ-preserve ⊢ᵥ (⊢-· ⊢ₗ ⊢ᵣ) = ⊢-· (applyₚ-preserve ⊢ᵥ ⊢ₗ) (applyₚ-preserve ⊢ᵥ ⊢ᵣ)
applyₚ-preserve ⊢ᵥ ⊢-#         = ⊢-#
applyₚ-preserve ⊢ᵥ (⊢-+ ⊢ₗ ⊢ᵣ) = ⊢-+ (applyₚ-preserve ⊢ᵥ ⊢ₗ) (applyₚ-preserve ⊢ᵥ ⊢ᵣ)
applyₚ-preserve ⊢ᵥ (⊢-μ ⊢ₚ)    = ⊢-μ (applyₚ-preserve (↑ₑ-preserve {c = 0} ⊢ᵥ) ⊢ₚ)

—→-preserve : ∀ {Γ r r′ τ}
  → Γ ⊢[ r ]∶ τ
  → r —→ r′
  → Γ ⊢[ r′ ]∶ τ
—→-preserve (⊢-· (⊢-ƛ ⊢ₑ) ⊢ᵥ) (T-β-· _) = applyₑ-preserve ⊢ᵥ ⊢ₑ
—→-preserve (⊢-+ ⊢-# ⊢-#) T-β-+       = ⊢-#
—→-preserve (⊢-φ _ ⊢ₑ) (T-β-φ _)       = ⊢ₑ
—→-preserve (⊢-δ ⊢ₑ) (T-β-δ _)         = ⊢ₑ
—→-preserve (⊢-μ ⊢ₑ) T-β-μ             = applyₑ-preserve (⊢-μ ⊢ₑ) ⊢ₑ

strip-δ-preserve : ∀ {Γ e τ}
  → Γ ⊢[ e ]∶ τ
  → Γ ⊢[ strip-δ e ]∶ τ
strip-δ-preserve (⊢-` ∋)     = ⊢-` ∋
strip-δ-preserve (⊢-ƛ ⊢ₑ)    = ⊢-ƛ (strip-δ-preserve ⊢ₑ)
strip-δ-preserve (⊢-· ⊢ₗ ⊢ᵣ) = ⊢-· (strip-δ-preserve ⊢ₗ) (strip-δ-preserve ⊢ᵣ)
strip-δ-preserve (⊢-+ ⊢ₗ ⊢ᵣ) = ⊢-+ (strip-δ-preserve ⊢ₗ) (strip-δ-preserve ⊢ᵣ)
strip-δ-preserve ⊢-#         = ⊢-#
strip-δ-preserve (⊢-φ ⊢ₚ ⊢ₑ) = ⊢-φ ⊢ₚ (strip-δ-preserve ⊢ₑ)
strip-δ-preserve (⊢-δ ⊢ₑ)    = strip-δ-preserve ⊢ₑ
strip-δ-preserve (⊢-μ ⊢ₑ)    = ⊢-μ (strip-δ-preserve ⊢ₑ)

strip-δ-reflect : ∀ {Γ} e {τ}
  → Γ ⊢[ strip-δ e ]∶ τ
  → Γ ⊢[ e ]∶ τ
strip-δ-reflect (` x)    ⊢           = ⊢
strip-δ-reflect (ƛ e)    (⊢-ƛ ⊢ₑ)    = ⊢-ƛ (strip-δ-reflect e ⊢ₑ)
strip-δ-reflect (l `· r) (⊢-· ⊢ₗ ⊢ᵣ) = ⊢-· (strip-δ-reflect l ⊢ₗ) (strip-δ-reflect r ⊢ᵣ)
strip-δ-reflect (# n)    ⊢           = ⊢
strip-δ-reflect (l `+ r) (⊢-+ ⊢ₗ ⊢ᵣ) = ⊢-+ (strip-δ-reflect l ⊢ₗ) (strip-δ-reflect r ⊢ᵣ)
strip-δ-reflect (φ f e)  (⊢-φ ⊢ₚ ⊢ₑ) = ⊢-φ ⊢ₚ (strip-δ-reflect e ⊢ₑ)
strip-δ-reflect (δ r e)  ⊢           = ⊢-δ (strip-δ-reflect e ⊢)
strip-δ-reflect (μ e)    (⊢-μ ⊢ₑ)    = ⊢-μ (strip-δ-reflect e ⊢ₑ)

⇛-preserve : ∀ {Φ s e C′ r t τ}
  → (Φ , s) ⊢ e ⇛ C′ ⟨ r ⟩ ⊣ t
  → ∅ ⊢[ compose (ctx s) e ]∶ τ
  → ∅ ⊢[ compose C′ r ]∶ τ
⇛-preserve {C′ = C′} {r = r} {τ = τ} D ⊢ =
  strip-δ-reflect (compose C′ r)
    (subst (λ e → ∅ ⊢[ e ]∶ τ) (sym (recompose D)) (strip-δ-preserve ⊢))

compose-preserve : ∀ C {Γ e τ}
  → Γ ⊢[ compose C e ]∶ τ
  → ∃[ τₕ ] Γ ⊢[ e ]∶ τₕ × (∀ {e′} → Γ ⊢[ e′ ]∶ τₕ → Γ ⊢[ compose C e′ ]∶ τ)
compose-preserve ∘ ⊢ = _ , ⊢ , λ ⊢′ → ⊢′
compose-preserve (c ·ₗ r) ⊢ with compose-preserve c ⊢
... | _ , ⊢-· ⊢ₗ ⊢ᵣ , plug = _ , ⊢ₗ , λ ⊢′ → plug (⊢-· ⊢′ ⊢ᵣ)
compose-preserve (l ·ᵣ c) ⊢ with compose-preserve c ⊢
... | _ , ⊢-· ⊢ₗ ⊢ᵣ , plug = _ , ⊢ᵣ , λ ⊢′ → plug (⊢-· ⊢ₗ ⊢′)
compose-preserve (c +ₗ r) ⊢ with compose-preserve c ⊢
... | _ , ⊢-+ ⊢ₗ ⊢ᵣ , plug = _ , ⊢ₗ , λ ⊢′ → plug (⊢-+ ⊢′ ⊢ᵣ)
compose-preserve (l +ᵣ c) ⊢ with compose-preserve c ⊢
... | _ , ⊢-+ ⊢ₗ ⊢ᵣ , plug = _ , ⊢ᵣ , λ ⊢′ → plug (⊢-+ ⊢ₗ ⊢′)
compose-preserve (φ f c) ⊢ with compose-preserve c ⊢
... | _ , ⊢-φ ⊢ₚ ⊢ₑ , plug = _ , ⊢ₑ , λ ⊢′ → plug (⊢-φ ⊢ₚ ⊢′)
compose-preserve (δ r c) ⊢ with compose-preserve c ⊢
... | _ , ⊢-δ ⊢ₑ , plug = _ , ⊢ₑ , λ ⊢′ → plug (⊢-δ ⊢′)

transition-preserve : ∀ C {r r′ τ}
  → ∅ ⊢[ compose C r ]∶ τ
  → r —→ r′
  → ∅ ⊢[ compose C r′ ]∶ τ
transition-preserve C ⊢ T with compose-preserve C ⊢
... | _ , ⊢ᵣ , plug = plug (—→-preserve ⊢ᵣ T)

⇥-preserve : ∀ {e e′ τ}
  → ∅ ⊢[ e ]∶ τ
  → e ⇥ e′
  → ∅ ⊢[ e′ ]∶ τ
⇥-preserve ⊢ (S-Step {C = C} D _ T) = transition-preserve C (⇛-preserve D ⊢) T
⇥-preserve ⊢ (S-Skip {C = C} D T S) =
  ⇥-preserve (transition-preserve C (⇛-preserve D ⊢) T) S
⇥-preserve ⊢ (S-Value _) = ⊢
