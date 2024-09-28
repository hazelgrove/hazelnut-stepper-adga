module Preservation where

open import Base
open import Dynamics
open import Statics
open import Match
open import Substitution
open import Data.Nat using (ℕ; _≤_; _<?_; _<_; _≥_; zero; suc; s≤s; z≤n; <-cmp; s<s; z<s; pred; _>_)
open import Data.Nat.Properties using (≮⇒≥; ≤-trans)
open import Relation.Binary using (tri<; tri>; tri≈)
open import Data.List using (List)
open import Relation.Nullary using (yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; _≡_; cong; cong₂; subst; subst₂; sym)

strip-preserve : ∀ {Γ e τ}
  → Γ ⊢ e ∶ τ
  → Γ ⊢ (strip e) ∶ τ
strip-preserve (⊢-` ∋-x)   = ⊢-` ∋-x
strip-preserve (⊢-ƛ ⊢ₑ)   = ⊢-ƛ (strip-preserve ⊢ₑ)
strip-preserve (⊢-· ⊢ₗ ⊢ᵣ) = ⊢-· (strip-preserve ⊢ₗ) (strip-preserve ⊢ᵣ)
strip-preserve (⊢-+ ⊢ₗ ⊢ᵣ) = ⊢-+ (strip-preserve ⊢ₗ) (strip-preserve ⊢ᵣ)
strip-preserve ⊢-#         = ⊢-#
strip-preserve (⊢-φ ⊢ₚ ⊢ₑ) = strip-preserve ⊢ₑ
strip-preserve (⊢-δ ⊢ₑ)    = strip-preserve ⊢ₑ
strip-preserve (⊢-μ ⊢ₑ)    = ⊢-μ (strip-preserve ⊢ₑ)

⇝-preserve : ∀ {Γ s e₁ e₂ τ}
  → Γ ⊢ e₁ ∶ τ
  → s ⊢ e₁ ⇝ e₂
  → Γ ⊢ e₂ ∶ τ
⇝-preserve (⊢-ƛ ⊢) (I-V V) = ⊢-ƛ ⊢
⇝-preserve (⊢-#) (I-V V) = ⊢-#
⇝-preserve (⊢-` ∋) (I-`) = ⊢-` ∋
⇝-preserve (⊢-· ⊢ₗ ⊢ᵣ) (I-·-⊤ M Iₗ Iᵣ) = ⊢-δ (⊢-· (⇝-preserve ⊢ₗ Iₗ) (⇝-preserve ⊢ᵣ Iᵣ))
⇝-preserve (⊢-· ⊢ₗ ⊢ᵣ) (I-·-⊥ M Iₗ Iᵣ) = ⊢-· (⇝-preserve ⊢ₗ Iₗ) (⇝-preserve ⊢ᵣ Iᵣ)
⇝-preserve (⊢-+ ⊢ₗ ⊢ᵣ) (I-+-⊤ M Iₗ Iᵣ) = ⊢-δ (⊢-+ (⇝-preserve ⊢ₗ Iₗ) (⇝-preserve ⊢ᵣ Iᵣ))
⇝-preserve (⊢-+ ⊢ₗ ⊢ᵣ) (I-+-⊥ M Iₗ Iᵣ) = ⊢-+ (⇝-preserve ⊢ₗ Iₗ) (⇝-preserve ⊢ᵣ Iᵣ)
⇝-preserve (⊢-φ ⊢ₚ ⊢ₑ) (I-φ I₀ I₁) = ⊢-φ ⊢ₚ (⇝-preserve (⇝-preserve ⊢ₑ I₀) I₁)
⇝-preserve (⊢-δ ⊢) (I-δ I) = ⊢-δ (⇝-preserve ⊢ I)
⇝-preserve (⊢-μ ⊢) (I-μ) = ⊢-μ ⊢

⇐-preserve : ∀ {Γ} {e e′ e₀ e₀′ : Exp} {τ} {ε : Dynamics.Ctx}
  → Γ ⊢ e ∶ τ
  → e ⇒ ε ⟨ e₀ ⟩
  → (∀ {Γ} {τ₀} → Γ ⊢ e₀ ∶ τ₀ → Γ ⊢ e₀′ ∶ τ₀)
  → e′ ⇐ (decay ε) ⟨ e₀′ ⟩
  → Γ ⊢ e′ ∶ τ
⇐-preserve (⊢-· ⊢ₗ ⊢ᵣ) (D-ξ-·ₗ D) P₀ (C-·ₗ C) = ⊢-· (⇐-preserve ⊢ₗ D P₀ C) ⊢ᵣ
⇐-preserve (⊢-· ⊢ₗ ⊢ᵣ) (D-ξ-·ᵣ V D) P₀ (C-·ᵣ C) = ⊢-· ⊢ₗ (⇐-preserve ⊢ᵣ D P₀ C)
⇐-preserve (⊢-· ⊢ₗ ⊢ᵣ) (D-β-· Vₗ Vᵣ) P₀ (C-∘) = P₀ (⊢-· ⊢ₗ ⊢ᵣ)
⇐-preserve (⊢-+ ⊢ₗ ⊢ᵣ) (D-ξ-+ₗ D) P₀ (C-+ₗ C) = ⊢-+ (⇐-preserve ⊢ₗ D P₀ C) ⊢ᵣ
⇐-preserve (⊢-+ ⊢ₗ ⊢ᵣ) (D-ξ-+ᵣ V D) P₀ (C-+ᵣ C) = ⊢-+ ⊢ₗ (⇐-preserve ⊢ᵣ D P₀ C)
⇐-preserve (⊢-+ ⊢ₗ ⊢ᵣ) (D-β-+ Vₗ Vᵣ) P₀ (C-∘) = P₀ (⊢-+ ⊢ₗ ⊢ᵣ)
⇐-preserve (⊢-φ ⊢ₚ ⊢ₑ) (D-ξ-φ D) P₀ (C-φ C) = ⊢-φ ⊢ₚ (⇐-preserve ⊢ₑ D P₀ C)
⇐-preserve (⊢-φ ⊢ₚ ⊢ₑ) (D-β-φ V) P₀ (C-∘) = P₀ (⊢-φ ⊢ₚ ⊢ₑ)
⇐-preserve (⊢-δ {r = a , 𝟙 , l} ⊢) (D-ξ-δ D) P₀ C = ⇐-preserve ⊢ D P₀ C
⇐-preserve (⊢-δ {r = a , ⋆ , l} ⊢) (D-ξ-δ D) P₀ (C-δ C) = ⊢-δ (⇐-preserve ⊢ D P₀ C)
⇐-preserve (⊢-δ {r = a , 𝟙 , l} ⊢) (D-β-δ V) P₀ (C-∘) = P₀ (⊢-δ ⊢)
⇐-preserve (⊢-δ {r = a , ⋆ , l} ⊢) (D-β-δ V) P₀ (C-∘) = P₀ (⊢-δ ⊢)
⇐-preserve (⊢-μ ⊢) (D-β-μ) P₀ (C-∘) = P₀ (⊢-μ ⊢)

insert-preserve-> : ∀ {Γ x τᵥ i τᵢ}
  → (i > x)
  → (insert Γ x τᵥ) ∋ i ∶ τᵢ
  → Γ ∋ pred i ∶ τᵢ
insert-preserve-> {Γ} {x = zero} {i = suc i} (s≤s z≤n) (∋-S ∋) = ∋
insert-preserve-> {Γ ⸴ τ₀} {x = suc x} {i = suc (suc i)} (s≤s (s≤s >)) (∋-S ∋) = ∋-S (insert-preserve-> (s≤s >) ∋)

insert-preserve-≡ : ∀ {Γ} {τᵥ} {i : ℕ} {τᵢ}
  → (insert Γ i τᵥ) ∋ i ∶ τᵢ
  → τᵥ ≡ τᵢ
insert-preserve-≡ {∅} {i = zero} ∋-Z = refl
insert-preserve-≡ {Γ ⸴ τ} {i = zero} ∋-Z = refl
insert-preserve-≡ {Γ ⸴ τ} {i = suc i} (∋-S ∋) = insert-preserve-≡ ∋

insert-preserve-< : ∀ {Γ x τᵥ i τᵢ}
  → (i < x)
  → (insert Γ x τᵥ) ∋ i ∶ τᵢ
  → Γ ∋ i ∶ τᵢ
insert-preserve-< {Γ ⸴ τ₀} {x = suc x} {i = zero} (s≤s z≤n) ∋-Z = ∋-Z
insert-preserve-< {Γ ⸴ τ₀} {x = suc (suc x)} {i = suc i} (s≤s (s≤s <)) (∋-S ∋) = ∋-S (insert-preserve-< (s≤s <) ∋)

applyₙ-preserve : ∀ {Γ} {v : Exp} {i x : ℕ} {τᵥ τᵢ}
  → Γ ⊢ v ∶ τᵥ
  → (insert Γ x τᵥ) ∋ i ∶ τᵢ
  → Γ ⊢ applyₙ i x v ∶ τᵢ
applyₙ-preserve {Γ} {i = i} {x = x} ⊢ᵥ ∋ with <-cmp i x
applyₙ-preserve ⊢ᵥ ∋ | tri< (s≤s i<x) _ _ = ⊢-` (insert-preserve-< (s≤s i<x) ∋)
applyₙ-preserve ⊢ᵥ ∋ | tri≈ _ refl _      rewrite insert-preserve-≡ ∋ = ⊢ᵥ
applyₙ-preserve ⊢ᵥ ∋ | tri> _ _ (s≤s i>x) = ⊢-` (insert-preserve-> (s≤s i>x) ∋)

patternize-preserve : ∀ {Γ} {e : Exp} {τ}
  → Γ ⊢ e ∶ τ
  → Γ ⊢ (patternize e) ∶ τ
patternize-preserve (⊢-` ∋) = ⊢-` ∋
patternize-preserve (⊢-ƛ ⊢ₑ) = ⊢-ƛ ⊢ₑ
patternize-preserve (⊢-· ⊢ₗ ⊢ᵣ) = ⊢-· (patternize-preserve ⊢ₗ) (patternize-preserve ⊢ᵣ)
patternize-preserve (⊢-+ ⊢ₗ ⊢ᵣ) = ⊢-+ (patternize-preserve ⊢ₗ) (patternize-preserve ⊢ᵣ)
patternize-preserve ⊢-# = ⊢-#
patternize-preserve (⊢-φ ⊢ₚ ⊢ₑ) = patternize-preserve ⊢ₑ
patternize-preserve (⊢-δ ⊢ₑ) = patternize-preserve ⊢ₑ
patternize-preserve (⊢-μ ⊢ₑ) = ⊢-μ ⊢ₑ

↑ₙ-preserve : ∀ {Γ τ₀} {x c : ℕ} {τ}
  → Γ ∋ x ∶ τ
  → (insert Γ c τ₀) ∋ (↑ₙ c 1 x) ∶ τ
↑ₙ-preserve {c = zero} ∋ = ∋-S ∋
↑ₙ-preserve {c = suc c} ∋-Z = ∋-Z
↑ₙ-preserve {c = suc c} (∋-S ∋) = ∋-S (↑ₙ-preserve ∋)

↑ₑ-preserve : ∀ {Γ} {e : Exp} {c : ℕ} {τₑ τᵥ}
  → Γ ⊢ e ∶ τₑ
  → (insert Γ c τᵥ) ⊢ (↑ₑ c 1 e) ∶ τₑ
↑ₚ-preserve : ∀ {Γ} {p : Pat} {c : ℕ} {τₚ τᵥ}
  → Γ ⊢ p ∶ τₚ
  → (insert Γ c τᵥ) ⊢ (↑ₚ c 1 p) ∶ τₚ
↑ₑ-preserve (⊢-` ∋) = ⊢-` (↑ₙ-preserve ∋)
↑ₑ-preserve (⊢-ƛ ⊢ₑ) = ⊢-ƛ (↑ₑ-preserve ⊢ₑ)
↑ₑ-preserve (⊢-· ⊢ₗ ⊢ᵣ) = ⊢-· (↑ₑ-preserve ⊢ₗ) (↑ₑ-preserve ⊢ᵣ)
↑ₑ-preserve (⊢-+ ⊢ₗ ⊢ᵣ) = ⊢-+ (↑ₑ-preserve ⊢ₗ) (↑ₑ-preserve ⊢ᵣ)
↑ₑ-preserve ⊢-# = ⊢-#
↑ₑ-preserve (⊢-φ ⊢ₚ ⊢ₑ) = ⊢-φ (↑ₚ-preserve ⊢ₚ) (↑ₑ-preserve ⊢ₑ)
↑ₑ-preserve (⊢-δ ⊢ₑ) = ⊢-δ (↑ₑ-preserve ⊢ₑ)
↑ₑ-preserve (⊢-μ ⊢ₑ) = ⊢-μ (↑ₑ-preserve ⊢ₑ)

↑ₚ-preserve ⊢-E = ⊢-E
↑ₚ-preserve ⊢-V = ⊢-V
↑ₚ-preserve (⊢-` ∋) = ⊢-` (↑ₙ-preserve ∋)
↑ₚ-preserve (⊢-ƛ ⊢ₑ) = ⊢-ƛ (↑ₑ-preserve ⊢ₑ)
↑ₚ-preserve (⊢-· ⊢ₗ ⊢ᵣ) = ⊢-· (↑ₚ-preserve ⊢ₗ) (↑ₚ-preserve ⊢ᵣ)
↑ₚ-preserve ⊢-# = ⊢-#
↑ₚ-preserve (⊢-+ ⊢ₗ ⊢ᵣ) = ⊢-+ (↑ₚ-preserve ⊢ₗ) (↑ₚ-preserve ⊢ᵣ)
↑ₚ-preserve (⊢-μ ⊢ₑ) = ⊢-μ (↑ₑ-preserve ⊢ₑ)

applyₑ-preserve : ∀ {Γ} {e v : Exp} {x : ℕ} {τᵥ τᵢ}
  → Γ ⊢ v ∶ τᵥ
  → (insert Γ x τᵥ) ⊢ e ∶ τᵢ
  → Γ ⊢ applyₑ e x v ∶ τᵢ
applyₚ-preserve : ∀ {Γ} {p : Pat} {v : Exp} {x : ℕ} {τᵥ τᵢ}
  → Γ ⊢ v ∶ τᵥ
  → (insert Γ x τᵥ) ⊢ p ∶ τᵢ
  → Γ ⊢ applyₚ p x v ∶ τᵢ
applyₑ-preserve ⊢ᵥ (⊢-` ∋) = applyₙ-preserve ⊢ᵥ ∋
applyₑ-preserve ⊢ᵥ (⊢-ƛ ⊢ₑ) = ⊢-ƛ (applyₑ-preserve (↑ₑ-preserve ⊢ᵥ) ⊢ₑ)
applyₑ-preserve ⊢ᵥ (⊢-· ⊢ₗ ⊢ᵣ) = ⊢-· (applyₑ-preserve ⊢ᵥ ⊢ₗ) (applyₑ-preserve ⊢ᵥ ⊢ᵣ)
applyₑ-preserve ⊢ᵥ (⊢-+ ⊢ₗ ⊢ᵣ) = ⊢-+ (applyₑ-preserve ⊢ᵥ ⊢ₗ) (applyₑ-preserve ⊢ᵥ ⊢ᵣ)
applyₑ-preserve ⊢ᵥ ⊢-# = ⊢-#
applyₑ-preserve ⊢ᵥ (⊢-φ ⊢ₚ ⊢ₑ) = ⊢-φ (applyₚ-preserve ⊢ᵥ ⊢ₚ) (applyₑ-preserve ⊢ᵥ ⊢ₑ)
applyₑ-preserve ⊢ᵥ (⊢-δ ⊢ₑ) = ⊢-δ (applyₑ-preserve ⊢ᵥ ⊢ₑ)
applyₑ-preserve ⊢ᵥ (⊢-μ ⊢ₑ) = ⊢-μ (applyₑ-preserve (↑ₑ-preserve ⊢ᵥ) ⊢ₑ)

applyₚ-preserve ⊢ᵥ ⊢-E = ⊢-E
applyₚ-preserve ⊢ᵥ ⊢-V = ⊢-V
applyₚ-preserve ⊢ᵥ (⊢-` ∋) = patternize-preserve (applyₙ-preserve ⊢ᵥ ∋)
applyₚ-preserve ⊢ᵥ (⊢-ƛ ⊢ₑ) = patternize-preserve (applyₑ-preserve ⊢ᵥ (⊢-ƛ ⊢ₑ))
applyₚ-preserve ⊢ᵥ (⊢-· ⊢ₗ ⊢ᵣ) = ⊢-· (applyₚ-preserve ⊢ᵥ ⊢ₗ) (applyₚ-preserve ⊢ᵥ ⊢ᵣ)
applyₚ-preserve ⊢ᵥ ⊢-# = ⊢-#
applyₚ-preserve ⊢ᵥ (⊢-+ ⊢ₗ ⊢ᵣ) = ⊢-+ (applyₚ-preserve ⊢ᵥ ⊢ₗ) (applyₚ-preserve ⊢ᵥ ⊢ᵣ)
applyₚ-preserve ⊢ᵥ (⊢-μ ⊢ₑ) = patternize-preserve (applyₑ-preserve ⊢ᵥ (⊢-μ ⊢ₑ))

—→-preserve : ∀ {Γ e₁ e₂ τ}
  → Γ ⊢ e₁ ∶ τ
  → e₁ —→ e₂
  → Γ ⊢ e₂ ∶ τ
—→-preserve (⊢-· (⊢-ƛ ⊢ₗ) ⊢ᵣ) (T-β-· Vᵣ) = applyₑ-preserve ⊢ᵣ ⊢ₗ
—→-preserve (⊢-+ ⊢-# ⊢-#) T-β-+ = ⊢-#
—→-preserve (⊢-φ ⊢ₚ ⊢ₑ) (T-β-φ V) = ⊢ₑ
—→-preserve (⊢-δ ⊢ₑ) (T-β-δ V) = ⊢ₑ
—→-preserve (⊢-μ ⊢ₑ) (T-β-μ)   = applyₑ-preserve (⊢-μ ⊢ₑ) ⊢ₑ

⇴-preserve : ∀ {Γ e₁ e₂ τ}
  → Γ ⊢ e₁ ∶ τ
  → e₁ ⇴ e₂
  → Γ ⊢ e₂ ∶ τ
⇴-preserve (⊢-` ∋) O-` = ⊢-` ∋
⇴-preserve (⊢-ƛ ⊢) (O-V V-ƛ) = ⊢-ƛ ⊢
⇴-preserve (⊢-· ⊢ₗ ⊢ᵣ) (O-· Oₗ Oᵣ) = ⊢-· (⇴-preserve ⊢ₗ Oₗ) (⇴-preserve ⊢ᵣ Oᵣ)
⇴-preserve (⊢-+ ⊢ₗ ⊢ᵣ) (O-+ Oₗ Oᵣ) = ⊢-+ (⇴-preserve ⊢ₗ Oₗ) (⇴-preserve ⊢ᵣ Oᵣ)
⇴-preserve ⊢-# (O-V V-#) = ⊢-#
⇴-preserve (⊢-φ ⊢ₚ ⊢ₑ) (O-φ O) = ⊢-φ ⊢ₚ (⇴-preserve ⊢ₑ O)
⇴-preserve (⊢-δ ⊢) (O-δᵢ x O) = ⇴-preserve ⊢ O
⇴-preserve (⊢-δ (⊢-δ ⊢)) (O-δₒ x O) = ⇴-preserve (⊢-δ ⊢) O
⇴-preserve (⊢-δ ⊢) (O-δ x O) = ⊢-δ (⇴-preserve ⊢ O)
⇴-preserve (⊢-μ ⊢) (O-μ) = ⊢-μ ⊢

-- ↦-preserve : ∀ {Γ e₁ e₂ τ}
--   → Γ ⊢ e₁ ∶ τ
--   → e₁ ↦ e₂
--   → Γ ⊢ e₂ ∶ τ
-- ↦-preserve (⊢-` ∋) (step () T C)
-- ↦-preserve (⊢-ƛ ⊢) (step () T C)
-- ↦-preserve (⊢-· ⊢ₗ ⊢ᵣ) (step (D-ξ-·ₗ D) T (C-·ₗ C)) = ⊢-· (↦-preserve ⊢ₗ (step D T C)) ⊢ᵣ
-- ↦-preserve (⊢-· ⊢ₗ ⊢ᵣ) (step (D-ξ-·ᵣ V D) T (C-·ᵣ C)) = ⊢-· ⊢ₗ (↦-preserve ⊢ᵣ (step D T C))
-- ↦-preserve (⊢-· ⊢ₗ ⊢ᵣ) (step (D-β-· Vₗ Vᵣ) T C) = {!!}
-- ↦-preserve (⊢-#) S = {!!}
-- ↦-preserve ⊢ (step (D-ξ-+ₗ D) T C) = {!!}
-- ↦-preserve ⊢ (step (D-ξ-+ᵣ V D) T C) = {!!}
-- ↦-preserve ⊢ (step (D-β-+ Vₗ Vᵣ) T C) = {!!}
-- ↦-preserve ⊢ (step (D-ξ-φ D) T C) = {!!}
-- ↦-preserve ⊢ (step (D-β-φ V) T C) = {!!}
-- ↦-preserve ⊢ (step (D-ξ-δ D) T C) = {!!}
-- ↦-preserve ⊢ (step (D-β-δ V) T C) = {!!}

preserve : ∀ {Γ e₁ e₂ τ}
  → Γ ⊢ e₁ ∶ τ
  → e₁ ⇥ e₂
  → Γ ⊢ e₂ ∶ τ
preserve ⊢ (step I O D A T C) = ⇐-preserve (⇴-preserve (⇝-preserve ⊢ I) O) D (λ ⊢₀ → —→-preserve ⊢₀ T) C
preserve ⊢ (skip I O D A T C S) = preserve (⇐-preserve (⇴-preserve (⇝-preserve ⊢ I) O) D (λ ⊢₀ → —→-preserve ⊢₀ T) C) S
preserve ⊢ (done V) = ⊢
