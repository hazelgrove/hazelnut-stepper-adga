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
strip-preserve (⊢-ƛ x⊢e)   = ⊢-ƛ (strip-preserve x⊢e)
strip-preserve (⊢-· ⊢ₗ ⊢ᵣ) = ⊢-· (strip-preserve ⊢ₗ) (strip-preserve ⊢ᵣ)
strip-preserve (⊢-+ ⊢ₗ ⊢ᵣ) = ⊢-+ (strip-preserve ⊢ₗ) (strip-preserve ⊢ᵣ)
strip-preserve ⊢-#         = ⊢-#
strip-preserve (⊢-φ ⊢ₚ ⊢ₑ) = strip-preserve ⊢ₑ
strip-preserve (⊢-δ ⊢ₑ)    = strip-preserve ⊢ₑ

⇝-preserve : ∀ {Γ s e₁ e₂ τ}
  → Γ ⊢ e₁ ∶ τ
  → s ⊢ e₁ ⇝ e₂
  → Γ ⊢ e₂ ∶ τ
⇝-preserve (⊢-ƛ ⊢) (I-V V) = ⊢-ƛ ⊢
⇝-preserve (⊢-#) (I-V V) = ⊢-#
⇝-preserve (⊢-` ∋) (I-`-⊤ M) = ⊢-δ (⊢-` ∋)
⇝-preserve (⊢-` ∋) (I-`-⊥ M) = ⊢-` ∋
⇝-preserve (⊢-· ⊢ₗ ⊢ᵣ) (I-·-⊤ M Iₗ Iᵣ) = ⊢-δ (⊢-· (⇝-preserve ⊢ₗ Iₗ) (⇝-preserve ⊢ᵣ Iᵣ))
⇝-preserve (⊢-· ⊢ₗ ⊢ᵣ) (I-·-⊥ M Iₗ Iᵣ) = ⊢-· (⇝-preserve ⊢ₗ Iₗ) (⇝-preserve ⊢ᵣ Iᵣ)
⇝-preserve (⊢-+ ⊢ₗ ⊢ᵣ) (I-+-⊤ M Iₗ Iᵣ) = ⊢-δ (⊢-+ (⇝-preserve ⊢ₗ Iₗ) (⇝-preserve ⊢ᵣ Iᵣ))
⇝-preserve (⊢-+ ⊢ₗ ⊢ᵣ) (I-+-⊥ M Iₗ Iᵣ) = ⊢-+ (⇝-preserve ⊢ₗ Iₗ) (⇝-preserve ⊢ᵣ Iᵣ)
⇝-preserve (⊢-φ ⊢ₚ ⊢ₑ) (I-φ I₀ I₁) = ⊢-φ ⊢ₚ (⇝-preserve (⇝-preserve ⊢ₑ I₀) I₁)
⇝-preserve (⊢-δ ⊢) (I-δ I) = ⊢-δ (⇝-preserve ⊢ I)

⇐-preserve : ∀ {Γ} {e e′ e₀ e₀′ : Exp} {τ} {ε : Dynamics.Ctx}
  → Γ ⊢ e ∶ τ
  → e ⇒ ε ⟨ e₀ ⟩
  → (∀ {τ₀} → Γ ⊢ e₀ ∶ τ₀ → Γ ⊢ e₀′ ∶ τ₀)
  → e′ ⇒ (decay ε) ⟨ e₀′ ⟩
  → Γ ⊢ e′ ∶ τ
⇐-preserve ⊢ D-β-` P₀ D-β-` = P₀ ⊢
⇐-preserve ⊢ D-β-` P₀ (D-β-· Vₗ Vᵣ) = P₀ ⊢
⇐-preserve ⊢ D-β-` P₀ (D-β-+ Vₗ Vᵣ) = P₀ ⊢
⇐-preserve ⊢ D-β-` P₀ (D-β-φ V) = P₀ ⊢
⇐-preserve ⊢ D-β-` P₀ (D-β-δ V) = P₀ ⊢
⇐-preserve (⊢-· ⊢ₗ ⊢ᵣ) (D-ξ-·-l D) P₀ (D-ξ-·-l C) = ⊢-· (⇐-preserve ⊢ₗ D P₀ C) ⊢ᵣ
⇐-preserve (⊢-· ⊢ₗ ⊢ᵣ) (D-ξ-·-r V D) P₀ (D-ξ-·-r _ C) = ⊢-· ⊢ₗ (⇐-preserve ⊢ᵣ D P₀ C)
⇐-preserve ⊢ (D-β-· Vₗ Vᵣ) P₀ D-β-` = P₀ ⊢
⇐-preserve ⊢ (D-β-· Vₗ Vᵣ) P₀ (D-β-· Vₗ₁ Vᵣ₁) = P₀ ⊢
⇐-preserve ⊢ (D-β-· Vₗ Vᵣ) P₀ (D-β-+ Vₗ₁ Vᵣ₁) = P₀ ⊢
⇐-preserve ⊢ (D-β-· Vₗ Vᵣ) P₀ (D-β-φ V) = P₀ ⊢
⇐-preserve ⊢ (D-β-· Vₗ Vᵣ) P₀ (D-β-δ V) = P₀ ⊢
⇐-preserve (⊢-+ ⊢ₗ ⊢ᵣ) (D-ξ-+-l D) P₀ (D-ξ-+-l C) = ⊢-+ (⇐-preserve ⊢ₗ D P₀ C) ⊢ᵣ
⇐-preserve (⊢-+ ⊢ₗ ⊢ᵣ) (D-ξ-+-r V D) P₀ (D-ξ-+-r _ C) = ⊢-+ ⊢ₗ (⇐-preserve ⊢ᵣ D P₀ C)
⇐-preserve ⊢ (D-β-+ Vₗ Vᵣ) P₀ D-β-` = P₀ ⊢
⇐-preserve ⊢ (D-β-+ Vₗ Vᵣ) P₀ (D-β-· Vₗ₁ Vᵣ₁) = P₀ ⊢
⇐-preserve ⊢ (D-β-+ Vₗ Vᵣ) P₀ (D-β-+ Vₗ₁ Vᵣ₁) = P₀ ⊢
⇐-preserve ⊢ (D-β-+ Vₗ Vᵣ) P₀ (D-β-φ V) = P₀ ⊢
⇐-preserve ⊢ (D-β-+ Vₗ Vᵣ) P₀ (D-β-δ V) = P₀ ⊢
⇐-preserve (⊢-φ x ⊢) (D-ξ-φ D) P₀ C = ⇐-preserve ⊢ D P₀ C
⇐-preserve (⊢-φ x ⊢) (D-β-φ V) P₀ D-β-` = P₀ (⊢-φ x ⊢)
⇐-preserve (⊢-φ x ⊢) (D-β-φ V) P₀ (D-β-· Vₗ Vᵣ) = P₀ (⊢-φ x ⊢)
⇐-preserve (⊢-φ x ⊢) (D-β-φ V) P₀ (D-β-+ Vₗ Vᵣ) = P₀ (⊢-φ x ⊢)
⇐-preserve (⊢-φ x ⊢) (D-β-φ V) P₀ (D-β-φ V₁) = P₀ (⊢-φ x ⊢)
⇐-preserve (⊢-φ x ⊢) (D-β-φ V) P₀ (D-β-δ V₁) = P₀ (⊢-φ x ⊢)
⇐-preserve (⊢-δ ⊢) (D-ξ-δ D) P₀ C = ⇐-preserve ⊢ D P₀ C
⇐-preserve ⊢ (D-β-δ V) P₀ D-β-` = P₀ ⊢
⇐-preserve ⊢ (D-β-δ V) P₀ (D-β-· Vₗ Vᵣ) = P₀ ⊢
⇐-preserve ⊢ (D-β-δ V) P₀ (D-β-+ Vₗ Vᵣ) = P₀ ⊢
⇐-preserve ⊢ (D-β-δ V) P₀ (D-β-φ V₁) = P₀ ⊢
⇐-preserve ⊢ (D-β-δ V) P₀ (D-β-δ V₁) = P₀ ⊢

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

↑ₚ-preserve ⊢-E = ⊢-E
↑ₚ-preserve ⊢-V = ⊢-V
↑ₚ-preserve (⊢-` ∋) = ⊢-` (↑ₙ-preserve ∋)
↑ₚ-preserve (⊢-ƛ ⊢ₑ) = ⊢-ƛ (↑ₑ-preserve ⊢ₑ)
↑ₚ-preserve (⊢-· ⊢ₗ ⊢ᵣ) = ⊢-· (↑ₚ-preserve ⊢ₗ) (↑ₚ-preserve ⊢ᵣ)
↑ₚ-preserve ⊢-# = ⊢-#
↑ₚ-preserve (⊢-+ ⊢ₗ ⊢ᵣ) = ⊢-+ (↑ₚ-preserve ⊢ₗ) (↑ₚ-preserve ⊢ᵣ)

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

applyₚ-preserve ⊢ᵥ ⊢-E = ⊢-E
applyₚ-preserve ⊢ᵥ ⊢-V = ⊢-V
applyₚ-preserve ⊢ᵥ (⊢-` ∋) = patternize-preserve (applyₙ-preserve ⊢ᵥ ∋)
applyₚ-preserve ⊢ᵥ (⊢-ƛ ⊢ₑ) = patternize-preserve (applyₑ-preserve ⊢ᵥ (⊢-ƛ ⊢ₑ))
applyₚ-preserve ⊢ᵥ (⊢-· ⊢ₗ ⊢ᵣ) = ⊢-· (applyₚ-preserve ⊢ᵥ ⊢ₗ) (applyₚ-preserve ⊢ᵥ ⊢ᵣ)
applyₚ-preserve ⊢ᵥ ⊢-# = ⊢-#
applyₚ-preserve ⊢ᵥ (⊢-+ ⊢ₗ ⊢ᵣ) = ⊢-+ (applyₚ-preserve ⊢ᵥ ⊢ₗ) (applyₚ-preserve ⊢ᵥ ⊢ᵣ)

·-preserve : ∀ {Γ} {e v : Exp} {τᵥ τₑ}
  → Γ ⊢ v ∶ τᵥ
  → (Γ ⸴ τᵥ) ⊢ e ∶ τₑ
  → Γ ⊢ applyₑ e 0 v ∶ τₑ
·-preserve ⊢ᵥ ⊢ₑ = applyₑ-preserve ⊢ᵥ ⊢ₑ

—→-preserve : ∀ {Γ e₁ e₂ τ}
  → Γ ⊢ e₁ ∶ τ
  → e₁ —→ e₂
  → Γ ⊢ e₂ ∶ τ
—→-preserve (⊢-· (⊢-ƛ ⊢ₗ) ⊢ᵣ) (T-β-· Vᵣ) = ·-preserve ⊢ᵣ ⊢ₗ
—→-preserve (⊢-φ ⊢ₚ ⊢ₑ) (T-β-φ V) = ⊢ₑ
—→-preserve (⊢-δ ⊢ₑ) (T-β-δ V) = ⊢ₑ

preserve : ∀ {Γ s e₁ e₂ τ}
  → Γ ⊢ e₁ ∶ τ
  → s ⊢ e₁ ⇥ e₂
  → Γ ⊢ e₂ ∶ τ
preserve ⊢ (step I D A T C) = ⇐-preserve (⇝-preserve ⊢ I) D (λ ⊢₀ → —→-preserve ⊢₀ T) C
preserve ⊢ (skip I D A T C S) = preserve (⇐-preserve (⇝-preserve ⊢ I) D (λ ⊢₀ → —→-preserve ⊢₀ T) C) S
preserve ⊢ (done V) = ⊢
