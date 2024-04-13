open import Core
open import Dynamics
open import Statics
open import Match
open import Subst
open import Data.Nat using (_≤_; _<?_; _<_; _≥_; zero; suc; s≤s; z≤n)
open import Data.Nat.Properties using (≮⇒≥)
open import Relation.Nullary using (yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)

module Preservation where
  insert-preserve-< : ∀ {Γ x y τ₁ τ₂}
    → Γ ∋ x ∶ τ₁
    → (∈ : y ≤ length Γ)
    → x < y
    → (insert ∈ τ₂) ∋ x ∶ τ₁
  insert-preserve-< {Γ ⸴ τ₀} ∋-Z (s≤s ∈) (s≤s x<y) = ∋-Z
  insert-preserve-< {Γ ⸴ τ₀} (∋-S ∋) (s≤s ∈) (s≤s x<y) = ∋-S (insert-preserve-< ∋ ∈ x<y)

  insert-preserve-≥ : ∀ {Γ x y τ₁ τ₂}
    → Γ ∋ x ∶ τ₁
    → (∈ : y ≤ length Γ)
    → y < (suc x)
    → (insert ∈ τ₂) ∋ (suc x) ∶ τ₁
  insert-preserve-≥ {Γ ⸴ τ₀} ∋ z≤n (s≤s y<sx) = ∋-S ∋
  insert-preserve-≥ {Γ ⸴ τ₀} (∋-S ∋) (s≤s ∈) (s≤s y<sx) = ∋-S (insert-preserve-≥ ∋ ∈ y<sx)

  ↑-preserve-exp : ∀ {Γ τ τ₀ y} {e : Exp}
    → Γ ⊢ e ∶ τ
    → (∈ : y ≤ length Γ)
    → (insert ∈ τ₀) ⊢ (e ↑ (from y)) ∶ τ
  ↑-preserve-pat : ∀ {Γ τ τ₀ y} {p : Pat}
    → Γ ⊢ p ∶ τ
    → (∈ : y ≤ length Γ)
    → (insert ∈ τ₀) ⊢ (p ↑ (from y)) ∶ τ

  ↑-preserve-exp {y = y} (⊢-` {x = x} ∋) ∈ with x <? y
  ... | yes x<y = ⊢-` (insert-preserve-< ∋ ∈ x<y)
  ... | no x≮y = ⊢-` (insert-preserve-≥ ∋ ∈ (≮⇒≥ λ { (s≤s x<y) → x≮y x<y }))
  ↑-preserve-exp (⊢-ƛ ⊢) ∈ = ⊢-ƛ (↑-preserve-exp ⊢ (s≤s ∈))
  ↑-preserve-exp (⊢-· ⊢ₗ ⊢ᵣ) ∈ = ⊢-· (↑-preserve-exp ⊢ₗ ∈) (↑-preserve-exp ⊢ᵣ ∈)
  ↑-preserve-exp (⊢-+ ⊢ₗ ⊢ᵣ) ∈ = ⊢-+ (↑-preserve-exp ⊢ₗ ∈) (↑-preserve-exp ⊢ᵣ ∈)
  ↑-preserve-exp ⊢-# ∈ = ⊢-#
  ↑-preserve-exp (⊢-φ ⊢ₚ ⊢ₑ) ∈ = ⊢-φ (↑-preserve-pat ⊢ₚ ∈) (↑-preserve-exp ⊢ₑ ∈)
  ↑-preserve-exp (⊢-δ ⊢) ∈ = ⊢-δ (↑-preserve-exp ⊢ ∈)

  ↑-preserve-pat ⊢-E ∈ = ⊢-E
  ↑-preserve-pat ⊢-V ∈ = ⊢-V
  ↑-preserve-pat {y = y} (⊢-` {x = x} ∋) ∈ with x <? y
  ... | yes x<y = ⊢-` (insert-preserve-< ∋ ∈ x<y)
  ... | no x≮y = ⊢-` (insert-preserve-≥ ∋ ∈ (≮⇒≥ λ { (s≤s x<y) → x≮y x<y }))
  ↑-preserve-pat (⊢-ƛ ⊢) ∈ = ⊢-ƛ (↑-preserve-exp ⊢ (s≤s ∈))
  ↑-preserve-pat (⊢-· ⊢ₗ ⊢ᵣ) ∈ = ⊢-· (↑-preserve-pat ⊢ₗ ∈) (↑-preserve-pat ⊢ᵣ ∈)
  ↑-preserve-pat ⊢-# ∈ = ⊢-#
  ↑-preserve-pat (⊢-+ ⊢ₗ ⊢ᵣ) ∈ = ⊢-+ (↑-preserve-pat ⊢ₗ ∈) (↑-preserve-pat ⊢ᵣ ∈)

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

  decay-preserve : ∀ {Γ ε τ}
    → Γ ⊢ ε ∶ τ
    → Γ ⊢ (decay ε) ∶ τ
  decay-preserve ⊢-∘ = ⊢-∘
  decay-preserve (⊢-·-l ⊢ₗ ⊢ᵣ) = ⊢-·-l (decay-preserve ⊢ₗ) ⊢ᵣ
  decay-preserve (⊢-·-r ⊢ₗ ⊢ᵣ) = ⊢-·-r ⊢ₗ (decay-preserve ⊢ᵣ)

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

  ⇒-preserve : ∀ {Γ e ε τ e₀}
    → Γ ⊢ e ∶ τ
    → e ⇒ ε ⟨ e₀ ⟩
    → ∃ (λ τ₀ → (Γ ⊢ e₀ ∶ τ₀) × (Γ ⊢ ε ∶ τ))
  ⇒-preserve {τ = τ} (⊢-` ∋) D-β-` = τ , (⊢-` ∋) , ⊢-∘
  ⇒-preserve (⊢-· ⊢ₗ ⊢ᵣ) (D-ξ-·-l D) with ⇒-preserve ⊢ₗ D
  ... | τ₀ , f = τ₀ , {!!}
  ⇒-preserve (⊢-· ⊢ₗ ⊢ᵣ) (D-ξ-·-r x D) = {!!}
  ⇒-preserve (⊢-· ⊢ₗ ⊢ᵣ) (D-β-· x x₁) = {!!}
  ⇒-preserve (⊢-+ ⊢ ⊢₁) D = {!!}
  ⇒-preserve (⊢-φ x ⊢) D = {!!}
  ⇒-preserve (⊢-δ ⊢) D = {!!}

  ⇐-preserve : ∀ {Γ e ε e₀ τ}
    → ∃ (λ τ₀ → (Γ ⊢ e₀ ∶ τ₀) × (Γ ⊢ ε ∶ τ))
    → e ⇐ ε ⟨ e₀ ⟩
    → Γ ⊢ e ∶ τ
  ⇐-preserve = {!!}

  ·-preserve : ∀ {Γ} {e v : Exp} {τᵥ τₑ n}
    → Γ ⊢ v ∶ τᵥ
    → (Γ ⸴ τᵥ) ⊢ e ∶ τₑ
    → Γ ⊢ ([ v ↑ (from 0 by (suc n)) / n ] e) ↓ n ∶ τₑ
  ·-preserve ⊢ᵥ (⊢-` ∋) = {!!}
  ·-preserve ⊢ᵥ (⊢-ƛ ⊢ₑ) = ⊢-ƛ {!!}
  ·-preserve ⊢ᵥ (⊢-· ⊢ₑ ⊢ₑ₁) = {!!}
  ·-preserve ⊢ᵥ (⊢-+ ⊢ₑ ⊢ₑ₁) = {!!}
  ·-preserve ⊢ᵥ ⊢-# = {!!}
  ·-preserve ⊢ᵥ (⊢-φ x ⊢ₑ) = {!!}
  ·-preserve ⊢ᵥ (⊢-δ ⊢ₑ) = {!!}

  —→-preserve : ∀ {Γ e₁ e₂ τ}
    → Γ ⊢ e₁ ∶ τ
    → e₁ —→ e₂
    → Γ ⊢ e₂ ∶ τ
  —→-preserve (⊢-· (⊢-ƛ ⊢ₗ) ⊢ᵣ) (T-β-· Vᵣ) = {!!}
  —→-preserve (⊢-φ x ⊢) T = {!!}
  —→-preserve (⊢-δ ⊢) T = {!!}

  preserve : ∀ {Γ s e₁ e₂ τ}
    → Γ ⊢ e₁ ∶ τ
    → s ⊢ e₁ ⇥ e₂
    → Γ ⊢ e₂ ∶ τ
  preserve ⊢ (step I D A T C) with ⇒-preserve (⇝-preserve ⊢ I) D
  ... | τ₀ , ⊢₀ , ⊢ₑ = ⇐-preserve (τ₀ , (—→-preserve ⊢₀) T , decay-preserve ⊢ₑ) C
  preserve ⊢ (skip I D A T C S) = {!!}
  preserve ⊢ (done x) = {!!}
