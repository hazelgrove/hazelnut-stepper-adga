open import Core
open import Dynamics
open import Statics
open import Match
open import Subst
open import Data.Nat using (_≤_; _<?_; zero; suc; s≤s; z≤n)
open import Relation.Nullary using (yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)

module Preservation where

  private
    insert-preserve : ∀ {Γ x y τ₁ τ₂}
      → (∈ : x ≤ length Γ)
      → (x ≤ y)
      → 
    ↑-preserve-exp-` : ∀ {Γ τ τ₀ x y}
      → Γ ∋ x ∶ τ
      → (∈ : y ≤ length Γ)
      → (insert ∈ τ₀) ⊢ ((Exp.` x) ↑ y) ∶ τ
    ↑-preserve-exp-` {x = x} {y} ∋ ∈ with x <? y
    ↑-preserve-exp-` {x = zero} {suc y} ∋-Z (s≤s ∈) | yes (s≤s z≤n) = ⊢-` ∋-Z
    ↑-preserve-exp-` {x = suc x} {suc y} (∋-S ∋) (s≤s ∈) | yes (s≤s x<y) = ⊢-` (∋-S {!!})
    ↑-preserve-exp-` {x = x} {y} ∋ ∈ | no x≮y = {!!}
    -- ↑-preserve-exp-` {x = zero} {suc y} ∋-Z (s≤s ∈) | yes (s≤s z≤n) = ⊢-` {!!}
    -- ↑-preserve-exp-` {x = (suc x)} {y} (∋-S ∋) ∈ | yes x<y = ⊢-` {!!}

    ↑-preserve-exp : ∀ {Γ τ τ₀ y} {e : Exp}
      → Γ ⊢ e ∶ τ
      → (∈ : y ≤ length Γ)
      → (insert ∈ τ₀) ⊢ (e ↑ y) ∶ τ
    ↑-preserve-exp {y = y} (⊢-` {x = x} ∋) ∈ = {!!}
    ↑-preserve-exp (⊢-ƛ ⊢) ∈ = {!!}
    ↑-preserve-exp (⊢-· ⊢ ⊢₁) ∈ = {!!}
    ↑-preserve-exp (⊢-+ ⊢ ⊢₁) ∈ = {!!}
    ↑-preserve-exp ⊢-# ∈ = {!!}
    ↑-preserve-exp (⊢-φ ⊢ₚ ⊢) ∈ = {!!}
    ↑-preserve-exp (⊢-δ ⊢) ∈ = {!!}

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

  —→-preserve : ∀ {Γ e₁ e₂ τ}
    → Γ ⊢ e₁ ∶ τ
    → e₁ —→ e₂
    → Γ ⊢ e₂ ∶ τ
  —→-preserve (⊢-· ⊢ₗ ⊢ᵣ) (T-β-· Vᵣ) = {!!}
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
