open import Core
open import Dynamics
open import Statics
open import Match
open import Subst
open import Data.Nat using (ℕ; _≤_; _<?_; _<_; _≥_; zero; suc; s≤s; z≤n)
open import Data.Nat.Properties using (≮⇒≥)
open import Data.List using (List)
open import Relation.Nullary using (yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; _≡_; cong; cong₂; subst; subst₂; sym)

module Preservation where
  -- insert-preserve-< : ∀ {Γ x y τ₁ τ₂}
  --   → Γ ∋ x ∶ τ₁
  --   → (∈ : y ≤ length Γ)
  --   → x < y
  --   → (insert ∈ τ₂) ∋ x ∶ τ₁
  -- insert-preserve-< {Γ ⸴ τ₀} ∋-Z (s≤s ∈) (s≤s x<y) = ∋-Z
  -- insert-preserve-< {Γ ⸴ τ₀} (∋-S ∋) (s≤s ∈) (s≤s x<y) = ∋-S (insert-preserve-< ∋ ∈ x<y)

  -- insert-preserve-≥ : ∀ {Γ x y τ₁ τ₂}
  --   → Γ ∋ x ∶ τ₁
  --   → (∈ : y ≤ length Γ)
  --   → y < (suc x)
  --   → (insert ∈ τ₂) ∋ (suc x) ∶ τ₁
  -- insert-preserve-≥ {Γ ⸴ τ₀} ∋ z≤n (s≤s y<sx) = ∋-S ∋
  -- insert-preserve-≥ {Γ ⸴ τ₀} (∋-S ∋) (s≤s ∈) (s≤s y<sx) = ∋-S (insert-preserve-≥ ∋ ∈ y<sx)

  -- ↑ₑ-preserve : ∀ {Γ τ τs y} {e : Exp}
  --   → Γ ⊢ e ∶ τ
  --   → (∈ : y ≤ lenght Γ)
  --   → (insert ∈ τs)

  ↑ₙ₀¹-preserve : ∀ {Γ x τₓ τ}
    → Γ ∋ x ∶ τₓ
    → (Γ ⸴ τ) ∋ (↑ₙ 0 1 x) ∶ τₓ
  ↑ₙ₀¹-preserve ∋-Z = ∋-S ∋-Z
  ↑ₙ₀¹-preserve (∋-S ∋) = ∋-S (∋-S ∋)

  ↑ₙ¹-preserve : ∀ {Γ x τₓ y Γ′ τ′}
    → Γ ∋ x ∶ τₓ
    → (∈ : y ≤ length Γ)
    → (insert ∈ (Γ′ ⸴ τ′)) ∋ (↑ₙ y 1 (↑ₙ y (length Γ′) x)) ∶ τₓ
  ↑ₙ¹-preserve ∋-Z z≤n = ∋-S {!!}
  ↑ₙ¹-preserve ∋-Z (s≤s ∈) = ∋-Z
  ↑ₙ¹-preserve (∋-S ∋) z≤n = ∋-S {!!}
  ↑ₙ¹-preserve (∋-S ∋) (s≤s ∈) = ∋-S {!!}

  ↑ₙ-preserve : ∀ {Γ τₓ y Γ′} {x : ℕ}
    → Γ ∋ x ∶ τₓ
    → (∈ : y ≤ length Γ)
    → (insert ∈ Γ′) ∋ (↑ₙ y (length Γ′) x) ∶ τₓ
  ↑ₙ-preserve {Γ ⸴ τ} {Γ′ = ∅} ∋ z≤n = ∋
  ↑ₙ-preserve {Γ ⸴ τ} {τₓ} {Γ′ = ∅} ∋ (s≤s {m} ∈) = subst₂ (λ Γ x → Γ ⸴ τ ∋ x ∶ τₓ) (sym insert-∅) (sym (↑ₙ⁰ {suc m})) ∋
  ↑ₙ-preserve {Γ ⸴ τ} {Γ′ = Γ′ ⸴ τ′} ∋ z≤n = ∋-S (↑ₙ-preserve ∋ z≤n)
  ↑ₙ-preserve {Γ ⸴ τ} {Γ′ = Γ′ ⸴ τ′} {zero} ∋-Z (s≤s ∈) = ∋-Z
  -- insert ∈ (Γ′ ⸴ τ′) ∋ ↑ₙ m (suc (length Γ′)) x ∶ τₓ
  ↑ₙ-preserve {Γ ⸴ τ} {τₓ} {Γ′ = Γ′ ⸴ τ′} {suc x} (∋-S ∋) (s≤s {m} ∈) with (↑ₙ-preserve {Γ = Γ} {τₓ = τₓ} {y = m} {Γ′ = Γ′} {x = x} ∋ ∈)
  ↑ₙ-preserve {Γ ⸴ τ} {τₓ} {Γ′ = Γ′ ⸴ τ′} {suc x} (∋-S ∋) (s≤s {m} ∈) | R = ∋-S (subst (λ x → insert ∈ (Γ′ ⸴ τ′) ∋ x ∶ τₓ) (↑ₙ-cascade {m} {length Γ′}) {!!})

  ↑ₑ-preserve : ∀ {Γ τ y Γ′} {e : Exp}
    → Γ ⊢ e ∶ τ
    → (∈ : y ≤ length Γ)
    → (insert ∈ Γ′) ⊢ (↑ y (length Γ′) e) ∶ τ
  ↑-preserve-pat : ∀ {Γ τ y Γ′} {p : Pat}
    → Γ ⊢ p ∶ τ
    → (∈ : y ≤ length Γ)
    → (insert ∈ Γ′) ⊢ (↑ y (length Γ′) p) ∶ τ

  -- ↑ₑ-preserve {y = y} (⊢-` {x = x} ∋) ∈ with x <? y
  -- ↑ₑ-preserve {y = y} (⊢-` {x = x} ∋) ∈ | yes x<y = ⊢-` {!!}
  -- ↑ₑ-preserve {y = y} (⊢-` {x = x} ∋) ∈ | no x≮y  = ⊢-` {!!}
  ↑ₑ-preserve (⊢-` ∋)     ∈ = ⊢-` {!!}
  ↑ₑ-preserve (⊢-ƛ ⊢)     ∈ = ⊢-ƛ (↑ₑ-preserve ⊢ (s≤s ∈))
  ↑ₑ-preserve (⊢-· ⊢ₗ ⊢ᵣ) ∈ = ⊢-· (↑ₑ-preserve ⊢ₗ ∈) (↑ₑ-preserve ⊢ᵣ ∈)
  ↑ₑ-preserve (⊢-+ ⊢ₗ ⊢ᵣ) ∈ = ⊢-+ (↑ₑ-preserve ⊢ₗ ∈) (↑ₑ-preserve ⊢ᵣ ∈)
  ↑ₑ-preserve ⊢-#         ∈ = ⊢-#
  ↑ₑ-preserve (⊢-φ ⊢ₚ ⊢ₑ) ∈ = ⊢-φ (↑-preserve-pat ⊢ₚ ∈) (↑ₑ-preserve ⊢ₑ ∈)
  ↑ₑ-preserve (⊢-δ ⊢)     ∈ = ⊢-δ (↑ₑ-preserve ⊢ ∈)

  ↑-preserve-pat ⊢-E ∈ = ⊢-E
  ↑-preserve-pat ⊢-V ∈ = ⊢-V
  ↑-preserve-pat {y = y} (⊢-` {x = x} ∋) ∈ with x <? y
  ... | yes x<y = ⊢-` {!!}
  ... | no x≮y = ⊢-` {!!}
  ↑-preserve-pat (⊢-ƛ ⊢) ∈ = ⊢-ƛ (↑ₑ-preserve ⊢ (s≤s ∈))
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
  decay-preserve (⊢-+-l ⊢ₗ ⊢ᵣ) = ⊢-+-l (decay-preserve ⊢ₗ) ⊢ᵣ
  decay-preserve (⊢-+-r ⊢ₗ ⊢ᵣ) = ⊢-+-r ⊢ₗ (decay-preserve ⊢ᵣ)
  decay-preserve (⊢-φ ⊢ₚ ⊢ₑ) = decay-preserve ⊢ₑ
  decay-preserve (⊢-δ ⊢ₑ) = decay-preserve ⊢ₑ

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
    → ∃[ τ₀ ] (Γ ⊢ e₀ ∶ τ₀) × (Γ ⊢ ε ∶ τ)
  ⇒-preserve {τ = τ} (⊢-` ∋) D-β-` = τ , (⊢-` ∋) , ⊢-∘
  ⇒-preserve (⊢-· ⊢ₗ ⊢ᵣ) (D-ξ-·-l D) with ⇒-preserve ⊢ₗ D
  ... | τ₀ , ⊢ₑ , ⊢ₖ = τ₀ , ⊢ₑ , ⊢-·-l ⊢ₖ ⊢ᵣ
  ⇒-preserve (⊢-· ⊢ₗ ⊢ᵣ) (D-ξ-·-r V D) with ⇒-preserve ⊢ᵣ D
  ... | τ₀ , ⊢ₑ , ⊢ₖ = τ₀ , ⊢ₑ , ⊢-·-r ⊢ₗ ⊢ₖ
  ⇒-preserve {τ = τ} (⊢-· ⊢ₗ ⊢ᵣ) (D-β-· Vₗ Vᵣ) = τ , (⊢-· ⊢ₗ ⊢ᵣ , ⊢-∘)
  ⇒-preserve (⊢-+ ⊢ₗ ⊢ᵣ) (D-ξ-+-l D) with ⇒-preserve ⊢ₗ D
  ... | τ₀ , ⊢ₑ , ⊢ₖ = τ₀ , ⊢ₑ , ⊢-+-l ⊢ₖ ⊢ᵣ
  ⇒-preserve (⊢-+ ⊢ₗ ⊢ᵣ) (D-ξ-+-r V D) with ⇒-preserve ⊢ᵣ D
  ... | τ₀ , ⊢ₑ , ⊢ₖ = τ₀ , ⊢ₑ , ⊢-+-r ⊢ₗ ⊢ₖ
  ⇒-preserve (⊢-+ ⊢ₗ ⊢ᵣ) (D-β-+ Vₗ Vᵣ) = Ν , (⊢-+ ⊢ₗ ⊢ᵣ) , ⊢-∘
  ⇒-preserve {τ = τ} (⊢-φ ⊢ₚ ⊢ₑ) (D-ξ-φ D) with ⇒-preserve ⊢ₑ D
  ⇒-preserve {τ = τ} (⊢-φ ⊢ₚ ⊢ₑ) (D-ξ-φ D) | τ₀ , ⊢₀ , ⊢ₖ = τ₀ , (⊢₀ , ⊢-φ ⊢ₚ ⊢ₖ)
  ⇒-preserve {τ = τ} (⊢-φ ⊢ₚ ⊢ₑ) (D-β-φ V) = τ , ((⊢-φ ⊢ₚ ⊢ₑ) , ⊢-∘)
  ⇒-preserve (⊢-δ ⊢) (D-ξ-δ D) with ⇒-preserve ⊢ D
  ⇒-preserve (⊢-δ ⊢) (D-ξ-δ D) | τ₀ , ⊢₀ , ⊢ₖ = τ₀ , ⊢₀ , ⊢-δ ⊢ₖ
  ⇒-preserve {τ = τ} (⊢-δ ⊢) (D-β-δ V) = τ , ⊢-δ ⊢ , ⊢-∘

  ⇐-preserve : ∀ {Γ e ε e₀ τ}
    → ∃ (λ τ₀ → (Γ ⊢ e₀ ∶ τ₀) × (Γ ⊢ ε ∶ τ))
    → e ⇐ ε ⟨ e₀ ⟩
    → Γ ⊢ e ∶ τ
  ⇐-preserve = {!!}

  ·-preserve : ∀ {Γ} {e v : Exp} {τᵥ τₑ n}
    → Γ ⊢ v ∶ τᵥ
    → (Γ ⸴ τᵥ) ⊢ e ∶ τₑ
    → Γ ⊢ ↓ n 1 ([ ↑ 0 (suc n) v / n ] e) ∶ τₑ
  ·-preserve ⊢ᵥ (⊢-` ∋) = {!!}
  ·-preserve {Γ} {v = v} {n = n} ⊢ᵥ (⊢-ƛ {e = e} {τₓ = τₓ} {τₑ} ⊢ₑ) with ·-preserve {!!} ⊢ₑ
  ... | x = ⊢-ƛ {!!}
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
