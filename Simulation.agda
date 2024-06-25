open import Base
open import Dynamics
open import Match
open import Data.Product using (∃-syntax; _,_; _×_)
open import Data.Nat using (z≤n)

module Simulation where

data _∼_ : Exp → Exp → Set where
  ∼` : ∀ {x}
    → (` x) ∼ (` x)

  ∼ƛ : ∀ {e e†}
    → e ∼ e†
    → (ƛ e) ∼ (ƛ e†)

  _∼·_ : ∀ {eₗ eᵣ eₗ† eᵣ†}
    → eₗ ∼ eₗ†
    → eᵣ ∼ eᵣ†
    → (eₗ `· eᵣ) ∼ (eₗ† `· eᵣ†)

  ∼# : ∀ {n}
    → (# n) ∼ (# n)

  _∼+_ : ∀ {eₗ eᵣ eₗ† eᵣ†}
    → eₗ ∼ eₗ†
    → eᵣ ∼ eᵣ†
    → (eₗ `+ eᵣ) ∼ (eₗ† `+ eᵣ†)

  ∼φ : ∀ {f e}
    → (φ f e) ∼ e

  ∼δ : ∀ {r e}
    → (δ r e) ∼ e

sim : ∀ {e e† e′ : Exp}
  → ((e ∼ e†) × (e ⇥ e′))
  → ∃[ e′† ](e′ ∼ e′† × e† ↦* e′†)
sim (∼` , step (I-`-⊤ M-E) (D-ξ-δ ()) A T C)
sim (∼` , step (I-`-⊤ M-E) (D-β-δ ()) A T C)
sim (∼` , skip (I-`-⊤ M-E) (D-ξ-δ ()) A T C S)
sim (∼` , skip (I-`-⊤ M-E) (D-β-δ ()) A T C S)
sim (∼ƛ R , step (I-V V-ƛ) () A T C)
sim (∼ƛ R , skip (I-V V-ƛ) () A T C S)
sim (∼ƛ {e} {e†} R , done V-ƛ) = ƛ e† , ∼ƛ R , init
sim ((Rₗ ∼· Rᵣ) , step (I-·-⊤ M I I₁) (D-ξ-δ (D-ξ-·ₗ D)) A T C) = {!!} , {!!} , {!!}
sim ((Rₗ ∼· Rᵣ) , step (I-·-⊤ M I I₁) (D-ξ-δ (D-ξ-·ᵣ V D)) A T C) = {!!} , {!!} , {!!}
sim ((Rₗ ∼· Rᵣ) , step (I-·-⊤ M I I₁) (D-ξ-δ (D-β-· Vₗ Vᵣ)) A T C) = {!!} , {!!} , {!!}
sim ((Rₗ ∼· Rᵣ) , step (I-·-⊥ ¬M I I₁) D A T C) = {!!} , {!!} , {!!}
sim ((Rₗ ∼· Rᵣ) , skip I D A T C S) = {!!} , {!!} , {!!}
sim (∼# , S) = {!!}
sim ((R ∼+ R₁) , S) = {!!}
sim (∼φ , S) = {!!}
sim (∼δ , S) = {!!}
