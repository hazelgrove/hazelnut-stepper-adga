open import Base
open import Statics
open import Dynamics
open import Data.Product using (∃-syntax; _,_; _×_)
open import Data.Unit using (⊤)

module Normalization where

data _halts : Exp → Set where
  halt : ∀ {e v}
    → (E : e ⇥* v)
    → (V : v value)
    → e halts

value-halts : ∀ {v : Exp} → v value → v halts
value-halts V-ƛ = halt (init (done V-ƛ)) V-ƛ
value-halts V-# = halt (init (done V-#)) V-#

reachable : ∀ (τ : Typ) (e : Exp) → Set
reachable τ e = (∅ ⊢ e ∶ τ) × (e halts) × (ρ τ e)
  where
    ρ : (τ : Typ) (e : Exp) → Set
    ρ (τₓ ⇒ τₑ) e = (∀ x → reachable τₓ x → reachable τₑ (applyₑ e 0 x))
    ρ Ν e = ⊤

reachable-halts : ∀ {e τ} → reachable τ e → e halts
reachable-halts (⊢ , H , ρ) = H

reachable-typed : ∀ {e τ} → reachable τ e → ∅ ⊢ e ∶ τ
reachable-typed (⊢ , H , ρ) = ⊢



→-preserve-halting : ∀ {e e′} → e ⇥ e′ → (e halts → e′ halts)
→-preserve-halting (step I D A T C) (halt (init (step I₁ D₁ A₁ T₁ C₁)) V) = halt (init (step {!I₁!} {!!} {!!} {!!} {!!})) V
→-preserve-halting (step I D A T C) (halt (init (skip I₁ D₁ A₁ T₁ C₁ x)) V) = {!!}
→-preserve-halting (step I D A T C) (halt (init (done x)) V) = {!!}
→-preserve-halting (step I D A T C) (halt (next x x₁) V) = {!!}
→-preserve-halting (skip I D A T C S) H = {!!}
→-preserve-halting (done x) H = {!!}
