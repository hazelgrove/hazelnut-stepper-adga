module Progress where

open import Base
open import Ctx using (_·ₗ_; _·ᵣ_; _+ₗ_; _+ᵣ_; φ)
open import Decompose
open import Statics
open import Transition
open import Data.List using (_∷_)
open import Data.Nat using (ℕ; _⊔_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Nullary using (¬_)

data ⇛-Progress (s : Filters × State) (e : Exp) : Set where
  ⇛-V : (V : e value)
    → ⇛-Progress s e

  ⇛-D : ∀ {o t}
    → (D : s ⊢ e ⇛ o ⊣ t)
    → ⇛-Progress s e

value-final : ∀ {s v o t} → v value → ¬ (s ⊢ v ⇛ o ⊣ t)
value-final V-ƛ ()
value-final V-# ()

progress : ∀ {Φ s e τ} → ∅ ⊢[ e ]∶ τ → ⇛-Progress (Φ , s) e
progress (⊢-` ())
progress (⊢-ƛ _) = ⇛-V V-ƛ
progress ⊢-# = ⇛-V V-#
progress {Φ} {s} {eₗ `· eᵣ} (⊢-· ⊢ₗ ⊢ᵣ)
  with lookup Φ (eₗ `· eᵣ) s in L
... | s′ with progress {Φ} {record s′ { ctx = ctx s′ ·ₗ eᵣ }} ⊢ₗ
...   | ⇛-D D = ⇛-D (D-ξ-·ₗ L D)
...   | ⇛-V Vₗ with progress {Φ} {record s′ { ctx = eₗ ·ᵣ ctx s′ }} ⊢ᵣ
...     | ⇛-D D = ⇛-D (D-ξ-·ᵣ L D)
...     | ⇛-V Vᵣ = ⇛-D (D-β-· Vₗ Vᵣ L)
progress {Φ} {s} {eₗ `+ eᵣ} (⊢-+ ⊢ₗ ⊢ᵣ)
  with lookup Φ (eₗ `+ eᵣ) s in L
... | s′ with progress {Φ} {record s′ { ctx = ctx s′ +ₗ eᵣ }} ⊢ₗ
...   | ⇛-D D = ⇛-D (D-ξ-+ₗ L D)
...   | ⇛-V Vₗ with progress {Φ} {record s′ { ctx = eₗ +ᵣ ctx s′ }} ⊢ᵣ
...     | ⇛-D D = ⇛-D (D-ξ-+ᵣ L D)
...     | ⇛-V Vᵣ = ⇛-D (D-β-+ Vₗ Vᵣ L)
progress {Φ} {s} {φ f e} (⊢-φ _ ⊢ₑ)
  with progress {f ∷ Φ} {record s { ctx = φ f (ctx s) }} ⊢ₑ
... | ⇛-D D = ⇛-D (D-ξ-φ D)
... | ⇛-V V = ⇛-D (D-β-φ V)
progress {Φ} {s} {δ (b , n) e} (⊢-δ ⊢ₑ) with bump (act s , act-lvl s) (b , n) in B
... | (a′ , l′) with progress {Φ}
  {state a′ l′ (n ⊔ ins-lvl s) (keep (ins-lvl s) (b , n) (ctx s))} ⊢ₑ
...   | ⇛-D D = ⇛-D (D-ξ-δ B D)
...   | ⇛-V V = ⇛-D (D-β-δ V B)
progress {Φ} {s} {μ e} (⊢-μ _) with lookup Φ (μ e) s in L
... | s′ = ⇛-D (D-β-μ L)

⇛-progress : ∀ {s e τ C′ r t}
  → ∅ ⊢[ e ]∶ τ
  → s ⊢ e ⇛ C′ ⟨ r ⟩ ⊣ t
  → ∃[ r′ ] r —→ r′
⇛-progress (⊢-· ⊢ₗ _) (D-ξ-·ₗ _ D) = ⇛-progress ⊢ₗ D
⇛-progress (⊢-· _ ⊢ᵣ) (D-ξ-·ᵣ _ D) = ⇛-progress ⊢ᵣ D
⇛-progress (⊢-· (⊢-ƛ _) _) (D-β-· V-ƛ Vᵣ _) = _ , T-β-· Vᵣ
⇛-progress (⊢-+ ⊢ₗ _) (D-ξ-+ₗ _ D) = ⇛-progress ⊢ₗ D
⇛-progress (⊢-+ _ ⊢ᵣ) (D-ξ-+ᵣ _ D) = ⇛-progress ⊢ᵣ D
⇛-progress (⊢-+ ⊢-# ⊢-#) (D-β-+ V-# V-# _) = _ , T-β-+
⇛-progress (⊢-φ _ ⊢ₑ) (D-ξ-φ D) = ⇛-progress ⊢ₑ D
⇛-progress (⊢-φ _ _) (D-β-φ V) = _ , T-β-φ V
⇛-progress (⊢-δ ⊢ₑ) (D-ξ-δ _ D) = ⇛-progress ⊢ₑ D
⇛-progress (⊢-δ _) (D-β-δ V _) = _ , T-β-δ V
⇛-progress (⊢-μ _) (D-β-μ _) = _ , T-β-μ
