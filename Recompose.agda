module Recompose where

open import Base
open import Ctx
open import Match using (strip-δ; _matches?_)
open import Decompose
open import Data.List using ([]; _∷_; length)
open import Data.Nat using (suc; _≤?_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; trans)
open import Relation.Nullary using (yes; no)

compose-cong : ∀ C {e e′}
  → strip-δ e ≡ strip-δ e′
  → strip-δ (compose C e) ≡ strip-δ (compose C e′)
compose-cong ∘        eq = eq
compose-cong (c ·ₗ r) eq = compose-cong c (cong (_`· strip-δ r) eq)
compose-cong (l ·ᵣ c) eq = compose-cong c (cong (strip-δ l `·_) eq)
compose-cong (c +ₗ r) eq = compose-cong c (cong (_`+ strip-δ r) eq)
compose-cong (l +ᵣ c) eq = compose-cong c (cong (strip-δ l `+_) eq)
compose-cong (φ f c)  eq = compose-cong c (cong (φ f) eq)
compose-cong (δ r c)  eq = compose-cong c eq

lookup-ctx : ∀ Φ e s x
  → strip-δ (compose (ctx (lookup Φ e s)) x) ≡ strip-δ (compose (ctx s) x)
lookup-ctx [] e s x = refl
lookup-ctx ((p , b , g) ∷ Φ) e (state a l i C) x with suc (length Φ) ≤? i
... | yes _ = refl
... | no  _ with p matches? e
...   | no  _ = lookup-ctx Φ e (state a l i C) x
...   | yes _ with g | bump (a , l) (b , suc (length Φ))
...     | 𝟙 | (a′ , l′) = lookup-ctx Φ e (state a′ l′ i C) x
...     | ⋆ | (a′ , l′) = compose-cong C refl

lookup-ctx′ : ∀ Φ e s {s′}
  → lookup Φ e s ≡ s′
  → ∀ x → strip-δ (compose (ctx s′) x) ≡ strip-δ (compose (ctx s) x)
lookup-ctx′ Φ e s L x =
  subst (λ C′ → strip-δ (compose C′ x) ≡ strip-δ (compose (ctx s) x))
    (cong ctx L) (lookup-ctx Φ e s x)

keep-ctx : ∀ i r C e → strip-δ (compose (keep i r C) e) ≡ strip-δ (compose C (δ r e))
keep-ctx i (b , n) C e with n ≤? i
... | yes _ = compose-cong C refl
... | no  _ = refl

recompose : ∀ {Φ s e C′ r t}
  → (Φ , s) ⊢ e ⇛ C′ ⟨ r ⟩ ⊣ t
  → strip-δ (compose C′ r) ≡ strip-δ (compose (ctx s) e)
recompose {Φ} {s} {e} (D-ξ-·ₗ L D) =
  trans (recompose D) (lookup-ctx′ Φ e s L e)
recompose {Φ} {s} {e} (D-ξ-·ᵣ L D) =
  trans (recompose D) (lookup-ctx′ Φ e s L e)
recompose {Φ} {s} {e} (D-β-· _ _ L) =
  lookup-ctx′ Φ e s L e
recompose {Φ} {s} {e} (D-ξ-+ₗ L D) =
  trans (recompose D) (lookup-ctx′ Φ e s L e)
recompose {Φ} {s} {e} (D-ξ-+ᵣ L D) =
  trans (recompose D) (lookup-ctx′ Φ e s L e)
recompose {Φ} {s} {e} (D-β-+ _ _ L) =
  lookup-ctx′ Φ e s L e
recompose (D-ξ-φ D) = recompose D
recompose (D-β-φ _) = refl
recompose {s = s} {e = δ r e} (D-ξ-δ _ D) =
  trans (recompose D) (keep-ctx (ins-lvl s) r (ctx s) e)
recompose (D-β-δ _ _) = refl
recompose {Φ} {s} {e} (D-β-μ L) =
  lookup-ctx′ Φ e s L e

recompose-top : ∀ {e C′ r t}
  → ([] , state ∥ 0 0 ∘) ⊢ e ⇛ C′ ⟨ r ⟩ ⊣ t
  → strip-δ (compose C′ r) ≡ strip-δ e
recompose-top = recompose
