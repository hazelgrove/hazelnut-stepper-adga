module Decompose where

open import Base
open import Ctx
open import Match
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; suc; _≤?_; _⊔_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)

Filters : Set
Filters = List Filter

record State : Set where
  constructor state
  field
    act     : Act
    act-lvl : ℕ
    ins-lvl : ℕ
    ctx     : Ctx

open State public

bump : Act × ℕ → Act × ℕ → Act × ℕ
bump (a , l) (b , n) with n ≤? l
... | yes _ = (a , l)
... | no  _ = (b , n)

lookup : Filters → Exp → State → State
lookup [] e s = s
lookup ((p , b , g) ∷ Φ) e (state a l i C) with suc (length Φ) ≤? i
... | yes _ = state a l i C
... | no  _ with p matches? e
...   | no  _ = lookup Φ e (state a l i C)
...   | yes _ with g | bump (a , l) (b , suc (length Φ))
...     | 𝟙 | (a′ , l′) = lookup Φ e (state a′ l′ i C)
...     | ⋆ | (a′ , l′) =
              state a′ l′ (suc (length Φ)) (δ (b , suc (length Φ)) C)

keep : ℕ → Residue → Ctx → Ctx
keep i (b , n) C with n ≤? i
... | yes _ = C
... | no  _ = δ (b , n) C

infixr 1 _⟨_⟩

data Obj : Set where
  _⟨_⟩ : Ctx → Exp → Obj

infix 0 _⊢_⇛_⊣_

data _⊢_⇛_⊣_ : Filters × State → Exp → Obj → Act × ℕ → Set where
  D-ξ-·ₗ : ∀ {Φ s s′ eₗ eᵣ o t}
    → (L : lookup Φ (eₗ `· eᵣ) s ≡ s′)
    → (D : (Φ , record s′ { ctx = ctx s′ ·ₗ eᵣ }) ⊢ eₗ ⇛ o ⊣ t)
    → (Φ , s) ⊢ eₗ `· eᵣ ⇛ o ⊣ t

  D-ξ-·ᵣ : ∀ {Φ s s′ eₗ eᵣ o t}
    → (L : lookup Φ (eₗ `· eᵣ) s ≡ s′)
    → (D : (Φ , record s′ { ctx = eₗ ·ᵣ ctx s′ }) ⊢ eᵣ ⇛ o ⊣ t)
    → (Φ , s) ⊢ eₗ `· eᵣ ⇛ o ⊣ t

  D-β-· : ∀ {Φ s s′ vₗ vᵣ}
    → (Vₗ : vₗ value)
    → (Vᵣ : vᵣ value)
    → (L : lookup Φ (vₗ `· vᵣ) s ≡ s′)
    → (Φ , s) ⊢ vₗ `· vᵣ ⇛ ctx s′ ⟨ vₗ `· vᵣ ⟩ ⊣ (act s′ , act-lvl s′)

  D-ξ-+ₗ : ∀ {Φ s s′ eₗ eᵣ o t}
    → (L : lookup Φ (eₗ `+ eᵣ) s ≡ s′)
    → (D : (Φ , record s′ { ctx = ctx s′ +ₗ eᵣ }) ⊢ eₗ ⇛ o ⊣ t)
    → (Φ , s) ⊢ eₗ `+ eᵣ ⇛ o ⊣ t

  D-ξ-+ᵣ : ∀ {Φ s s′ eₗ eᵣ o t}
    → (L : lookup Φ (eₗ `+ eᵣ) s ≡ s′)
    → (D : (Φ , record s′ { ctx = eₗ +ᵣ ctx s′ }) ⊢ eᵣ ⇛ o ⊣ t)
    → (Φ , s) ⊢ eₗ `+ eᵣ ⇛ o ⊣ t

  D-β-+ : ∀ {Φ s s′ vₗ vᵣ}
    → (Vₗ : vₗ value)
    → (Vᵣ : vᵣ value)
    → (L : lookup Φ (vₗ `+ vᵣ) s ≡ s′)
    → (Φ , s) ⊢ vₗ `+ vᵣ ⇛ ctx s′ ⟨ vₗ `+ vᵣ ⟩ ⊣ (act s′ , act-lvl s′)

  D-ξ-φ : ∀ {Φ s f e o t}
    → (D : ((f ∷ Φ) , record s { ctx = φ f (ctx s) }) ⊢ e ⇛ o ⊣ t)
    → (Φ , s) ⊢ φ f e ⇛ o ⊣ t

  D-β-φ : ∀ {Φ s f v}
    → (V : v value)
    → (Φ , s) ⊢ φ f v ⇛ ctx s ⟨ φ f v ⟩ ⊣ (⊳ , act-lvl s)

  D-ξ-δ : ∀ {Φ s b n e a′ l′ o t}
    → (B : bump (act s , act-lvl s) (b , n) ≡ (a′ , l′))
    → (D : (Φ , state a′ l′ (n ⊔ ins-lvl s) (keep (ins-lvl s) (b , n) (ctx s)))
             ⊢ e ⇛ o ⊣ t)
    → (Φ , s) ⊢ δ (b , n) e ⇛ o ⊣ t

  D-β-δ : ∀ {Φ s b n v a′ l′}
    → (V : v value)
    → (B : bump (act s , act-lvl s) (b , n) ≡ (a′ , l′))
    → (Φ , s) ⊢ δ (b , n) v ⇛ ctx s ⟨ δ (b , n) v ⟩ ⊣ (⊳ , l′)

  D-β-μ : ∀ {Φ s s′ e}
    → (L : lookup Φ (μ e) s ≡ s′)
    → (Φ , s) ⊢ μ e ⇛ ctx s′ ⟨ μ e ⟩ ⊣ (act s′ , act-lvl s′)
