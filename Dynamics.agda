open import Core
open import Subst
open import Match
open import Data.Integer using (+_)
open import Data.Nat using (ℕ; _≤?_; _>_; _≤_)
open import Data.Nat.Properties using (≰⇒>)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_; yes; no)

module Dynamics where
  infix 0 _—→_

  data _—→_ : Exp → Exp → Set where
    T-β-· : ∀ {v e}
      → v value
      → (ƛ e) · v —→ ↓ 0 1 ([ (↑ 0 1 v) / 0 ] e)

    T-β-φ : ∀ {f v}
      → v value
      → (φ f v) —→ v

    T-β-δ : ∀ {r v}
      → v value
      → (δ r v) —→ v

  data Ctx : Set where
    ∘    : Ctx
    _·ₗ_ : Ctx → Exp → Ctx
    _·ᵣ_ : Exp → Ctx → Ctx
    _+ₗ_ : Ctx → Exp → Ctx
    _+ᵣ_ : Exp → Ctx → Ctx
    φ    : Filter  → Ctx → Ctx
    δ    : Residue → Ctx → Ctx

  data _⇒_⟨_⟩ : Exp → Ctx → Exp → Set where
    D-β-` : ∀ {x}
      → (` x) ⇒ ∘ ⟨ (` x) ⟩

    D-ξ-·-l : ∀ {eₗ eᵣ ℰ eₗ′}
      → eₗ ⇒ ℰ ⟨ eₗ′ ⟩
      → (eₗ · eᵣ) ⇒ (ℰ ·ₗ eᵣ) ⟨ eₗ′ ⟩

    D-ξ-·-r : ∀ {vₗ eᵣ ℰ eᵣ′}
      → vₗ value
      → eᵣ ⇒ ℰ ⟨ eᵣ′ ⟩
      → (vₗ · eᵣ) ⇒ (vₗ ·ᵣ ℰ) ⟨ eᵣ′ ⟩

    D-β-· : ∀ {vₗ vᵣ}
      → vₗ value
      → vᵣ value
      → (vₗ · vᵣ) ⇒ ∘ ⟨ vₗ · vᵣ ⟩

    D-ξ-+-l : ∀ {eₗ eᵣ ℰ eₗ′}
      → (D : eₗ ⇒ ℰ ⟨ eₗ′ ⟩)
      → (eₗ + eᵣ) ⇒ (ℰ +ₗ eᵣ) ⟨ eₗ′ ⟩

    D-ξ-+-r : ∀ {vₗ eᵣ ℰ eᵣ′}
      → (V : vₗ value)
      → (D : eᵣ ⇒ ℰ ⟨ eᵣ′ ⟩)
      → (vₗ + eᵣ) ⇒ (vₗ +ᵣ ℰ) ⟨ eᵣ′ ⟩

    D-β-+ : ∀ {vₗ vᵣ}
      → (Vₗ : vₗ value)
      → (Vᵣ : vᵣ value)
      → (vₗ + vᵣ) ⇒ ∘ ⟨ vₗ + vᵣ ⟩

    D-ξ-φ : ∀ {f e ℰ e′}
      → (D : e ⇒ ℰ ⟨ e′ ⟩)
      → (φ f e) ⇒ (φ f ℰ) ⟨ e′ ⟩

    D-β-φ : ∀ {f v}
      → (V : v value)
      → (φ f v) ⇒ ∘ ⟨ φ f v ⟩

    D-ξ-δ : ∀ {r e ℰ e′}
      → (D : e ⇒ ℰ ⟨ e′ ⟩)
      → (δ r e) ⇒ (δ r ℰ) ⟨ e′ ⟩

    D-β-δ : ∀ {r v}
      → (V : v value)
      → (δ r v) ⇒ ∘ ⟨ δ r v ⟩

  data _⇐_⟨_⟩ : Exp → Ctx → Exp → Set where
    C-∘ : ∀ {e}
      → e ⇐ ∘ ⟨ e ⟩

    C-·-l : ∀ {εₗ eᵣ eₗ e}
      → eₗ ⇐ εₗ ⟨ e ⟩
      → (eₗ · eᵣ) ⇐ (εₗ ·ₗ eᵣ) ⟨ e ⟩

    C-·-r : ∀ {eₗ εᵣ eᵣ e}
      → eᵣ ⇐ εᵣ ⟨ e ⟩
      → (eₗ · eᵣ) ⇐ (eₗ ·ᵣ εᵣ) ⟨ e ⟩

    C-+-l : ∀ {εₗ eᵣ eₗ e}
      → eₗ ⇐ εₗ ⟨ e ⟩
      → (eₗ + eᵣ) ⇐ (εₗ +ₗ eᵣ) ⟨ e ⟩

    C-+-r : ∀ {eₗ εᵣ eᵣ e}
      → eᵣ ⇐ εᵣ ⟨ e ⟩
      → (eₗ + eᵣ) ⇐ (eₗ +ᵣ εᵣ) ⟨ e ⟩

    C-φ : ∀ {pag ε e e′}
      → e′ ⇐ ε ⟨ e ⟩
      → (φ pag  e′) ⇐ (φ pag  ε) ⟨ e ⟩

    C-δ : ∀ {agl ε e e′}
      → e′ ⇐ ε ⟨ e ⟩
      → (δ agl  e′) ⇐ (δ agl  ε) ⟨ e ⟩

  data _⊢_⇝_ : Pat × Act × Gas × ℕ → Exp → Exp → Set where
    I-V : ∀ {pagl v}
      → v value
      → pagl ⊢ v ⇝ v

    I-`-⊤ : ∀ {p a g l x}
      → p matches (` x)
      → (p , a , g , l) ⊢ (` x) ⇝ (δ (a , g , l) (` x))

    I-`-⊥ : ∀ {p a g l x}
      → ¬ (p matches (` x))
      → (p , a , g , l) ⊢ (` x) ⇝ (` x)

    I-·-⊤ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
      → p matches (eₗ · eᵣ)
      → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
      → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
      → (p , a , g , l) ⊢ (eₗ · eᵣ) ⇝ (δ (a , g , l) (eₗ′ · eᵣ′))

    I-·-⊥ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
      → ¬ (p matches (eₗ · eᵣ))
      → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
      → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
      → (p , a , g , l) ⊢ (eₗ · eᵣ) ⇝ (eₗ′ · eᵣ′)

    I-+-⊤ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
      → p matches (eₗ + eᵣ)
      → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
      → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
      → (p , a , g , l) ⊢ (eₗ + eᵣ) ⇝ (δ (a , g , l) (eₗ′ + eᵣ′))

    I-+-⊥ : ∀ {p a g l eₗ eᵣ eₗ′ eᵣ′}
      → ¬ (p matches (eₗ + eᵣ))
      → (p , a , g , l) ⊢ eₗ ⇝ eₗ′
      → (p , a , g , l) ⊢ eᵣ ⇝ eᵣ′
      → (p , a , g , l) ⊢ (eₗ + eᵣ) ⇝ (eₗ′ + eᵣ′)

    I-φ : ∀ {pat act gas lvl p a g e e′ e″}
      → (pat , act , gas , lvl) ⊢ e ⇝ e′
      → (p , a , g , ℕ.suc lvl) ⊢ e′ ⇝ e″
      → (pat , act , gas , lvl) ⊢ (φ (p , a , g) e) ⇝ (φ (p , a , g) e″)

    I-δ : ∀ {pat act gas lvl a g l e e′}
      → (pat , act , gas , lvl) ⊢ e ⇝ e′
      → (pat , act , gas , lvl) ⊢ (δ (a , g , l) e) ⇝ (δ (a , g , l) e′)

  decay : Ctx → Ctx
  decay ∘ = ∘
  decay (ε ·ₗ e) = (decay ε) ·ₗ e
  decay (e ·ᵣ ε) = e ·ᵣ (decay ε)
  decay (ε +ₗ e) = (decay ε) +ₗ e
  decay (e +ᵣ ε) = e +ᵣ (decay ε)
  decay (φ f  ε) = decay ε
  decay (δ r  ε) = decay ε

  select : Act → ℕ → Ctx → Act
  select act lvl ∘ = act
  select act lvl (c ·ₗ e) = select act lvl c
  select act lvl (e ·ᵣ c) = select act lvl c
  select act lvl (c +ₗ e) = select act lvl c
  select act lvl (e +ᵣ c) = select act lvl c
  select act lvl (φ f c) = select act lvl c
  select act lvl (δ (a , g , l) c) with l ≤? lvl
  ... | yes _ = select act lvl c
  ... | no  _ = select a l c

  data _⊢_⊣_ : Act × ℕ → Ctx → Act → Set where
    A-∘ : ∀ {act lvl}
      → (act , lvl) ⊢ ∘ ⊣ act

    A-·-l : ∀ {act lvl εₗ eᵣ act′}
      → (act , lvl) ⊢ εₗ ⊣ act′
      → (act , lvl) ⊢ (εₗ ·ₗ eᵣ) ⊣ act′

    A-·-r : ∀ {act lvl eₗ εᵣ act′}
      → (act , lvl) ⊢ εᵣ ⊣ act′
      → (act , lvl) ⊢ (eₗ ·ᵣ εᵣ) ⊣ act′

    A-+-l : ∀ {act lvl εₗ eᵣ act′}
      → (act , lvl) ⊢ εₗ ⊣ act′
      → (act , lvl) ⊢ (εₗ +ₗ eᵣ) ⊣ act′

    A-+-r : ∀ {act lvl eₗ εᵣ act′}
      → (act , lvl) ⊢ εᵣ ⊣ act′
      → (act , lvl) ⊢ (eₗ +ᵣ εᵣ) ⊣ act′

    A-φ : ∀ {act lvl ε act′ pag}
      → (act , lvl) ⊢ ε ⊣ act′
      → (act , lvl) ⊢ φ pag ε ⊣ act′

    A-Δ-> : ∀ {act lvl ε act′ a g l}
      → l > lvl
      → (a , l) ⊢ ε ⊣ act′
      → (act , lvl) ⊢ δ (a , g , l)  ε ⊣ act′

    A-Δ-≤ : ∀ {act lvl ε act′ a g l}
      → l ≤ lvl
      → (act , lvl) ⊢ ε ⊣ act′
      → (act , lvl) ⊢ δ (a , g , l)  ε ⊣ act′

  ⊢⊣-select : ∀ {a l ε}
    → (a , l) ⊢ ε ⊣ (select a l ε)
  ⊢⊣-select {ε = ∘} = A-∘
  ⊢⊣-select {ε = ε ·ₗ e} = A-·-l ⊢⊣-select
  ⊢⊣-select {ε = e ·ᵣ ε} = A-·-r ⊢⊣-select
  ⊢⊣-select {ε = ε +ₗ e} = A-+-l ⊢⊣-select
  ⊢⊣-select {ε = e +ᵣ ε} = A-+-r ⊢⊣-select
  ⊢⊣-select {ε = φ f  ε} = A-φ ⊢⊣-select
  ⊢⊣-select {a = act} {l = lvl} {ε = δ (a , _ , l)  ε} with (l ≤? lvl)
  ... | yes ≤ = (A-Δ-≤ ≤) ⊢⊣-select
  ... | no  ≰ = A-Δ-> (≰⇒> ≰) ⊢⊣-select

  data _⊢_⇥_ : Pat × Act × Gas × ℕ → Exp → Exp → Set where
    step : ∀ {p a g l e e′ eᵢ e₀ e₀′ ε₀}
      → (I : (p , a , g , l) ⊢ e ⇝ eᵢ)
      → (D : eᵢ ⇒ ε₀ ⟨ e₀ ⟩)
      → (A : (a , l) ⊢ ε₀ ⊣ ∥)
      → (T : e₀ —→ e₀′)
      → (C : e′ ⇐ (decay ε₀) ⟨ e₀′ ⟩)
      → (p , a , g , l) ⊢ e ⇥ e′

    skip : ∀ {p a g l e e′ e″ eᵢ e₀ e₀′ ε₀}
      → (I : (p , a , g , l) ⊢ e ⇝ eᵢ)
      → (D : eᵢ ⇒ ε₀ ⟨ e₀ ⟩)
      → (A : e₀ filter ⊎ (a , l) ⊢ ε₀ ⊣ ⊳)
      → (T : e₀ —→ e₀′)
      → (C : e′ ⇐ (decay ε₀) ⟨ e₀′ ⟩)
      → (R : (p , a , g , l) ⊢ e′ ⇥ e″)
      → (p , a , g , l) ⊢ e ⇥ e″

    done : ∀ {p a g l v}
      → v value
      → (p , a , g , l) ⊢ v ⇥ v
