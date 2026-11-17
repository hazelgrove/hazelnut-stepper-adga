module Step where

open import Base
open import Ctx
open import Decompose
open import Transition
open import Data.List using ([])
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)

top : Filters × State
top = [] , state ∥ 0 0 ∘

infix 0 _⇥_

data _⇥_ : Exp → Exp → Set where
  S-Step : ∀ {e C r r′ l}
    → (D : top ⊢ e ⇛ C ⟨ r ⟩ ⊣ (∥ , l))
    → (P : ∀ {o l′} → ¬ (top ⊢ e ⇛ o ⊣ (⊳ , l′)))
    → (T : r —→ r′)
    → e ⇥ compose C r′

  S-Skip : ∀ {e C r r′ l e′}
    → (D : top ⊢ e ⇛ C ⟨ r ⟩ ⊣ (⊳ , l))
    → (T : r —→ r′)
    → (S : compose C r′ ⇥ e′)
    → e ⇥ e′

  S-Value : ∀ {v}
    → (V : v value)
    → v ⇥ v
