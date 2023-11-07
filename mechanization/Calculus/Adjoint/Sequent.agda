------------------------------------------------------------
-- Adjoint Sequent Calculus
------------------------------------------------------------

{-# OPTIONS --safe #-}
open import Calculus.Elevator.ModeSpec

module Calculus.Adjoint.Sequent {ℓ₁ ℓ₂} (ℳ : ModeSpec ℓ₁ ℓ₂) where
open ModeSpec ℳ

open import Agda.Primitive
open import Data.Bool as Bool using (true; false)
open import Data.List as List using ([]; _∷_)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Nat as ℕ using (ℕ; suc)
open import Data.Product as × using (∃; _×_; _,_)
open import Relation.Nullary using (¬_)

open import Calculus.Elevator.Syntax ℳ hiding (Term)
open import Calculus.Elevator.Typing ℳ

infix   4 _⇛_/_

data _⇛_/_ : Context → Type → Mode → Set (ℓ₁ ⊔ ℓ₂) where
  `⊤R : Γ is-all-del →
        ---------------
        Γ ⇛ `⊤ / m

  ‵⊸R : (S , m , true) ∷ Γ ⇛ T / m →
        -----------------------------
        Γ ⇛ S `⊸ T / m

  ‵⊸L : Γ ~ Γ₀ ⊞ Γ₁ →
        Γ₁ ~ Γ₂ ⊞ Γ₃ →
        x ⦂[ m ] S `⊸ T ∈ Γ₀ →
        ⊢[ m ] Γ₂ →
        Γ₂ ⇛ S / m →
        (T , m , true) ∷ Γ₃ ⇛ T′ / m′ →
        --------------------------------
        Γ ⇛ T′ / m′

  `↓R : Γ ~ Γ₀ ⊞ Γ₁ →
        ⊢[ m ] Γ₀ →
        Γ₁ is-all-del →
        Γ₀ ⇛ S / m →
        ------------------------
        Γ ⇛ `↓[ m ⇒ m₀ ] S / m₀

  `↓L : Γ ~ Γ₀ ⊞ Γ₁ →
        x ⦂[ m₀ ] `↓[ m₁ ⇒ m₀ ] S ∈ Γ₀ →
        (S , m₁ , true) ∷ Γ₁ ⇛ T / m →
        ---------------------------------
        Γ ⇛ T / m

  `↑R : Γ ⇛ S / m →
        ------------------------
        Γ ⇛ `↑[ m ⇒ m₀ ] S / m₀

  `↑L : Γ ~ Γ₀ ⊞ Γ₁ →
        x ⦂[ m₀ ] `↑[ m₁ ⇒ m₀ ] S ∈ Γ₀ →
        m ≤ₘ m₁ →
        (S , m₁ , true) ∷ Γ₁ ⇛ T / m →
        ---------------------------------
        Γ ⇛ T / m

completeness : ⊢[ m ] Γ →
               ⊢[ m ] T ⦂⋆ →
               Γ ⇛ T / m →
               -----------------------
               ∃ λ t → Γ ⊢[ m ] t ⦂ T
completeness ⊢Γ ⊢T (`⊤R ΓDel) = `unit , `unit ΓDel
completeness ⊢Γ ⊢T (‵⊸R Γ⇛T) = {!!}
completeness ⊢Γ ⊢T (‵⊸L x x₁ x₂ x₃ Γ⇛T Γ⇛T₁) = {!!}
completeness ⊢Γ ⊢T (`↓R x x₁ x₂ Γ⇛T) = {!!}
completeness ⊢Γ ⊢T (`↓L x x₁ Γ⇛T) = {!!}
completeness ⊢Γ ⊢T (`↑R Γ⇛T) = {!!}
completeness ⊢Γ ⊢T (`↑L x x₁ x₂ Γ⇛T) = {!!}
