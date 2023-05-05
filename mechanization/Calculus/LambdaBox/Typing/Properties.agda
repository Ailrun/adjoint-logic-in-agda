------------------------------------------------------------
-- Properties of Static Rules of λ□
------------------------------------------------------------

{-# OPTIONS --safe #-}
module Calculus.LambdaBox.Typing.Properties where

open import Data.Nat as ℕ using (ℕ; suc; s≤s; _+_)
open import Data.Nat.Properties as ℕ
open import Data.List using (List; []; _∷_; _++_; length)

open import Calculus.LambdaBox.Syntax
open import Calculus.LambdaBox.Typing

∈-++ˡ : ∀ Φ₁ →
        x ⦂ A ∈ Φ₀ →
        -----------------------------
        length Φ₁ + x ⦂ A ∈ Φ₁ ++ Φ₀
∈-++ˡ {x = x} []       x∈
  rewrite ℕ.+-identityʳ x     = x∈
∈-++ˡ {x = x} (B ∷ Φ₁) x∈
  rewrite +-suc x (length Φ₁) = there (∈-++ˡ Φ₁ x∈)

∈-++ʳ : ∀ Φ₀ →
        x ⦂ A ∈ Φ₁ →
        -----------------
        x ⦂ A ∈ Φ₁ ++ Φ₀
∈-++ʳ Φ₀ here       = here
∈-++ʳ Φ₀ (there x∈) = there (∈-++ʳ Φ₀ x∈)

>∈-++⇒∈ : ∀ Φ₁ →
          length Φ₁ ℕ.> x →
          x ⦂ A ∈ Φ₁ ++ Φ₀ →
          -------------------
          x ⦂ A ∈ Φ₁
>∈-++⇒∈ (_ ∷ Φ₁) >x       here       = here
>∈-++⇒∈ (_ ∷ Φ₁) (s≤s >x) (there x∈) = there (>∈-++⇒∈ Φ₁ >x x∈)

⊢⇒++⊢ : ∀ Ψ₀₀ →
        Ψ₁ ⍮ Ψ₀₁ ⊢ E ⦂ A →
        ------------------------
        Ψ₁ ⍮ Ψ₀₁ ++ Ψ₀₀ ⊢ E ⦂ A
⊢⇒++⊢ Ψ₀₀ `unit                = `unit
⊢⇒++⊢ Ψ₀₀ (`box ⊢E)            = `box ⊢E
⊢⇒++⊢ Ψ₀₀ (`let-box ⊢E `in ⊢F) = `let-box ⊢⇒++⊢ Ψ₀₀ ⊢E `in ⊢⇒++⊢ Ψ₀₀ ⊢F
⊢⇒++⊢ Ψ₀₀ (`λ⦂-∙ ⊢E)           = `λ⦂-∙ ⊢⇒++⊢ Ψ₀₀ ⊢E
⊢⇒++⊢ Ψ₀₀ (⊢E `$ ⊢F)           = ⊢⇒++⊢ Ψ₀₀ ⊢E `$ ⊢⇒++⊢ Ψ₀₀ ⊢F
⊢⇒++⊢ Ψ₀₀ (`#¹ u∈)             = `#¹ u∈
⊢⇒++⊢ Ψ₀₀ (`#⁰ x∈)             = `#⁰ ∈-++ʳ Ψ₀₀ x∈
