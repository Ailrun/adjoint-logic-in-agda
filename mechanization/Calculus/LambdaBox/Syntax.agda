{-# OPTIONS --safe #-}
module Calculus.LambdaBox.Syntax where

open import Data.Nat using (ℕ)
open import Data.List using (List)

data Type : Set where
  `⊤   : Type
  _`→_ : Type → Type → Type
  `□_  : Type → Type

data Term : Set where
  `unit         : Term

  `box          : Term → Term
  `let-box_`in_ : Term → Term → Term

  `λ⦂_∙_        : Type → Term → Term
  _`$_          : Term → Term → Term

  `#¹_          : ℕ → Term
  `#⁰_          : ℕ → Term

Context : Set
Context = List Type

variable
  x x′ x″ x‴ x₀ x₁ x₂ x₃ y y′ y″ y‴ y₀ y₁ y₂ y₃ u u′ u″ u‴ u₀ u₁ u₂ u₃ v v′ v″ v‴ v₀ v₁ v₂ v₃ : ℕ

module Variables where
  variable
    A A′ A″ A‴ A₀ A₁ A₂ A₃ B B′ B″ B‴ B₀ B₁ B₂ B₃ : Type
    E E′ E″ E‴ E₀ E₁ E₂ E₃ F F′ F″ F‴ F₀ F₁ F₂ F₃ G G′ G″ G‴ G₀ G₁ G₂ G₃ : Term
    Ψ₀ Ψ₀₀ Ψ₀₁ Ψ₀₂ Ψ₀₃ Ψ₀′ Ψ₀″ Ψ₀‴ Ψ₁ Ψ₁′ Ψ₁″ Ψ₁‴ Ψ₁₀ Ψ₁₁ Ψ₁₂ Ψ₁₃ Φ Φ′ Φ″ Φ‴ Φ₀ Φ₁ Φ₂ Φ₃ : Context

open Variables public
