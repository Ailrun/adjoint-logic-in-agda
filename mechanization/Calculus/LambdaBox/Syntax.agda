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
  S S′ S″ S‴ S₀ S₁ S₂ S₃ T T′ T″ T‴ T₀ T₁ T₂ T₃ : Type
  L L′ L″ L‴ L₀ L₁ L₂ L₃ M M′ M″ M‴ M₀ M₁ M₂ M₃ N N′ N″ N‴ N₀ N₁ N₂ N₃ : Term
  Γ Γ′ Γ″ Γ‴ Γ₀ Γ₁ Γ₂ Γ₃ Δ Δ′ Δ″ Δ‴ Δ₀ Δ₁ Δ₂ Δ₃ Ψ Ψ′ Ψ″ Ψ‴ Ψ₀ Ψ₁ Ψ₂ Ψ₃ : Context
