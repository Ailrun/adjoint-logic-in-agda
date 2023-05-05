------------------------------------------------------------
-- Syntax for Linear Lambda Calculus DILL [Barber & Plotkin 1996]
------------------------------------------------------------

{-# OPTIONS --safe #-}
module Calculus.LinearLambda.Syntax where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Product using (_×_)

data Type : Set where
  `⊤   : Type
  _`⊸_ : Type → Type → Type
  `!_  : Type → Type

data Term : Set where
  `unit          : Term

  `bang          : Term → Term
  `let-bang_`in_ : Term → Term → Term

  `λ⦂_∘_         : Type → Term → Term
  _`$_           : Term → Term → Term

  `#¹_           : ℕ → Term
  `#⁰_           : ℕ → Term

Useable = Bool
ContextEntry⁰ = Type × Useable
Context⁰ = List ContextEntry⁰
Context¹ = List Type

variable
  x x′ x″ x‴ x₀ x₁ x₂ x₃ y y′ y″ y‴ y₀ y₁ y₂ y₃ u u′ u″ u‴ u₀ u₁ u₂ u₃ v v′ v″ v‴ v₀ v₁ v₂ v₃ : ℕ
  d d′ d″ d‴ d₀ d₁ d₂ d₃ dP dP′ dP″ dP‴ dP₀ dP₁ dP₂ dP₃ dQ dQ′ dQ″ dQ‴ dQ₀ dQ₁ dQ₂ dQ₃ : Bool

module Variables where
  variable
    P P′ P″ P‴ P₀ P₁ P₂ P₃ Q Q′ Q″ Q‴ Q₀ Q₁ Q₂ Q₃ : Type
    I I′ I″ I‴ I₀ I₁ I₂ I₃ J J′ J″ J‴ J₀ J₁ J₂ J₃ K K′ K″ K‴ K₀ K₁ K₂ K₃ : Term
    ψ₀ ψ₀′ ψ₀″ ψ₀‴ ψ₀₀ ψ₀₁ ψ₀₂ ψ₀₃ : Context⁰
    ψ₁ ψ₁′ ψ₁″ ψ₁‴ ψ₁₀ ψ₁₁ ψ₁₂ ψ₁₃ : Context¹

open Variables public
