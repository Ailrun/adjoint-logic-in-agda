------------------------------------------------------------
-- Syntax of Elevator
------------------------------------------------------------

{-# OPTIONS --safe #-}
open import Calculus.AdjND.ModeSpec

module Calculus.AdjND.Syntax {ℓ₁ ℓ₂} (ℳ : ModeSpec ℓ₁ ℓ₂) where
open ModeSpec ℳ

open import Agda.Primitive
open import Data.Bool as Bool using (Bool; true; false)
open import Data.List as List using (List; []; _∷_)
open import Data.Nat as ℕ using (ℕ; suc)
open import Data.Product as × using (_×_; _,_)

data Type : Set ℓ₁ where
  `⊤ : Type
  _`⊸_ : Type → Type → Type
  `↑[_⇒_] : (m₀ : Mode) → (m₁ : Mode) → Type → Type
  `↓[_⇒_] : (m₀ : Mode) → (m₁ : Mode) → Type → Type

data Term : Set ℓ₁ where
  `unit                 : Term

  `lift[_⇒_]            : (m₀ : Mode) → (m₁ : Mode) → Term → Term
  `unlift[_⇒_]          : (m₀ : Mode) → (m₁ : Mode) → Term → Term

  `return[_⇒_]          : (m₀ : Mode) → (m₁ : Mode) → Term → Term
  `let-return[_⇒_]_`in_ : (m₀ : Mode) → (m₁ : Mode) → Term → Term → Term

  `λ⦂[_]_∘_             : (m : Mode) → (S : Type) → Term → Term
  _`$_                  : Term → Term → Term

  `#_                   : (x : ℕ) → Term

Useable = Bool
ContextEntry = Type × Mode × Useable
Context = List ContextEntry

module Variables where
  variable
    m m′ m″ m‴ m₀ m₁ m₂ m₃ : Mode
    d d′ d″ d‴ d₀ d₁ d₂ d₃ dS dS′ dS″ dS‴ dS₀ dS₁ dS₂ dS₃ dT dT′ dT″ dT‴ dT₀ dT₁ dT₂ dT₃ : Bool
    x x′ x″ x‴ x₀ x₁ x₂ x₃ y y′ y″ y‴ y₀ y₁ y₂ y₃ u u′ u″ u‴ u₀ u₁ u₂ u₃ v v′ v″ v‴ v₀ v₁ v₂ v₃ k k′ k″ k‴ k₀ k₁ k₂ k₃ : ℕ
    S S′ S″ S‴ S₀ S₁ S₂ S₃ T T′ T″ T‴ T₀ T₁ T₂ T₃ : Type
    L L′ L″ L‴ L₀ L₁ L₂ L₃ M M′ M″ M‴ M₀ M₁ M₂ M₃ N N′ N″ N‴ N₀ N₁ N₂ N₃ : Term
    e e′ e″ e‴ e₀ e₁ e₂ e₃ : ContextEntry
    Γ Γ′ Γ″ Γ‴ Γ₀ Γ₀′ Γ₀″ Γ₀‴ Γ₁ Γ₁′ Γ₁″ Γ₁‴ Γ₂ Γ₂′ Γ₂″ Γ₂‴ Γ₃ Γ₃′ Γ₃″ Γ₃‴ : Context
    Δ Δ′ Δ″ Δ‴ Δ₀ Δ₀′ Δ₀″ Δ₀‴ Δ₁ Δ₁′ Δ₁″ Δ₁‴ Δ₂ Δ₂′ Δ₂″ Δ₂‴ Δ₃ Δ₃′ Δ₃″ Δ₃‴ : Context

open Variables public
