------------------------------------------------------------
-- Static Rules for DP Modal Calculus
------------------------------------------------------------

{-# OPTIONS --safe #-}
module Calculus.LambdaBox.Typing where

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_)

open import Calculus.LambdaBox.Syntax

infix   4 _⦂_∈_
infix   4 _⍮_⊢_⦂_

data _⦂_∈_ : ℕ → Type → List Type → Set where
  here  : --------------
          0 ⦂ A ∈ A ∷ Φ

  there : x ⦂ A ∈ Φ →
          ------------------
          suc x ⦂ A ∈ B ∷ Φ

data _⍮_⊢_⦂_ : Context → Context → Term → Type → Set where
  `unit         : ---------------------
                  Ψ₁ ⍮ Ψ₀ ⊢ `unit ⦂ `⊤

  `box          : Ψ₁ ⍮ [] ⊢ E ⦂ A →
                  ------------------------
                  Ψ₁ ⍮ Ψ₀ ⊢ `box E ⦂ `□ A

  `let-box_`in_ : Ψ₁ ⍮ Ψ₀ ⊢ E ⦂ `□ B →
                  B ∷ Ψ₁ ⍮ Ψ₀ ⊢ F ⦂ A →
                  -------------------------------
                  Ψ₁ ⍮ Ψ₀ ⊢ `let-box E `in F ⦂ A

  `λ⦂-∙_        : Ψ₁ ⍮ A ∷ Ψ₀ ⊢ E ⦂ B →
                  -----------------------------
                  Ψ₁ ⍮ Ψ₀ ⊢ `λ⦂ A ∙ E ⦂ A `→ B

  _`$_          : Ψ₁ ⍮ Ψ₀ ⊢ E ⦂ B `→ A →
                  Ψ₁ ⍮ Ψ₀ ⊢ F ⦂ B →
                  ---------------------
                  Ψ₁ ⍮ Ψ₀ ⊢ E `$ F ⦂ A

  `#¹_          : u ⦂ A ∈ Ψ₁ →
                  --------------------
                  Ψ₁ ⍮ Ψ₀ ⊢ `#¹ u ⦂ A

  `#⁰_          : x ⦂ A ∈ Ψ₀ →
                  --------------------
                  Ψ₁ ⍮ Ψ₀ ⊢ `#⁰ x ⦂ A
