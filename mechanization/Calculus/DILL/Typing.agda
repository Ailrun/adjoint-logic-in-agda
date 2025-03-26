------------------------------------------------------------
-- Static Rules for DILL
------------------------------------------------------------

{-# OPTIONS --safe #-}
module Calculus.DILL.Typing where

open import Data.Bool as Bool using (true; false)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Calculus.DILL.Syntax

infix   4 _⦂_∈¹_
infix   4 _⦂_∈⁰_
infix   4 _~_⊞_
infix   4 _~d_⊞_
infix   4 _⍮_⊢_⦂_
infixr  6 _t∷_
infixr  6 _f∷_

pattern _t∷_ P φ = (P , true) ∷ φ
pattern _f∷_ P φ = (P , false) ∷ φ

-- Predicate for a Context⁰ only with disabled entries
_is-all-dis : Context⁰ → Set
_is-all-dis = All (λ (_ , b) → b ≡ false)

data _⦂_∈¹_ : ℕ → Type → Context¹ → Set where
  here  : ----------------
          0 ⦂ P ∈¹ P ∷ ψ₁

  there : x ⦂ P ∈¹ ψ₁ →
          --------------------
          suc x ⦂ P ∈¹ Q ∷ ψ₁

data _⦂_∈⁰_ : ℕ → Type → Context⁰ → Set where
  here  : ψ₀ is-all-dis →
          ---------------------
          0 ⦂ P ∈⁰ P t∷ ψ₀

  there : x ⦂ P ∈⁰ ψ₀ →
          ---------------------
          suc x ⦂ P ∈⁰ Q f∷ ψ₀

data _~d_⊞_ : Useable → Useable → Useable → Set where
  to-left  : true ~d true ⊞ false
  to-right : true ~d false ⊞ true
  unusable : false ~d false ⊞ false

data _~_⊞_ : Context⁰ → Context⁰ → Context⁰ → Set where
  []  : [] ~ [] ⊞ []

  _∷_ : d ~d d₀ ⊞ d₁ →
        ψ₀ ~ ψ₀₀ ⊞ ψ₀₁ →
        -----------------------------------------------
        (P , d) ∷ ψ₀ ~ (P , d₀) ∷ ψ₀₀ ⊞ (P , d₁) ∷ ψ₀₁

data _⍮_⊢_⦂_ : Context¹ → Context⁰ → Term → Type → Set where
  `unit            : ψ₀ is-all-dis →
                     ---------------------
                     ψ₁ ⍮ ψ₀ ⊢ `unit ⦂ `⊤

  _⊢`bang_         : ψ₀ is-all-dis →
                     ψ₁ ⍮ ψ₀ ⊢ I ⦂ P →
                     -------------------------
                     ψ₁ ⍮ ψ₀ ⊢ `bang I ⦂ `! P

  _⊢`let-bang_`in_ : ψ₀ ~ ψ₀₀ ⊞ ψ₀₁ →
                     ψ₁ ⍮ ψ₀₀ ⊢ I ⦂ `! Q →
                     Q ∷ ψ₁ ⍮ ψ₀₁ ⊢ J ⦂ P →
                     --------------------------------
                     ψ₁ ⍮ ψ₀ ⊢ `let-bang I `in J ⦂ P

  `λ⦂-∘_           : ψ₁ ⍮ P t∷ ψ₀ ⊢ I ⦂ Q →
                     -----------------------------
                     ψ₁ ⍮ ψ₀ ⊢ `λ⦂ P ∘ I ⦂ P `⊸ Q

  _⊢_`$_           : ψ₀ ~ ψ₀₀ ⊞ ψ₀₁ →
                     ψ₁ ⍮ ψ₀₀ ⊢ I ⦂ Q `⊸ P →
                     ψ₁ ⍮ ψ₀₁ ⊢ J ⦂ Q →
                     -------------------------
                     ψ₁ ⍮ ψ₀ ⊢ I `$ J ⦂ P

  _⊢`#¹_           : ψ₀ is-all-dis →
                     u ⦂ P ∈¹ ψ₁ →
                     ---------------------
                     ψ₁ ⍮ ψ₀ ⊢ `#¹ u ⦂ P

  `#⁰_             : x ⦂ P ∈⁰ ψ₀ →
                     --------------------
                     ψ₁ ⍮ ψ₀ ⊢ `#⁰ x ⦂ P
