------------------------------------------------------------
-- An Instance of Mode Specification for Adjoint DILL
------------------------------------------------------------

{-# OPTIONS --safe #-}
module Calculus.AdjND.Embedding.DILL.ModeSpec where

open import Agda.Primitive
open import Data.Bool using (Bool; true; false)
open import Relation.Binary using (Rel; _⇒_; Transitive; Antisymmetric; IsPreorder; IsPartialOrder; IsDecPartialOrder)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

open import Calculus.AdjND.ModeSpec

data Modeᴸ : Set where
  uMode lMode : Modeᴸ

data _≤ₘᴸ_ : Rel Modeᴸ lzero where
  refl : ∀ {m} →
         --------
         m ≤ₘᴸ m

  l≤u  : ----------------
         lMode ≤ₘᴸ uMode

≤ₘᴸ-reflexive : _≡_ ⇒ _≤ₘᴸ_
≤ₘᴸ-reflexive refl = refl

≤ₘᴸ-trans : Transitive _≤ₘᴸ_
≤ₘᴸ-trans refl m′≤m″ = m′≤m″
≤ₘᴸ-trans l≤u  refl  = l≤u

isPreorderₘᴸ : IsPreorder _≡_ _≤ₘᴸ_
isPreorderₘᴸ = record
               { isEquivalence = ≡.isEquivalence
               ; reflexive = ≤ₘᴸ-reflexive
               ; trans = ≤ₘᴸ-trans
               }

≤ₘᴸ-antisym : Antisymmetric _≡_ _≤ₘᴸ_
≤ₘᴸ-antisym refl refl = refl

isPartialOrderₘᴸ : IsPartialOrder _≡_ _≤ₘᴸ_
isPartialOrderₘᴸ = record
                   { isPreorder = isPreorderₘᴸ
                   ; antisym = ≤ₘᴸ-antisym
                   }

_≟ₘᴸ_ : ∀ (m m′ : Modeᴸ) → Dec (m ≡ m′)
uMode ≟ₘᴸ uMode = yes refl
uMode ≟ₘᴸ lMode = no λ ()
lMode ≟ₘᴸ uMode = no λ ()
lMode ≟ₘᴸ lMode = yes refl

_≤?ₘᴸ_ : ∀ m m′ → Dec (m ≤ₘᴸ m′)
uMode ≤?ₘᴸ uMode = yes refl
uMode ≤?ₘᴸ lMode = no λ ()
lMode ≤?ₘᴸ uMode = yes l≤u
lMode ≤?ₘᴸ lMode = yes refl

stₘᴸ : Modeᴸ → ModeSpecSt → Bool
stₘᴸ uMode st = true
stₘᴸ lMode st = false

opₘᴸ : Modeᴸ → ModeSpecOp → Bool
opₘᴸ uMode ``⊤ = false
opₘᴸ uMode ``⊸ = false
opₘᴸ uMode ``↑ = true
opₘᴸ uMode ``↓ = false
opₘᴸ lMode ``⊤ = true
opₘᴸ lMode ``⊸ = true
opₘᴸ lMode ``↑ = false
opₘᴸ lMode ``↓ = true

ℳᴸ : ModeSpec _ _
ℳᴸ = record
     { Mode = Modeᴸ
     ; _≤ₘ_ = _≤ₘᴸ_
     ; isPreorderₘ = isPreorderₘᴸ
     ; _≟ₘ_ = _≟ₘᴸ_
     ; _≤?ₘ_ = _≤?ₘᴸ_
     ; stₘ = stₘᴸ
     ; opₘ = opₘᴸ
     ; isWellStructuredₘ = λ{ _ _ _ refl t → t }
     }
