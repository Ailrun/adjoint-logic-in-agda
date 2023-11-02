------------------------------------------------------------
-- Properties of Operational Semantics for Elevator
------------------------------------------------------------

{-# OPTIONS --safe #-}
open import Calculus.Elevator.ModeSpec

module Calculus.Elevator.OpSem.Properties {ℓ₁ ℓ₂} (ℳ : ModeSpec ℓ₁ ℓ₂) where
open ModeSpec ℳ

open import Agda.Primitive
open import Data.Nat as ℕ using (ℕ; z≤n; s≤s)
import Data.Nat.Properties as ℕ
open import Data.Product using (Σ; _,_; ∃; ∃₂; _×_; -,_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Calculus.GeneralOpSem using (module ⟶*)
import Calculus.Elevator.Syntax as S
import Calculus.Elevator.OpSem as O
open S ℳ
open O ℳ

-- Properties of single step relations
--

WeakNorm⇒¬⟶ : WeakNorm L →
              ¬ (L ⟶ L′)
WeakNeut⇒¬⟶ : WeakNeut L →
              ¬ (L ⟶ L′)
DeferredTerm⇒¬⟶[≤] : DeferredTerm[ m ≤] L →
                     ¬ (L ⟶[ m ≤] L′)

WeakNorm⇒¬⟶ (`lift[ m₀ ⇒ m₁ ] WL)   (ξ-`lift[-⇒-] L⟶[≤]) = DeferredTerm⇒¬⟶[≤] WL L⟶[≤]
WeakNorm⇒¬⟶ (`return[ m₀ ⇒ m₁ ] VL) (ξ-`return[-⇒-] L⟶)  = WeakNorm⇒¬⟶ VL L⟶
WeakNorm⇒¬⟶ (`neut NL)              L⟶                   = WeakNeut⇒¬⟶ NL L⟶

WeakNeut⇒¬⟶ (`unlift[ m₀ ⇒ m₁ ] NL)           (ξ-`unlift[-⇒-] L⟶)        = WeakNeut⇒¬⟶ NL L⟶
WeakNeut⇒¬⟶ (`let-return[ m₀ ⇒ m₁ ] NL `in M) ξ-`let-return[-⇒-] L⟶ `in- = WeakNeut⇒¬⟶ NL L⟶
WeakNeut⇒¬⟶ (NL `$ VM)                        ξ- L⟶ `$?                  = WeakNeut⇒¬⟶ NL L⟶
WeakNeut⇒¬⟶ (NL `$ VM)                        (ξ-! VL `$ M⟶)             = WeakNorm⇒¬⟶ VM M⟶

DeferredTerm⇒¬⟶[≤] (`lift[ m₀ ⇒ m₁ ] WL)                 (ξ-`lift[-⇒-] L⟶[≤])                    = DeferredTerm⇒¬⟶[≤] WL L⟶[≤]
DeferredTerm⇒¬⟶[≤] (`unlift[≰ m≰m₀ ⇒ m₁ ] WL)            (ξ-`unlift[≰ _ ⇒-] L⟶[≤])               = DeferredTerm⇒¬⟶[≤] WL L⟶[≤]
DeferredTerm⇒¬⟶[≤] (`unlift[≰ m≰m₀ ⇒ m₁ ] WL)            (ξ-`unlift[≤ m≤m₀ ⇒-] L⟶)               = m≰m₀ m≤m₀
DeferredTerm⇒¬⟶[≤] (`unlift[≰ m≰m₀ ⇒ m₁ ] WL)            (β-`↑ m≤m₀ _)                           = m≰m₀ m≤m₀
DeferredTerm⇒¬⟶[≤] (`unlift[≤ m≤m₀ ⇒ m₁ ] VL)            (ξ-`unlift[≰ m≰m₀ ⇒-] L⟶[≤])            = m≰m₀ m≤m₀
DeferredTerm⇒¬⟶[≤] (`unlift[≤ m≤m₀ ⇒ m₁ ] VL)            (ξ-`unlift[≤ _ ⇒-] L⟶)                  = WeakNorm⇒¬⟶ VL L⟶
DeferredTerm⇒¬⟶[≤] (`return[≰ m≰m₀ ⇒ m₁ ] WL)            (ξ-`return[≰ _ ⇒-] L⟶[≤])               = DeferredTerm⇒¬⟶[≤] WL L⟶[≤]
DeferredTerm⇒¬⟶[≤] (`return[≰ m≰m₀ ⇒ m₁ ] WL)            (ξ-`return[≤ m≤m₀ ⇒-] L⟶)               = m≰m₀ m≤m₀
DeferredTerm⇒¬⟶[≤] (`return[≤ m≤m₀ ⇒ m₁ ] VL)            (ξ-`return[≰ m≰m₀ ⇒-] L⟶[≤])            = m≰m₀ m≤m₀
DeferredTerm⇒¬⟶[≤] (`return[≤ m≤m₀ ⇒ m₁ ] VL)            (ξ-`return[≤ _ ⇒-] L⟶)                  = WeakNorm⇒¬⟶ VL L⟶
DeferredTerm⇒¬⟶[≤] (`let-return[≰ m≰m₀ ⇒ m₁ ] WL `in WM) ξ-`let-return[≰ _ ⇒-] L⟶[≤] `in?        = DeferredTerm⇒¬⟶[≤] WL L⟶[≤]
DeferredTerm⇒¬⟶[≤] (`let-return[≰ m≰m₀ ⇒ m₁ ] WL `in WM) ξ-`let-return[≤ m≤m₀ ⇒-] L⟶ `in?        = m≰m₀ m≤m₀
DeferredTerm⇒¬⟶[≤] (`let-return[≤ m≤m₀ ⇒ m₁ ] VL `in WM) ξ-`let-return[≰ m≰m₀ ⇒-] L⟶[≤] `in?     = m≰m₀ m≤m₀
DeferredTerm⇒¬⟶[≤] (`let-return[≤ m≤m₀ ⇒ m₁ ] VL `in WM) ξ-`let-return[≤ _ ⇒-] L⟶ `in?           = WeakNorm⇒¬⟶ VL L⟶
DeferredTerm⇒¬⟶[≤] (`let-return[≰ m≰m₀ ⇒ m₁ ] WL `in WM) (ξ-`let-return[≰ _ ⇒-]! _ `in M⟶[≤])    = DeferredTerm⇒¬⟶[≤] WM M⟶[≤]
DeferredTerm⇒¬⟶[≤] (`let-return[≰ m≰m₀ ⇒ m₁ ] WL `in WM) (ξ-`let-return[≤ m≤m₀ ⇒-]! _ `in M⟶[≤]) = m≰m₀ m≤m₀
DeferredTerm⇒¬⟶[≤] (`let-return[≤ m≤m₀ ⇒ m₁ ] VL `in WM) (ξ-`let-return[≰ m≰m₀ ⇒-]! _ `in M⟶[≤]) = m≰m₀ m≤m₀
DeferredTerm⇒¬⟶[≤] (`let-return[≤ m≤m₀ ⇒ m₁ ] VL `in WM) (ξ-`let-return[≤ _ ⇒-]! _ `in M⟶[≤])    = DeferredTerm⇒¬⟶[≤] WM M⟶[≤]
DeferredTerm⇒¬⟶[≤] (`λ⦂[ m₀ ] S ∘ WL)                    (ξ-`λ⦂[-]-∘ L⟶[≤])                      = DeferredTerm⇒¬⟶[≤] WL L⟶[≤]
DeferredTerm⇒¬⟶[≤] (WL `$ WM)                            ξ- L⟶[≤] `$?                            = DeferredTerm⇒¬⟶[≤] WL L⟶[≤]
DeferredTerm⇒¬⟶[≤] (WL `$ WM)                            (ξ-! _ `$ M⟶[≤])                        = DeferredTerm⇒¬⟶[≤] WM M⟶[≤]

⟶-det : L ⟶ L₀ →
        L ⟶ L₁ →
        L₀ ≡ L₁
⟶[≤]-det : L ⟶[ m ≤] L₀ →
           L ⟶[ m ≤] L₁ →
           L₀ ≡ L₁

⟶-det (ξ-`lift[-⇒-] L⟶[≤]₀) (ξ-`lift[-⇒-] L⟶[≤]₁) = cong `lift[ _ ⇒ _ ] (⟶[≤]-det L⟶[≤]₀ L⟶[≤]₁)
⟶-det (ξ-`unlift[-⇒-] L⟶₀) (ξ-`unlift[-⇒-] L⟶₁) = cong `unlift[ _ ⇒ _ ] (⟶-det L⟶₀ L⟶₁)
⟶-det (ξ-`unlift[-⇒-] (ξ-`lift[-⇒-] L⟶[≤]₀)) (β-`↑ WL₁) with () ← DeferredTerm⇒¬⟶[≤] WL₁ L⟶[≤]₀
⟶-det (β-`↑ WL₀) (ξ-`unlift[-⇒-] (ξ-`lift[-⇒-] L⟶[≤]₁)) with () ← DeferredTerm⇒¬⟶[≤] WL₀ L⟶[≤]₁
⟶-det (β-`↑ WL₀) (β-`↑ WL₁) = refl
⟶-det (ξ-`return[-⇒-] L⟶₀) (ξ-`return[-⇒-] L⟶₁) = cong `return[ _ ⇒ _ ] (⟶-det L⟶₀ L⟶₁)
⟶-det ξ-`let-return[-⇒-] L⟶₀ `in- ξ-`let-return[-⇒-] L⟶₁ `in- = cong (`let-return[ _ ⇒ _ ]_`in _) (⟶-det L⟶₀ L⟶₁)
⟶-det ξ-`let-return[-⇒-] (ξ-`return[-⇒-] L⟶₀) `in- (β-`↓ VL₁) with () ← WeakNorm⇒¬⟶ VL₁ L⟶₀
⟶-det (β-`↓ VL₀) ξ-`let-return[-⇒-] (ξ-`return[-⇒-] L⟶₁) `in- with () ← WeakNorm⇒¬⟶ VL₀ L⟶₁
⟶-det (β-`↓ VL₀) (β-`↓ VL₁) = refl
⟶-det ξ- L⟶₀ `$? ξ- L⟶₁ `$? = cong (_`$ _) (⟶-det L⟶₀ L⟶₁)
⟶-det ξ- L⟶₀ `$? (ξ-! VL₁ `$ M⟶₁) with () ← WeakNorm⇒¬⟶ VL₁ L⟶₀
⟶-det (ξ-! VL₀ `$ M⟶₀) ξ- L⟶₁ `$? with () ← WeakNorm⇒¬⟶ VL₀ L⟶₁
⟶-det (ξ-! VL₀ `$ M⟶₀) (ξ-! VL₁ `$ M⟶₁) = cong (_ `$_) (⟶-det M⟶₀ M⟶₁)
⟶-det (ξ-! VL₀ `$ M⟶₀) (β-`⊸ VM₁) with () ← WeakNorm⇒¬⟶ VM₁ M⟶₀
⟶-det (β-`⊸ VM₀) (ξ-! VL₁ `$ M⟶₁) with () ← WeakNorm⇒¬⟶ VM₀ M⟶₁
⟶-det (β-`⊸ VM₀) (β-`⊸ VM₁) = refl

⟶[≤]-det (O.ξ-`lift[-⇒-] L⟶[≤]₀)                        (O.ξ-`lift[-⇒-] L⟶[≤]₁)                      = cong `lift[ _ ⇒ _ ] (⟶[≤]-det L⟶[≤]₀ L⟶[≤]₁)
⟶[≤]-det (O.ξ-`unlift[≰ m≰m₀ ⇒-] L⟶[≤]₀)                (O.ξ-`unlift[≰ _ ⇒-] L⟶[≤]₁)                 = cong `unlift[ _ ⇒ _ ] (⟶[≤]-det L⟶[≤]₀ L⟶[≤]₁)
⟶[≤]-det (O.ξ-`unlift[≰ m≰m₀ ⇒-] L⟶[≤]₀)                (O.ξ-`unlift[≤ m≤m₀ ⇒-] L⟶₁)                 with () ← m≰m₀ m≤m₀
⟶[≤]-det (O.ξ-`unlift[≰ m≰m₀ ⇒-] L⟶[≤]₀)                (O.β-`↑ m≤m₀ WL₁)                            with () ← m≰m₀ m≤m₀
⟶[≤]-det (O.ξ-`unlift[≤ m≤m₀ ⇒-] L⟶₀)                   (O.ξ-`unlift[≰ m≰m₀ ⇒-] L⟶[≤]₁)              with () ← m≰m₀ m≤m₀
⟶[≤]-det (O.ξ-`unlift[≤ m≤m₀ ⇒-] L⟶₀)                   (O.ξ-`unlift[≤ _ ⇒-] L⟶₁)                    = cong `unlift[ _ ⇒ _ ] (⟶-det L⟶₀ L⟶₁)
⟶[≤]-det (O.ξ-`unlift[≤ m≤m₀ ⇒-] (ξ-`lift[-⇒-] L⟶[≤]₀)) (O.β-`↑ _ WL₁)                               with () ← DeferredTerm⇒¬⟶[≤] WL₁ L⟶[≤]₀
⟶[≤]-det (O.β-`↑ m≤m₀ WL₀)                              (O.ξ-`unlift[≰ m≰m₀ ⇒-] L⟶[≤]₁)              with () ← m≰m₀ m≤m₀
⟶[≤]-det (O.β-`↑ m≤m₀ WL₀)                              (O.ξ-`unlift[≤ _ ⇒-] (ξ-`lift[-⇒-] L⟶[≤]₁))  with () ← DeferredTerm⇒¬⟶[≤] WL₀ L⟶[≤]₁
⟶[≤]-det (O.β-`↑ m≤m₀ WL₀)                              (O.β-`↑ _ WL₁)                               = refl
⟶[≤]-det (O.ξ-`return[≰ m≰m₀ ⇒-] L⟶[≤]₀)                (O.ξ-`return[≰ _ ⇒-] L⟶[≤]₁)                 = cong `return[ _ ⇒ _ ] (⟶[≤]-det L⟶[≤]₀ L⟶[≤]₁)
⟶[≤]-det (O.ξ-`return[≰ m≰m₀ ⇒-] L⟶[≤]₀)                (O.ξ-`return[≤ m≤m₀ ⇒-] L⟶₁)                 with () ← m≰m₀ m≤m₀
⟶[≤]-det (O.ξ-`return[≤ m≤m₀ ⇒-] L⟶₀)                   (O.ξ-`return[≰ m≰m₀ ⇒-] L⟶[≤]₁)              with () ← m≰m₀ m≤m₀
⟶[≤]-det (O.ξ-`return[≤ m≤m₀ ⇒-] L⟶₀)                   (O.ξ-`return[≤ _ ⇒-] L⟶₁)                    = cong `return[ _ ⇒ _ ] (⟶-det L⟶₀ L⟶₁)
⟶[≤]-det O.ξ-`let-return[≰ m≰m₀ ⇒-] L⟶[≤]₀ `in?         O.ξ-`let-return[≰ _ ⇒-] L⟶[≤]₁ `in?          = cong (`let-return[ _ ⇒ _ ]_`in _) (⟶[≤]-det L⟶[≤]₀ L⟶[≤]₁)
⟶[≤]-det O.ξ-`let-return[≰ m≰m₀ ⇒-] L⟶[≤]₀ `in?         O.ξ-`let-return[≤ m≤m₀ ⇒-] L⟶[≤]₁ `in?       with () ← m≰m₀ m≤m₀
⟶[≤]-det O.ξ-`let-return[≰ m≰m₀ ⇒-] L⟶[≤]₀ `in?         (O.ξ-`let-return[≰ _ ⇒-]! WL₁ `in M⟶[≤]₁)    with () ← DeferredTerm⇒¬⟶[≤] WL₁ L⟶[≤]₀
⟶[≤]-det O.ξ-`let-return[≰ m≰m₀ ⇒-] L⟶[≤]₀ `in?         (O.ξ-`let-return[≤ m≤m₀ ⇒-]! VL₁ `in M⟶[≤]₁) with () ← m≰m₀ m≤m₀
⟶[≤]-det O.ξ-`let-return[≤ m≤m₀ ⇒-] L⟶₀ `in?            O.ξ-`let-return[≰ m≰m₀ ⇒-] L⟶[≤]₁ `in?       with () ← m≰m₀ m≤m₀
⟶[≤]-det O.ξ-`let-return[≤ m≤m₀ ⇒-] L⟶₀ `in?            O.ξ-`let-return[≤ _ ⇒-] L⟶₁ `in?             = cong (`let-return[ _ ⇒ _ ]_`in _) (⟶-det L⟶₀ L⟶₁)
⟶[≤]-det O.ξ-`let-return[≤ m≤m₀ ⇒-] L⟶₀ `in?            (O.ξ-`let-return[≰ m≰m₀ ⇒-]! WL₁ `in M⟶[≤]₁) with () ← m≰m₀ m≤m₀
⟶[≤]-det O.ξ-`let-return[≤ m≤m₀ ⇒-] L⟶₀ `in?            (O.ξ-`let-return[≤ _ ⇒-]! VL₁ `in M⟶[≤]₁)    with () ← WeakNorm⇒¬⟶ VL₁ L⟶₀
⟶[≤]-det (O.ξ-`let-return[≰ m≰m₀ ⇒-]! WL₀ `in M⟶[≤]₀)   O.ξ-`let-return[≰ _ ⇒-] L⟶[≤]₁ `in?          with () ← DeferredTerm⇒¬⟶[≤] WL₀ L⟶[≤]₁
⟶[≤]-det (O.ξ-`let-return[≰ m≰m₀ ⇒-]! WL₀ `in M⟶[≤]₀)   O.ξ-`let-return[≤ m≤m₀ ⇒-] L⟶₁ `in?          with () ← m≰m₀ m≤m₀
⟶[≤]-det (O.ξ-`let-return[≤ m≤m₀ ⇒-]! VL₀ `in M⟶[≤]₀)   O.ξ-`let-return[≰ m≰m₀ ⇒-] L⟶[≤]₁ `in?       with () ← m≰m₀ m≤m₀
⟶[≤]-det (O.ξ-`let-return[≤ m≰m₀ ⇒-]! VL₀ `in M⟶[≤]₀)   O.ξ-`let-return[≤ _ ⇒-] L⟶₁ `in?             with () ← WeakNorm⇒¬⟶ VL₀ L⟶₁
⟶[≤]-det (O.ξ-`let-return[≰ m≰m₀ ⇒-]! WL₀ `in M⟶[≤]₀)   (O.ξ-`let-return[≰ _ ⇒-]! WL₁ `in M⟶[≤]₁)    = cong `let-return[ _ ⇒ _ ] _ `in_ (⟶[≤]-det M⟶[≤]₀ M⟶[≤]₁)
⟶[≤]-det (O.ξ-`let-return[≰ m≰m₀ ⇒-]! WL₀ `in M⟶[≤]₀)   (O.ξ-`let-return[≤ m≤m₀ ⇒-]! VL₁ `in M⟶[≤]₁) with () ← m≰m₀ m≤m₀
⟶[≤]-det (O.ξ-`let-return[≤ m≤m₀ ⇒-]! VL₀ `in M⟶[≤]₀)   (O.ξ-`let-return[≰ m≰m₀ ⇒-]! WL₁ `in M⟶[≤]₁) with () ← m≰m₀ m≤m₀
⟶[≤]-det (O.ξ-`let-return[≤ m≤m₀ ⇒-]! VL₀ `in M⟶[≤]₀)   (O.ξ-`let-return[≤ _ ⇒-]! VL₁ `in M⟶[≤]₁)    = cong `let-return[ _ ⇒ _ ] _ `in_ (⟶[≤]-det M⟶[≤]₀ M⟶[≤]₁)
⟶[≤]-det O.ξ- L⟶[≤]₀ `$?                                O.ξ- L⟶[≤]₁ `$?                              = cong (_`$ _) (⟶[≤]-det L⟶[≤]₀ L⟶[≤]₁)
⟶[≤]-det O.ξ- L⟶[≤]₀ `$?                                (O.ξ-! WL₁ `$ M⟶[≤]₁)                        with () ← DeferredTerm⇒¬⟶[≤] WL₁ L⟶[≤]₀
⟶[≤]-det (O.ξ-! WL₀ `$ M⟶[≤]₀)                          O.ξ- L⟶[≤]₁ `$?                              with () ← DeferredTerm⇒¬⟶[≤] WL₀ L⟶[≤]₁
⟶[≤]-det (O.ξ-! WL₀ `$ M⟶[≤]₀)                          (O.ξ-! WL₁ `$ M⟶[≤]₁)                        = cong (_ `$_) (⟶[≤]-det M⟶[≤]₀ M⟶[≤]₁)
⟶[≤]-det (O.ξ-`λ⦂[-]-∘ L⟶[≤]₀)                          (O.ξ-`λ⦂[-]-∘ L⟶[≤]₁)                        = cong `λ⦂[ _ ] _ ∘_ (⟶[≤]-det L⟶[≤]₀ L⟶[≤]₁)

-- Properties of multi-step relations
--

⟶*-factor : (L⟶*₀ : L ⟶* L₀) →
            (L⟶*₁ : L ⟶* L₁) →
            ⟶*length L⟶*₀ ℕ.≤ ⟶*length L⟶*₁ →
            Σ (L₀ ⟶* L₁) (λ L₀⟶* → ⟶*length L₀⟶* ℕ.≤ ⟶*length L⟶*₁)
⟶*-factor = ⟶*.⟶*-factor _⟶_ ⟶-det

⟶[≤]*-factor : (L⟶[≤]*₀ : L ⟶[ m ≤]* L₀) →
               (L⟶[≤]*₁ : L ⟶[ m ≤]* L₁) →
               ⟶[≤]*length L⟶[≤]*₀ ℕ.≤ ⟶[≤]*length L⟶[≤]*₁ →
               Σ (L₀ ⟶[ m ≤]* L₁) (λ L₀⟶[≤]* → ⟶[≤]*length L₀⟶[≤]* ℕ.≤ ⟶[≤]*length L⟶[≤]*₁)
⟶[≤]*-factor {m = m} = ⟶*.⟶*-factor _⟶[ m ≤]_ ⟶[≤]-det

⟶*length≤⟶*length-halt : (L⟶*₀ : L ⟶* L₀) →
                         (L⟶*₁ : L ⟶* L₁) →
                         WeakNorm L₁ →
                         ⟶*length L⟶*₀ ℕ.≤ ⟶*length L⟶*₁
⟶*length≤⟶*length-halt ε            L⟶*₁          VL₁ = z≤n
⟶*length≤⟶*length-halt (L⟶ ◅ L′⟶*₀) ε             VL  with () ← WeakNorm⇒¬⟶ VL L⟶
⟶*length≤⟶*length-halt (L⟶ ◅ L′⟶*₀) (L⟶′ ◅ L″⟶*₁) VL₁
  rewrite ⟶-det L⟶ L⟶′                                = s≤s (⟶*length≤⟶*length-halt L′⟶*₀ L″⟶*₁ VL₁)

⟶[≤]*length≤⟶[≤]*length-halt : (L⟶[≤]*₀ : L ⟶[ m ≤]* L₀) →
                               (L⟶[≤]*₁ : L ⟶[ m ≤]* L₁) →
                               DeferredTerm[ m ≤] L₁ →
                               ⟶[≤]*length L⟶[≤]*₀ ℕ.≤ ⟶[≤]*length L⟶[≤]*₁
⟶[≤]*length≤⟶[≤]*length-halt ε                  L⟶[≤]*₁             WL₁ = z≤n
⟶[≤]*length≤⟶[≤]*length-halt (L⟶[≤] ◅ L′⟶[≤]*₀) ε                   WL  with () ← DeferredTerm⇒¬⟶[≤] WL L⟶[≤]
⟶[≤]*length≤⟶[≤]*length-halt (L⟶[≤] ◅ L′⟶[≤]*₀) (L⟶[≤]′ ◅ L″⟶[≤]*₁) WL₁
  rewrite ⟶[≤]-det L⟶[≤] L⟶[≤]′                                         = s≤s (⟶[≤]*length≤⟶[≤]*length-halt L′⟶[≤]*₀ L″⟶[≤]*₁ WL₁)

halt-`lift-inversion-helper : `lift[ m₀ ⇒ m ] L ⟶* L′ →
                              WeakNorm L′ →
                              --------------------------
                              halt[ m ≤] L
halt-`lift-inversion-helper ε                           (`lift[ _ ⇒ _ ] WL) = -, ε , WL
halt-`lift-inversion-helper (ξ-`lift[-⇒-] L⟶[≤] ◅ lL′⟶*) VL″
  with _ , L′⟶[≤]* , WL″ ← halt-`lift-inversion-helper lL′⟶* VL″            = -, L⟶[≤] ◅ L′⟶[≤]* , WL″

halt-`lift-inversion : halt (`lift[ m₀ ⇒ m ] L) →
                       ---------------------------
                       halt[ m ≤] L
halt-`lift-inversion (_  , lL⟶* , VL′) = halt-`lift-inversion-helper lL⟶* VL′

halt-`unlift-inversion-helper : `unlift[ m₀ ⇒ m ] L ⟶* L′ →
                                WeakNorm L′ →
                                ----------------------------
                                halt L
halt-`unlift-inversion-helper ε                           (`neut (`unlift[ _ ⇒ _ ] NL))   = -, ε , `neut NL
halt-`unlift-inversion-helper (ξ-`unlift[-⇒-] L⟶ ◅ uL′⟶*) VL″
  with _ , L′⟶* , VL″ ← halt-`unlift-inversion-helper uL′⟶* VL″                           = -, L⟶ ◅ L′⟶* , VL″
halt-`unlift-inversion-helper (β-`↑ WL ◅ L′⟶*)            VL″                             = -, ε , `lift[ _ ⇒ _ ] WL

halt-`unlift-inversion : halt (`unlift[ m₀ ⇒ m ] L) →
                         -----------------------------
                         halt L
halt-`unlift-inversion (_  , uL⟶* , VL′) = halt-`unlift-inversion-helper uL⟶* VL′

halt-`return-inversion-helper : `return[ m₀ ⇒ m ] L ⟶* L′ →
                                WeakNorm L′ →
                                ----------------------------
                                halt L
halt-`return-inversion-helper ε                           (`return[ _ ⇒ _ ] VL)   = -, ε , VL
halt-`return-inversion-helper (ξ-`return[-⇒-] L⟶ ◅ rL′⟶*) VL″
  with _ , L′⟶* , VL″ ← halt-`return-inversion-helper rL′⟶* VL″                   = -, L⟶ ◅ L′⟶* , VL″

halt-`return-inversion : halt (`return[ m₀ ⇒ m ] L) →
                         -----------------------------
                         halt L
halt-`return-inversion (_  , rL⟶* , VL′) = halt-`return-inversion-helper rL⟶* VL′

halt-`let-return-`in-inversion-helper : `let-return[ m₀ ⇒ m ] L `in M ⟶* L′ →
                                        WeakNorm L′ →
                                        --------------------------------------
                                        halt L
halt-`let-return-`in-inversion-helper ε                                      (`neut (`let-return[ _ ⇒ _ ] NL `in M)) = -, ε , `neut NL
halt-`let-return-`in-inversion-helper (ξ-`let-return[-⇒-] L⟶ `in- ◅ lrL′M⟶*) VLM″
  with _ , L′⟶* , VL″ ← halt-`let-return-`in-inversion-helper lrL′M⟶* VLM″                                           = -, L⟶ ◅ L′⟶* , VL″
halt-`let-return-`in-inversion-helper (β-`↓ VL ⟶*.◅ lrL′M⟶*)               VLM″                                    = -, ε , `return[ _ ⇒ _ ] VL

halt-`let-return-`in-inversion : halt (`let-return[ m₀ ⇒ m ] L `in M) →
                                 ---------------------------------------
                                 halt L
halt-`let-return-`in-inversion (_  , lrLM⟶* , VL′) = halt-`let-return-`in-inversion-helper lrLM⟶* VL′

halt-`$-inversion-helper : L `$ M ⟶* L′ →
                           WeakNorm L′ →
                           ----------------
                           halt L × halt M
halt-`$-inversion-helper ε                        (`neut (NL `$ VM)) = (-, ε , `neut NL) , (-, ε , VM)
halt-`$-inversion-helper (ξ- L⟶ `$? ◅ L′$M⟶*)    VLM″
  with (_ , L′⟶* , VL″) , hM ← halt-`$-inversion-helper L′$M⟶* VLM″  = (-, L⟶ ◅ L′⟶* , VL″) , hM
halt-`$-inversion-helper (ξ-! VL `$ M⟶ ◅ L′$M⟶*) VLM″
  with hL , (_ , M′⟶* , VM″) ← halt-`$-inversion-helper L′$M⟶* VLM″  = hL , (-, M⟶ ◅ M′⟶* , VM″)
halt-`$-inversion-helper (β-`⊸ VM ⟶*.◅ L′$M⟶*) VLM″                = (-, ε , `λ⦂[ _ ] _ ∘ _) , (-, ε , VM)

halt-`$-inversion : halt (L `$ M) →
                    ----------------
                    halt L × halt M
halt-`$-inversion (_  , L$M⟶* , VL′) = halt-`$-inversion-helper L$M⟶* VL′

halt[≤]-`lift-inversion-helper : `lift[ m₀ ⇒ m ] L ⟶[ m′ ≤]* L′ →
                                 DeferredTerm[ m′ ≤] L′ →
                                 ---------------------------------
                                 halt[ m′ ≤] L
halt[≤]-`lift-inversion-helper ε                               (`lift[ _ ⇒ _ ] WL) = -, ε , WL
halt[≤]-`lift-inversion-helper (ξ-`lift[-⇒-] L⟶[≤] ◅ lL′⟶[≤]*) WL″
  with _ , L′⟶[≤]* , WL″ ← halt[≤]-`lift-inversion-helper lL′⟶[≤]* WL″             = -, L⟶[≤] ◅ L′⟶[≤]* , WL″

halt[≤]-`lift-inversion : halt[ m′ ≤] (`lift[ m₀ ⇒ m ] L) →
                          ----------------------------------
                          halt[ m′ ≤] L
halt[≤]-`lift-inversion (_  , lL⟶[≤]* , VL′) = halt[≤]-`lift-inversion-helper lL⟶[≤]* VL′

halt[≤]-`unlift-inversion-≤-helper : m′ ≤ₘ m₀ →
                                     `unlift[ m₀ ⇒ m ] L ⟶[ m′ ≤]* L′ →
                                     DeferredTerm[ m′ ≤] L′ →
                                     -----------------------------------
                                     halt L
halt[≤]-`unlift-inversion-≤-helper m′≤m₀ ε                                        (`unlift[≰ m′≰m₀ ⇒ _ ] WL) with () ← m′≰m₀ m′≤m₀
halt[≤]-`unlift-inversion-≤-helper m′≤m₀ ε                                        (`unlift[≤ _ ⇒ _ ] VL)     = -, ε , VL
halt[≤]-`unlift-inversion-≤-helper m′≤m₀ (ξ-`unlift[≰ m′≰m₀ ⇒-] L⟶[≤] ◅ uL′⟶[≤]*) WL″                        with () ← m′≰m₀ m′≤m₀
halt[≤]-`unlift-inversion-≤-helper m′≤m₀ (ξ-`unlift[≤ _ ⇒-] L⟶ ◅ uL′⟶[≤]*)        WL″
  with _ , L′⟶* , VL″ ← halt[≤]-`unlift-inversion-≤-helper m′≤m₀ uL′⟶[≤]* WL″                                = -, L⟶ ◅ L′⟶* , VL″
halt[≤]-`unlift-inversion-≤-helper m′≤m₀ (β-`↑ _ WL ◅ uL′⟶[≤]*)                   WL″                        = -, ε , `lift[ _ ⇒ _ ] WL

halt[≤]-`unlift-inversion-≤ : m′ ≤ₘ m₀ →
                              halt[ m′ ≤] (`unlift[ m₀ ⇒ m ] L) →
                              ------------------------------------
                              halt L
halt[≤]-`unlift-inversion-≤ m′≤m₀ (_  , uL⟶[≤]* , WL′) = halt[≤]-`unlift-inversion-≤-helper m′≤m₀ uL⟶[≤]* WL′

halt[≤]-`unlift-inversion-≰-helper : ¬ (m′ ≤ₘ m₀) →
                                     `unlift[ m₀ ⇒ m ] L ⟶[ m′ ≤]* L′ →
                                     DeferredTerm[ m′ ≤] L′ →
                                     -----------------------------------
                                     halt[ m′ ≤] L
halt[≤]-`unlift-inversion-≰-helper m′≰m₀ ε                                     (`unlift[≰ _ ⇒ _ ] WL)     = -, ε , WL
halt[≤]-`unlift-inversion-≰-helper m′≰m₀ ε                                     (`unlift[≤ m′≤m₀ ⇒ _ ] VL) with () ← m′≰m₀ m′≤m₀
halt[≤]-`unlift-inversion-≰-helper m′≰m₀ (ξ-`unlift[≰ _ ⇒-] L⟶[≤] ◅ uL′⟶[≤]*)  WL″
   with _ , L′⟶[≤]* , WL″ ← halt[≤]-`unlift-inversion-≰-helper m′≰m₀ uL′⟶[≤]* WL″                         = -, L⟶[≤] ◅ L′⟶[≤]* , WL″
halt[≤]-`unlift-inversion-≰-helper m′≰m₀ (ξ-`unlift[≤ m′≤m₀ ⇒-] L⟶ ◅ uL′⟶[≤]*) WL″                        with () ← m′≰m₀ m′≤m₀
halt[≤]-`unlift-inversion-≰-helper m′≰m₀ (β-`↑ m′≤m₀ WL ◅ uL′⟶[≤]*)            WL″                        with () ← m′≰m₀ m′≤m₀

halt[≤]-`unlift-inversion-≰ : ¬ (m′ ≤ₘ m₀) →
                              halt[ m′ ≤] (`unlift[ m₀ ⇒ m ] L) →
                              ------------------------------------
                              halt[ m′ ≤] L
halt[≤]-`unlift-inversion-≰ m′≰m₀ (_  , uL⟶[≤]* , WL′) = halt[≤]-`unlift-inversion-≰-helper m′≰m₀ uL⟶[≤]* WL′

halt[≤]-`return-inversion-≤-helper : m′ ≤ₘ m₀ →
                                     `return[ m₀ ⇒ m ] L ⟶[ m′ ≤]* L′ →
                                     DeferredTerm[ m′ ≤] L′ →
                                     -----------------------------------
                                     halt L
halt[≤]-`return-inversion-≤-helper m′≤m₀ ε                                        (`return[≰ m′≰m₀ ⇒ _ ] WL) with () ← m′≰m₀ m′≤m₀
halt[≤]-`return-inversion-≤-helper m′≤m₀ ε                                        (`return[≤ _ ⇒ _ ] VL)     = -, ε , VL
halt[≤]-`return-inversion-≤-helper m′≤m₀ (ξ-`return[≰ m′≰m₀ ⇒-] L⟶[≤] ◅ rL′⟶[≤]*) WL″                        with () ← m′≰m₀ m′≤m₀
halt[≤]-`return-inversion-≤-helper m′≤m₀ (ξ-`return[≤ _ ⇒-] L⟶ ◅ rL′⟶[≤]*)        WL″
  with _ , L′⟶* , VL″ ← halt[≤]-`return-inversion-≤-helper m′≤m₀ rL′⟶[≤]* WL″                                = -, L⟶ ◅ L′⟶* , VL″

halt[≤]-`return-inversion-≤ : m′ ≤ₘ m₀ →
                              halt[ m′ ≤] (`return[ m₀ ⇒ m ] L) →
                              ------------------------------------
                              halt L
halt[≤]-`return-inversion-≤ m′≤m₀ (_  , rL⟶[≤]* , WL′) = halt[≤]-`return-inversion-≤-helper m′≤m₀ rL⟶[≤]* WL′

halt[≤]-`return-inversion-≰-helper : ¬ (m′ ≤ₘ m₀) →
                                     `return[ m₀ ⇒ m ] L ⟶[ m′ ≤]* L′ →
                                     DeferredTerm[ m′ ≤] L′ →
                                     -----------------------------------
                                     halt[ m′ ≤] L
halt[≤]-`return-inversion-≰-helper m′≰m₀ ε                                     (`return[≰ _ ⇒ _ ] WL)     = -, ε , WL
halt[≤]-`return-inversion-≰-helper m′≰m₀ ε                                     (`return[≤ m′≤m₀ ⇒ _ ] VL) with () ← m′≰m₀ m′≤m₀
halt[≤]-`return-inversion-≰-helper m′≰m₀ (ξ-`return[≰ _ ⇒-] L⟶[≤] ◅ rL′⟶[≤]*)  WL″
   with _ , L′⟶[≤]* , WL″ ← halt[≤]-`return-inversion-≰-helper m′≰m₀ rL′⟶[≤]* WL″                         = -, L⟶[≤] ◅ L′⟶[≤]* , WL″
halt[≤]-`return-inversion-≰-helper m′≰m₀ (ξ-`return[≤ m′≤m₀ ⇒-] L⟶ ◅ rL′⟶[≤]*) WL″                        with () ← m′≰m₀ m′≤m₀

halt[≤]-`return-inversion-≰ : ¬ (m′ ≤ₘ m₀) →
                              halt[ m′ ≤] (`return[ m₀ ⇒ m ] L) →
                              ------------------------------------
                              halt[ m′ ≤] L
halt[≤]-`return-inversion-≰ m′≰m₀ (_  , rL⟶[≤]* , WL′) = halt[≤]-`return-inversion-≰-helper m′≰m₀ rL⟶[≤]* WL′

halt[≤]-`let-return[≤]-`in-inversion-helper : m′ ≤ₘ m₀ →
                                              `let-return[ m₀ ⇒ m ] L `in M ⟶[ m′ ≤]* L′ →
                                              DeferredTerm[ m′ ≤] L′ →
                                              ---------------------------------------------
                                              halt L × halt[ m′ ≤] M
halt[≤]-`let-return[≤]-`in-inversion-helper m′≤m₀ ε                                                      (`let-return[≰ m′≰m₀ ⇒ _ ] WL `in WM) with () ← m′≰m₀ m′≤m₀
halt[≤]-`let-return[≤]-`in-inversion-helper m′≤m₀ ε                                                      (`let-return[≤ _ ⇒ _ ] VL `in WM)     = (-, ε , VL) , (-, ε , WM)
halt[≤]-`let-return[≤]-`in-inversion-helper m′≤m₀ (ξ-`let-return[≰ m′≰m₀ ⇒-] L⟶[≤] `in? ◅ lrL′M⟶[≤]*)    WLM″                                  with () ← m′≰m₀ m′≤m₀
halt[≤]-`let-return[≤]-`in-inversion-helper m′≤m₀ (ξ-`let-return[≤ _ ⇒-] L⟶ `in? ◅ lrL′M⟶[≤]*)        WLM″
  with (_ , L′⟶* , WL″) , hM ← halt[≤]-`let-return[≤]-`in-inversion-helper m′≤m₀ lrL′M⟶[≤]* WLM″                                               = (-, L⟶ ◅ L′⟶* , WL″) , hM
halt[≤]-`let-return[≤]-`in-inversion-helper m′≤m₀ (ξ-`let-return[≰ m′≰m₀ ⇒-]! WL `in M⟶[≤] ◅ lrL′M⟶[≤]*) WLM″                                  with () ← m′≰m₀ m′≤m₀
halt[≤]-`let-return[≤]-`in-inversion-helper m′≤m₀ (ξ-`let-return[≤ _ ⇒-]! VL `in M⟶[≤] ◅ lrL′M⟶[≤]*)     WLM″
  with hL , (_ , M′⟶[≤]* , WM″) ← halt[≤]-`let-return[≤]-`in-inversion-helper m′≤m₀ lrL′M⟶[≤]* WLM″                                            = hL , (-, M⟶[≤] ◅ M′⟶[≤]* , WM″)

halt[≤]-`let-return[≤]-`in-inversion : m′ ≤ₘ m₀ →
                                       halt[ m′ ≤] (`let-return[ m₀ ⇒ m ] L `in M) →
                                       ----------------------------------------------
                                       halt L × halt[ m′ ≤] M
halt[≤]-`let-return[≤]-`in-inversion m′≤m₀ (_  , lrLM⟶[≤]* , WL′) = halt[≤]-`let-return[≤]-`in-inversion-helper m′≤m₀ lrLM⟶[≤]* WL′

halt[≤]-`let-return[≰]-`in-inversion-helper : ¬ (m′ ≤ₘ m₀) →
                                              `let-return[ m₀ ⇒ m ] L `in M ⟶[ m′ ≤]* L′ →
                                              DeferredTerm[ m′ ≤] L′ →
                                              ---------------------------------------------
                                              halt[ m′ ≤] L × halt[ m′ ≤] M
halt[≤]-`let-return[≰]-`in-inversion-helper m′≰m₀ ε                                                      (`let-return[≰ _ ⇒ _ ] WL `in WM)     = (-, ε , WL) , (-, ε , WM)
halt[≤]-`let-return[≰]-`in-inversion-helper m′≰m₀ ε                                                      (`let-return[≤ m′≤m₀ ⇒ _ ] VL `in WM) with () ← m′≰m₀ m′≤m₀
halt[≤]-`let-return[≰]-`in-inversion-helper m′≰m₀ (ξ-`let-return[≰ m′≰m₀ ⇒-] L⟶[≤] `in? ◅ lrL′M⟶[≤]*)    WLM″
  with (_ , L′⟶[≤]* , WL″) , hM ← halt[≤]-`let-return[≰]-`in-inversion-helper m′≰m₀ lrL′M⟶[≤]* WLM″                                            = (-, L⟶[≤] ◅ L′⟶[≤]* , WL″) , hM
halt[≤]-`let-return[≰]-`in-inversion-helper m′≰m₀ (ξ-`let-return[≤ m′≤m₀ ⇒-] L⟶[≤] `in? ◅ lrL′M⟶[≤]*)    WLM″                                  with () ← m′≰m₀ m′≤m₀
halt[≤]-`let-return[≰]-`in-inversion-helper m′≰m₀ (ξ-`let-return[≰ _ ⇒-]! WL `in M⟶[≤] ◅ lrL′M⟶[≤]*)     WLM″
  with hL , (_ , M′⟶[≤]* , WM″) ← halt[≤]-`let-return[≰]-`in-inversion-helper m′≰m₀ lrL′M⟶[≤]* WLM″                                            = hL , (-, M⟶[≤] ◅ M′⟶[≤]* , WM″)
halt[≤]-`let-return[≰]-`in-inversion-helper m′≰m₀ (ξ-`let-return[≤ m′≤m₀ ⇒-]! WL `in M⟶[≤] ◅ lrL′M⟶[≤]*) WLM″                                  with () ← m′≰m₀ m′≤m₀

halt[≤]-`let-return[≰]-`in-inversion : ¬ (m′ ≤ₘ m₀) →
                                       halt[ m′ ≤] (`let-return[ m₀ ⇒ m ] L `in M) →
                                       ----------------------------------------------
                                       halt[ m′ ≤] L × halt[ m′ ≤] M
halt[≤]-`let-return[≰]-`in-inversion m′≰m₀ (_  , lrLM⟶[≤]* , WL′) = halt[≤]-`let-return[≰]-`in-inversion-helper m′≰m₀ lrLM⟶[≤]* WL′

halt[≤]-`λ⦂-∘-inversion-helper : `λ⦂[ m ] S ∘ L ⟶[ m′ ≤]* L′ →
                                 DeferredTerm[ m′ ≤] L′ →
                                 ------------------------------
                                 halt[ m′ ≤] L
halt[≤]-`λ⦂-∘-inversion-helper ε                                 (`λ⦂[ _ ] _ ∘ WL) = -, ε , WL
halt[≤]-`λ⦂-∘-inversion-helper (ξ-`λ⦂[-]-∘ L⟶[≤] ◅ `λ⦂-∘L′⟶[≤]*) WL″
  with _ , L′⟶[≤]* , WL″ ← halt[≤]-`λ⦂-∘-inversion-helper `λ⦂-∘L′⟶[≤]* WL″         = -, L⟶[≤] ◅ L′⟶[≤]* , WL″

halt[≤]-`λ⦂-∘-inversion : halt[ m′ ≤] (`λ⦂[ m ] S ∘ L) →
                          -------------------------------
                          halt[ m′ ≤] L
halt[≤]-`λ⦂-∘-inversion (_  , `λ⦂-∘L⟶[≤]* , WL′) = halt[≤]-`λ⦂-∘-inversion-helper `λ⦂-∘L⟶[≤]* WL′

halt[≤]-`$-inversion-helper : L `$ M ⟶[ m′ ≤]* L′ →
                              DeferredTerm[ m′ ≤] L′ →
                              ------------------------------
                              halt[ m′ ≤] L × halt[ m′ ≤] M
halt[≤]-`$-inversion-helper ε                             (WL `$ WM)            = (-, ε , WL) , (-, ε , WM)
halt[≤]-`$-inversion-helper (ξ- L⟶[≤] `$? ◅ L′$M⟶[≤]*)    WLM″
  with (_ , L′⟶[≤]* , WL″) , h[≤]M ← halt[≤]-`$-inversion-helper L′$M⟶[≤]* WLM″ = (-, L⟶[≤] ◅ L′⟶[≤]* , WL″) , h[≤]M
halt[≤]-`$-inversion-helper (ξ-! WL `$ M⟶[≤] ◅ L′$M⟶[≤]*) WLM″
  with h[≤]L , (_ , M′⟶[≤]* , WM″) ← halt[≤]-`$-inversion-helper L′$M⟶[≤]* WLM″ = h[≤]L , (-, M⟶[≤] ◅ M′⟶[≤]* , WM″)

halt[≤]-`$-inversion : halt[ m′ ≤] (L `$ M) →
                       ------------------------------
                       halt[ m′ ≤] L × halt[ m′ ≤] M
halt[≤]-`$-inversion (_  , L$M⟶[≤]* , WL′) = halt[≤]-`$-inversion-helper L$M⟶[≤]* WL′
