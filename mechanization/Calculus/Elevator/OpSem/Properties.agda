------------------------------------------------------------
-- Non-interference of Elevator
------------------------------------------------------------

{-# OPTIONS --safe #-}
open import Calculus.Elevator.ModeSpec

module Calculus.Elevator.OpSem.Properties {ℓ₁ ℓ₂} (ℳ : ModeSpec ℓ₁ ℓ₂) where
open ModeSpec ℳ

open import Agda.Primitive
open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Properties as ℕ
open import Relation.Nullary using (¬_; yes; no)

import Calculus.Elevator.Syntax as S
import Calculus.Elevator.OpSem as O
open S ℳ
open O ℳ

infix   4 _≈[≥_]_

data _≈[≥_]_ : Term → Mode → Term → Set (ℓ₁ ⊔ ℓ₂) where
  `unit                 : `unit ≈[≥ m ] `unit

  `lift[≤_⇒_]           : m ≤ₘ m₀ →
                          (m₁ : Mode) →
                          L ≈[≥ m ] L′ →
                          -----------------------------------------------
                          `lift[ m₀ ⇒ m₁ ] L ≈[≥ m ] `lift[ m₀ ⇒ m₁ ] L′

  `lift[≰_⇒_]           : ¬ (m ≤ₘ m₀) →
                          (m₁ : Mode) →
                          (L : Term) →
                          (L′ : Term) →
                          ----------------------------------------------
                          `lift[ m₀ ⇒ m₁ ] L ≈[≥ m ] `lift[ m₀ ⇒ m₁ ] L′

  `unlift[_⇒_]          : (m₀ m₁ : Mode) →
                          L ≈[≥ m ] L′ →
                          ---------------------------------------------------
                          `unlift[ m₀ ⇒ m₁ ] L ≈[≥ m ] `unlift[ m₀ ⇒ m₁ ] L′


  `return[_⇒_]          : (m₀ m₁ : Mode) →
                          L ≈[≥ m ] L′ →
                          ---------------------------------------------------
                          `return[ m₀ ⇒ m₁ ] L ≈[≥ m ] `return[ m₀ ⇒ m₁ ] L′

  `let-return[_⇒_]_`in_ : (m₀ m₁ : Mode) →
                          L ≈[≥ m ] L′ →
                          M ≈[≥ m ] M′ →
                          ------------------------------------------------------------------------
                          `let-return[ m₀ ⇒ m₁ ] L `in M ≈[≥ m ] `let-return[ m₀ ⇒ m₁ ] L′ `in M′

  `λ⦂[_]_∘_             : (m₀ : Mode) → (S : Type) →
                          L ≈[≥ m ] L′ →
                          -----------------------------------------
                          `λ⦂[ m₀ ] S ∘ L ≈[≥ m ] `λ⦂[ m₀ ] S ∘ L′

  _`$_                  : L ≈[≥ m ] L′ →
                          M ≈[≥ m ] M′ →
                          ------------------------
                          L `$ M ≈[≥ m ] L′ `$ M′

  `#_                   : (x : ℕ) →
                          ------------------
                          `# x ≈[≥ m ] `# x

≈[≥]-refl : M ≈[≥ m ] M
≈[≥]-refl {`unit} = `unit
≈[≥]-refl {`lift[ m₀ ⇒ m₁ ] M}             {m}
  with m ≤?ₘ m₀
...  | yes m≤                    = `lift[≤ m≤ ⇒ _ ] ≈[≥]-refl
...  | no  m≰                    = `lift[≰ m≰ ⇒ _ ] _ _
≈[≥]-refl {`unlift[ m₀ ⇒ m₁ ] M} = `unlift[ _ ⇒ _ ] ≈[≥]-refl
≈[≥]-refl {`return[ m₀ ⇒ m₁ ] M} = `return[ _ ⇒ _ ] ≈[≥]-refl
≈[≥]-refl {`let-return[ m₀ ⇒ m₁ ] M `in N} = `let-return[ m₀ ⇒ m₁ ] ≈[≥]-refl `in ≈[≥]-refl
≈[≥]-refl {`λ⦂[ m ] S ∘ M} = `λ⦂[ _ ] _ ∘ ≈[≥]-refl
≈[≥]-refl {M `$ N} = ≈[≥]-refl `$ ≈[≥]-refl
≈[≥]-refl {`# x} = `# _

wk[↑]≈[≥]wk[↑] : L ≈[≥ m ] L′ →
                 wk[ k ↑ x ] L ≈[≥ m ] wk[ k ↑ x ] L′
wk[↑]≈[≥]wk[↑] `unit = `unit
wk[↑]≈[≥]wk[↑] (`lift[≤ m≤ ⇒ m₁ ] L≈L′) = `lift[≤ m≤ ⇒ m₁ ] (wk[↑]≈[≥]wk[↑] L≈L′)
wk[↑]≈[≥]wk[↑] (`lift[≰ m≰ ⇒ m₁ ] _ _) = `lift[≰ m≰ ⇒ m₁ ] _ _
wk[↑]≈[≥]wk[↑] (`unlift[ m₀ ⇒ m₁ ] L≈L′) = `unlift[ _ ⇒ _ ] (wk[↑]≈[≥]wk[↑] L≈L′)
wk[↑]≈[≥]wk[↑] (`return[ m₀ ⇒ m₁ ] L≈L′) = `return[ _ ⇒ _ ] (wk[↑]≈[≥]wk[↑] L≈L′)
wk[↑]≈[≥]wk[↑] (`let-return[ m₀ ⇒ m₁ ] L≈L′ `in M≈M′) = `let-return[ _ ⇒ _ ] wk[↑]≈[≥]wk[↑] L≈L′ `in wk[↑]≈[≥]wk[↑] M≈M′
wk[↑]≈[≥]wk[↑] (`λ⦂[ m₀ ] S ∘ L≈L′) = `λ⦂[ _ ] _ ∘ wk[↑]≈[≥]wk[↑] L≈L′
wk[↑]≈[≥]wk[↑] (L≈L′ `$ M≈M′) = wk[↑]≈[≥]wk[↑] L≈L′ `$ wk[↑]≈[≥]wk[↑] M≈M′
wk[↑]≈[≥]wk[↑] (`# x) = `# _

nonInterference : (M : Term) →
                  L ≈[≥ m ] L′ →
                  [ L /[ m′ ] x ] M ≈[≥ m ] [ L′ /[ m′ ] x ] M
nonInterference                           `unit                            L≈L′ = `unit
nonInterference {m = m}                   (`lift[ m₀ ⇒ m₁ ] M)             L≈L′
  with m ≤?ₘ m₀
...  | yes m≤                                                                   = `lift[≤ m≤ ⇒ _ ] (nonInterference M L≈L′)
...  | no  m≰                                                                   = `lift[≰ m≰ ⇒ _ ] _ _
nonInterference         {m′ = m′}         (`unlift[ m₀ ⇒ m₁ ] M)           L≈L′
  with m₀ ≤?ₘ m′
...  | yes _                                                                    = `unlift[ _ ⇒ _ ] (nonInterference M L≈L′)
...  | no  _                                                                    = `unlift[ _ ⇒ _ ] (nonInterference M ≈[≥]-refl)
nonInterference         {m′ = m′}         (`return[ m₀ ⇒ m₁ ] M)           L≈L′
  with m₀ ≤?ₘ m′
...  | yes _                                                                    = `return[ _ ⇒ _ ] (nonInterference M L≈L′)
...  | no  _                                                                    = `return[ _ ⇒ _ ] (nonInterference M ≈[≥]-refl)
nonInterference                           (`let-return[ m₀ ⇒ m₁ ] M `in N) L≈L′ = `let-return[ _ ⇒ _ ] nonInterference M L≈L′ `in nonInterference N (wk[↑]≈[≥]wk[↑] L≈L′)
nonInterference                           (`λ⦂[ m₀ ] S ∘ M)                L≈L′ = `λ⦂[ _ ] _ ∘ nonInterference M (wk[↑]≈[≥]wk[↑] L≈L′)
nonInterference                           (M `$ N)                         L≈L′ = nonInterference M L≈L′ `$ nonInterference N L≈L′
nonInterference                   {x = x} (`# y)                           L≈L′
  with y ℕ.≥? x
...  | no  _                                                                    = `# _
...  | yes _
    with y ℕ.≟ x
...    | no  _                                                                  = `# _
...    | yes _                                                                  = L≈L′
