{-# OPTIONS --safe #-}
module Calculus.GeneralOpSem where

open import Agda.Primitive
open import Data.Nat as ℕ using (ℕ; suc; _+_; s≤s)
import Data.Nat.Properties as ℕ
open import Data.Product using (Σ; _,_; ∃; ∃₂; _×_; -,_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)

infixr 25 wkidx[_↑_]_
infixr 25 idx[_/_]_along_

wkidx[_↑_]_ : ℕ → ℕ → ℕ → ℕ
wkidx[ n ↑ x ] y
  with y ℕ.≥? x
...  | no  _ = y
...  | yes _ = n + y

idx[_/_]_along_ : ∀ {ℓ} {A : Set ℓ} → A → ℕ → ℕ → (ℕ → A) → A
idx[ L / x ] y along `#_
  with y ℕ.≥? x
...  | no  _ = `# y
...  | yes _
    with y ℕ.≟ x
...    | no  _ = `# (ℕ.pred y)
...    | yes _ = L

module ⟶* {ℓ ℓ′} {A : Set ℓ} (_⟶_ : Rel A ℓ′) where
  open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_) public
  open import Relation.Binary.Construct.Closure.ReflexiveTransitive public

  infix   4 _⟶*_

  _⟶*_ = Star _⟶_

  ξ-of-↝*-⟶* : ∀ {ℓ″} (_↝_ : Rel A ℓ″) (f : A → A) →
               (∀ {L L′} → L ↝ L′ → f L ⟶ f L′) →
               ∀ {L L′} → Star _↝_ L L′ → f L ⟶* f L′
  ξ-of-↝*-⟶* _↝_ f ξ-rule ε           = ε
  ξ-of-↝*-⟶* _↝_ f ξ-rule (L⟶ ◅ L′⟶*) = ξ-rule L⟶ ◅ ξ-of-↝*-⟶* _↝_ f ξ-rule L′⟶*

  ξ-of-⟶* : (f : A → A) →
            (∀ {L L′} → L ⟶ L′ → f L ⟶ f L′) →
            ∀ {L L′} → L ⟶* L′ → f L ⟶* f L′
  ξ-of-⟶* = ξ-of-↝*-⟶* _⟶_

  ⟶*length : ∀ {L L′} → L ⟶* L′ → ℕ
  ⟶*length ε         = 0
  ⟶*length (_ ◅ L⟶*) = suc (⟶*length L⟶*)

  ⟶*-factor : (⟶-det : ∀ {L L₀ L₁} → L ⟶ L₀ → L ⟶ L₁ → L₀ ≡ L₁) →
              ∀ {L L₀ L₁} → 
              (L⟶*₀ : L ⟶* L₀) →
              (L⟶*₁ : L ⟶* L₁) →
              ⟶*length L⟶*₀ ℕ.≤ ⟶*length L⟶*₁ →
              Σ (L₀ ⟶* L₁) (λ L₀⟶* → ⟶*length L₀⟶* ℕ.≤ ⟶*length L⟶*₁)
  ⟶*-factor ⟶-det ε            L⟶*₁          L⟶*₀≤L⟶*₁              = L⟶*₁ , ℕ.≤-refl
  ⟶*-factor ⟶-det (L⟶ ◅ L′⟶*₀) (L⟶′ ◅ L″⟶*₁) (s≤s L⟶*₀≤L⟶*₁)
    rewrite ⟶-det L⟶ L⟶′
      with L₀⟶* , L₀⟶*≤L⟶*₁ ← ⟶*-factor ⟶-det L′⟶*₀ L″⟶*₁ L⟶*₀≤L⟶*₁ = L₀⟶* , ℕ.m≤n⇒m≤1+n L₀⟶*≤L⟶*₁
