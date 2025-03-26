{-# OPTIONS --safe #-}
module Calculus.DILL.Typing.Properties where

import Data.Bool.Properties as Bool
open import Data.Nat as ℕ using (ℕ; suc; s≤s; _+_)
open import Data.Nat.Properties as ℕ
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; -,_; ∃₂)
import Data.List.Relation.Unary.All.Properties as All
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Calculus.DILL.Syntax
open import Calculus.DILL.Typing

length-respects-~⊞ : ψ₀ ~ ψ₀₀ ⊞ ψ₀₁ →
                     ------------------------------------------------
                     length ψ₀₀ ≡ length ψ₀ × length ψ₀₁ ≡ length ψ₀
length-respects-~⊞ []       = refl , refl
length-respects-~⊞ (_ ∷ ψ₀~) = cong suc (proj₁ (length-respects-~⊞ ψ₀~)) , cong suc (proj₂ (length-respects-~⊞ ψ₀~))

~⊞-preserves-++ : ∀ ψ₀ →
                  ψ₀ ++ ψ₀′ ~ ψ₀₀ ⊞ ψ₀₁ →
                  -----------------------------------
                  ∃₂ (λ ψ₀₀′ ψ₀₀″ →
                    ∃₂ (λ ψ₀₁′ ψ₀₁″ → ψ₀₀ ≡ ψ₀₀′ ++ ψ₀₀″
                                    × ψ₀₁ ≡ ψ₀₁′ ++ ψ₀₁″
                                    × ψ₀ ~ ψ₀₀′ ⊞ ψ₀₁′
                                    × ψ₀′ ~ ψ₀₀″ ⊞ ψ₀₁″))
~⊞-preserves-++ []       ψ₀′~                                               = -, -, -, -, refl , refl , [] , ψ₀′~
~⊞-preserves-++ (_ ∷ ψ₀) (d₀~ ∷ ψ₀ψ₀′~)
  with _ , _ , _ , _ , refl , refl , ψ₀~ , ψ₀′~ ← ~⊞-preserves-++ ψ₀ ψ₀ψ₀′~ = -, -, -, -, refl , refl , d₀~ ∷ ψ₀~ , ψ₀′~

~⊞-++ : ψ₀ ~ ψ₀₀ ⊞ ψ₀₁ →
        ψ₀′ ~ ψ₀₂ ⊞ ψ₀₃ →
        ψ₀ ++ ψ₀′ ~ ψ₀₀ ++ ψ₀₂ ⊞ ψ₀₁ ++ ψ₀₃
~⊞-++ []         ψ₀′~ = ψ₀′~
~⊞-++ (d~ ∷ ψ₀~) ψ₀′~ = d~ ∷ ~⊞-++ ψ₀~ ψ₀′~

is-all-dis-~⊞ : ψ₀ is-all-dis →
                ψ₀ ~ ψ₀ ⊞ ψ₀
is-all-dis-~⊞ []             = []
is-all-dis-~⊞ (refl ∷ ψ₀Dis) = unusable ∷ is-all-dis-~⊞ ψ₀Dis

∈¹-++ˡ : ∀ ψ₁₁ →
         u ⦂ P ∈¹ ψ₁₀ →
         ---------------------------------
         length ψ₁₁ + u ⦂ P ∈¹ ψ₁₁ ++ ψ₁₀
∈¹-++ˡ {u} []        u∈
  rewrite ℕ.+-identityʳ u      = u∈
∈¹-++ˡ {u} (B ∷ ψ₁₁) u∈
  rewrite +-suc u (length ψ₁₁) = there (∈¹-++ˡ ψ₁₁ u∈)

∈⁰-++ˡ : ψ₀₁ is-all-dis →
         x ⦂ P ∈⁰ ψ₀₀ →
         ---------------------------------
         length ψ₀₁ + x ⦂ P ∈⁰ ψ₀₁ ++ ψ₀₀
∈⁰-++ˡ {_}   {x} []              x∈
  rewrite ℕ.+-identityʳ x           = x∈
∈⁰-++ˡ {ψ₀₁} {x} (refl ∷ ψ₀₁Dis) x∈
  rewrite +-suc x (length ψ₀₁)      = there (∈⁰-++ˡ ψ₀₁Dis x∈)

∈¹-++ʳ : ∀ ψ₁₀ →
         u ⦂ P ∈¹ ψ₁₁ →
         --------------------
         u ⦂ P ∈¹ ψ₁₁ ++ ψ₁₀
∈¹-++ʳ ψ₁₀ here       = here
∈¹-++ʳ ψ₁₀ (there u∈) = there (∈¹-++ʳ ψ₁₀ u∈)

∈⁰-++ʳ : ψ₀₀ is-all-dis →
         x ⦂ P ∈⁰ ψ₀₁ →
         ----------------------
         x ⦂ P ∈⁰ ψ₀₁ ++ ψ₀₀
∈⁰-++ʳ ψ₀₀Dis (here ψ₀₁Dis) = here (All.++⁺ ψ₀₁Dis ψ₀₀Dis)
∈⁰-++ʳ ψ₀₀Dis (there x∈)    = there (∈⁰-++ʳ ψ₀₀Dis x∈)

>∈¹-++⇒∈¹ : ∀ ψ₁₁ →
            length ψ₁₁ ℕ.> u →
            u ⦂ P ∈¹ ψ₁₁ ++ ψ₁₀ →
            ----------------------
            u ⦂ P ∈¹ ψ₁₁
>∈¹-++⇒∈¹ (_ ∷ ψ₁₁) >u       here       = here
>∈¹-++⇒∈¹ (_ ∷ ψ₁₁) (s≤s >u) (there u∈) = there (>∈¹-++⇒∈¹ ψ₁₁ >u u∈)

>∈⁰-++⇒∈⁰ : ∀ ψ₀₁ →
            length ψ₀₁ ℕ.> x →
            x ⦂ P ∈⁰ ψ₀₁ ++ ψ₀₀ →
            ----------------------
            x ⦂ P ∈⁰ ψ₀₁
>∈⁰-++⇒∈⁰ (_ ∷ ψ₀₁) >x       (here ψ₀₁ψ₀₀Dis) = here (All.++⁻ˡ ψ₀₁ ψ₀₁ψ₀₀Dis)
>∈⁰-++⇒∈⁰ (_ ∷ ψ₀₁) (s≤s >x) (there x∈)       = there (>∈⁰-++⇒∈⁰ ψ₀₁ >x x∈)

⊢⇒++⊢ : ψ₀₀ is-all-dis →
        ψ₁ ⍮ ψ₀₁ ⊢ I ⦂ P →
        ------------------------
        ψ₁ ⍮ ψ₀₁ ++ ψ₀₀ ⊢ I ⦂ P
⊢⇒++⊢ ψ₀₀Dis (`unit ψ₀₁Dis)              = `unit (All.++⁺ ψ₀₁Dis ψ₀₀Dis)
⊢⇒++⊢ ψ₀₀Dis (ψ₀₁Dis ⊢`bang ⊢I)          = All.++⁺ ψ₀₁Dis ψ₀₀Dis ⊢`bang ⊢⇒++⊢ ψ₀₀Dis ⊢I
⊢⇒++⊢ ψ₀₀Dis (ψ₀₁~ ⊢`let-bang ⊢I `in ⊢J) = ~⊞-++ ψ₀₁~ (is-all-dis-~⊞ ψ₀₀Dis) ⊢`let-bang ⊢⇒++⊢ ψ₀₀Dis ⊢I `in ⊢⇒++⊢ ψ₀₀Dis ⊢J
⊢⇒++⊢ ψ₀₀Dis (`λ⦂-∘ ⊢I)                  = `λ⦂-∘ ⊢⇒++⊢ ψ₀₀Dis ⊢I
⊢⇒++⊢ ψ₀₀Dis (ψ₀₁~ ⊢ ⊢I `$ ⊢J)           = ~⊞-++ ψ₀₁~ (is-all-dis-~⊞ ψ₀₀Dis) ⊢ ⊢⇒++⊢ ψ₀₀Dis ⊢I `$ ⊢⇒++⊢ ψ₀₀Dis ⊢J
⊢⇒++⊢ ψ₀₀Dis (ψ₀₁Dis ⊢`#¹ u∈)            = All.++⁺ ψ₀₁Dis ψ₀₀Dis ⊢`#¹ u∈
⊢⇒++⊢ ψ₀₀Dis (`#⁰ x∈)                    = `#⁰ ∈⁰-++ʳ ψ₀₀Dis x∈
