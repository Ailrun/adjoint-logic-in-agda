------------------------------------------------------------
-- Properties of (Declarative) Static Rules for Elevator
------------------------------------------------------------

{-# OPTIONS --safe #-}
open import Calculus.Elevator.ModeSpec

module Calculus.Elevator.Typing.Properties {ℓ₁ ℓ₂} (ℳ : ModeSpec ℓ₁ ℓ₂) where
open ModeSpec ℳ

open import Data.Bool as Bool using (true; false)
open import Data.List as List using ([]; _∷_; _++_; length)
import Data.List.Properties as List
open import Data.List.Relation.Unary.All as All using ([]; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.Nat as ℕ using (suc; _+_; s≤s)
import Data.Nat.Properties as ℕ
open import Data.Product as × using (_×_; _,_; proj₁; proj₂; ∃; ∃₂; -,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import Calculus.Elevator.Syntax as S
import Calculus.Elevator.Typing as T
import Calculus.Elevator.OpSem as O
open S ℳ
open T ℳ
open O ℳ

left-bias-~d⊞ : ∀ m d →
                ----------------------------
                ∃ (λ d₁ → d [ m ]~d d ⊞ d₁)
left-bias-~d⊞ _ false = -, unusable
left-bias-~d⊞ _ true  = -, to-left

left-bias-~⊞ : ∀ Γ →
               ----------------------
               ∃ (λ Γ₁ → Γ ~ Γ ⊞ Γ₁)
left-bias-~⊞ []                = -, []
left-bias-~⊞ ((S , m , d) ∷ Γ)
  with _ , d~ ← left-bias-~d⊞ m d
     | _ , Γ~ ← left-bias-~⊞ Γ = -, d~ ∷ Γ~

left-bias-~d⊞-is-del : ∀ m d →
                       --------------------------------------
                       proj₁ (left-bias-~d⊞ m d) [ m ]is-del
left-bias-~d⊞-is-del m false = unusable
left-bias-~d⊞-is-del m true  = unusable

left-bias-~⊞-is-all-del : ∀ Γ →
                          ----------------------------------
                          proj₁ (left-bias-~⊞ Γ) is-all-del
left-bias-~⊞-is-all-del []                = []
left-bias-~⊞-is-all-del ((S , m , d) ∷ Γ) = left-bias-~d⊞-is-del m d ∷ left-bias-~⊞-is-all-del Γ

length-respects-~⊞ : Γ ~ Γ₀ ⊞ Γ₁ →
                     --------------------------------------------
                     length Γ₀ ≡ length Γ × length Γ₁ ≡ length Γ
length-respects-~⊞ []       = refl , refl
length-respects-~⊞ (_ ∷ Γ~)
  with eq₀ , eq₁ ← length-respects-~⊞ Γ~
    rewrite eq₀
          | eq₁             = refl , refl

~d⊞-commute : d [ m ]~d d₀ ⊞ d₁ →
              --------------------
              d [ m ]~d d₁ ⊞ d₀
~d⊞-commute (contraction Co∈m) = contraction Co∈m
~d⊞-commute to-left            = to-right
~d⊞-commute to-right           = to-left
~d⊞-commute unusable           = unusable

~⊞-commute : Γ ~ Γ₀ ⊞ Γ₁ →
             --------------
             Γ ~ Γ₁ ⊞ Γ₀
~⊞-commute []        = []
~⊞-commute (d~ ∷ Γ~) = ~d⊞-commute d~ ∷ ~⊞-commute Γ~

~⊞-preserves-++ : ∀ Δ →
                  Δ ++ Ψ ~ Γ₀ ⊞ Γ₁ →
                  ------------------------------
                  ∃₂ (λ Δ₀ Δ₁ →
                    ∃₂ (λ Ψ₀ Ψ₁ → Γ₀ ≡ Δ₀ ++ Ψ₀
                                × Γ₁ ≡ Δ₁ ++ Ψ₁
                                × Δ ~ Δ₀ ⊞ Δ₁
                                × Ψ ~ Ψ₀ ⊞ Ψ₁))
~⊞-preserves-++ []      Ψ~                                           = -, -, -, -, refl , refl , [] , Ψ~
~⊞-preserves-++ (_ ∷ Δ) (d~ ∷ ΔΨ~)
  with _ , _ , _ , _ , refl , refl , Δ~ , Ψ~ ← ~⊞-preserves-++ Δ ΔΨ~ = -, -, -, -, refl , refl , d~ ∷ Δ~ , Ψ~

~⊞-++⁺ : Γ ~ Γ₀ ⊞ Γ₁ →
         Δ ~ Δ₀ ⊞ Δ₁ →
         -----------------------------
         Γ ++ Δ ~ Γ₀ ++ Δ₀ ⊞ Γ₁ ++ Δ₁
~⊞-++⁺ []        Δ~ = Δ~
~⊞-++⁺ (e~ ∷ Γ~) Δ~ = e~ ∷ ~⊞-++⁺ Γ~ Δ~

~d⊞-identityˡ : ∀ d →
                --------------------
                d [ m ]~d false ⊞ d
~d⊞-identityˡ false = unusable
~d⊞-identityˡ true  = to-right

~d⊞-identityʳ : ∀ d →
                --------------------
                d [ m ]~d d ⊞ false
~d⊞-identityʳ false = unusable
~d⊞-identityʳ true  = to-left

~d⊞-assocˡ : d [ m ]~d d₀ ⊞ d₁ →
             d₀ [ m ]~d d₂ ⊞ d₃ →
             -----------------------------------------------------
             ∃ (λ d₁′ → d₁′ [ m ]~d d₃ ⊞ d₁ × d [ m ]~d d₂ ⊞ d₁′)
~d⊞-assocˡ d~              to-left            = -, ~d⊞-identityˡ _ , d~
~d⊞-assocˡ d~              to-right           = -, d~ , ~d⊞-identityˡ _
~d⊞-assocˡ d~              unusable           = -, ~d⊞-identityˡ _ , d~
~d⊞-assocˡ (contraction _) (contraction Co∈m) = -, contraction Co∈m , contraction Co∈m
~d⊞-assocˡ to-left         (contraction Co∈m) = -, to-left , contraction Co∈m

~⊞-assocˡ : Γ ~ Γ₀ ⊞ Γ₁ →
            Γ₀ ~ Γ₂ ⊞ Γ₃ →
            -----------------------------------------
            ∃ (λ Γ₁′ → Γ₁′ ~ Γ₃ ⊞ Γ₁ × Γ ~ Γ₂ ⊞ Γ₁′)
~⊞-assocˡ [] []                          = _ , [] , []
~⊞-assocˡ (d~ ∷ Γ~) (d₀~ ∷ Γ₀~)
  with _ , d₁′~ , d~′ ← ~d⊞-assocˡ d~ d₀~
     | _ , Γ₁′~ , Γ~′ ← ~⊞-assocˡ Γ~ Γ₀~ = -, d₁′~ ∷ Γ₁′~ , d~′ ∷ Γ~′

~⊞-assocʳ : Γ ~ Γ₀ ⊞ Γ₁ →
            Γ₁ ~ Γ₂ ⊞ Γ₃ →
            -----------------------------------------
            ∃ (λ Γ₀′ → Γ₀′ ~ Γ₀ ⊞ Γ₂ × Γ ~ Γ₀′ ⊞ Γ₃)
~⊞-assocʳ Γ~ Γ₁~
  with _ , Γ₀′~ , Γ~′ ← ~⊞-assocˡ (~⊞-commute Γ~) (~⊞-commute Γ₁~) = -, ~⊞-commute Γ₀′~ , ~⊞-commute Γ~′

~d⊞-contraction-assocˡ : d [ m₀ ]~d d₀ ⊞ d₁ →
                         d₀ [ m₀ ]~d d₂ ⊞ d₃ →
                         [ m₀ ]⊢[ m ]d d₁ →
                         Bool.T (stₘ m ``Co) →
                         --------------------------------------
                         ∃₂ (λ d₂′ d₃′ → d₂′ [ m₀ ]~d d₂ ⊞ d₁
                                       × d₃′ [ m₀ ]~d d₃ ⊞ d₁
                                       × d [ m₀ ]~d d₂′ ⊞ d₃′)
~d⊞-contraction-assocˡ (contraction Co∈m₀) (contraction _) ⊢d         Co∈m = -, -, contraction Co∈m₀ , contraction Co∈m₀ , contraction Co∈m₀
~d⊞-contraction-assocˡ (contraction Co∈m₀) to-left         ⊢d         Co∈m = -, -, contraction Co∈m₀ , to-right , contraction Co∈m₀
~d⊞-contraction-assocˡ (contraction Co∈m₀) to-right        ⊢d         Co∈m = -, -, to-right , contraction Co∈m₀ , contraction Co∈m₀
~d⊞-contraction-assocˡ to-left             d₀~             ⊢d         Co∈m = -, -, ~d⊞-identityʳ _ , ~d⊞-identityʳ _ , d₀~
~d⊞-contraction-assocˡ to-right            unusable        (valid m≤) Co∈m = -, -, to-right , to-right , contraction (isWellStructuredₘ _ _ ``Co m≤ Co∈m)
~d⊞-contraction-assocˡ unusable            d₀~             ⊢d         Co∈m = -, -, ~d⊞-identityʳ _ , ~d⊞-identityʳ _ , d₀~

~⊞-contraction-assocˡ : Γ ~ Γ₀ ⊞ Γ₁ →
                        Γ₀ ~ Γ₂ ⊞ Γ₃ →
                        ⊢[ m ] Γ₁ →
                        Bool.T (stₘ m ``Co) →
                        -------------------------------
                        ∃₂ (λ Γ₂′ Γ₃′ → Γ₂′ ~ Γ₂ ⊞ Γ₁
                                      × Γ₃′ ~ Γ₃ ⊞ Γ₁
                                      × Γ ~ Γ₂′ ⊞ Γ₃′)
~⊞-contraction-assocˡ []        []          []                 Co∈m      = -, -, [] , [] , []
~⊞-contraction-assocˡ (d~ ∷ Γ~) (d₀~ ∷ Γ₀~) ((⊢S , ⊢d₁) ∷ ⊢Γ₁) Co∈m
  with _ , _ , d₂′~ , d₃′~ , d~′ ← ~d⊞-contraction-assocˡ d~ d₀~ ⊢d₁ Co∈m
     | _ , _ , Γ₂′~ , Γ₃′~ , Γ~′ ← ~⊞-contraction-assocˡ Γ~ Γ₀~ ⊢Γ₁ Co∈m = -, -, d₂′~ ∷ Γ₂′~ , d₃′~ ∷ Γ₃′~ , d~′ ∷ Γ~′

~⊞-contraction-assocʳ : Γ ~ Γ₀ ⊞ Γ₁ →
                        Γ₁ ~ Γ₂ ⊞ Γ₃ →
                        ⊢[ m ] Γ₀ →
                        Bool.T (stₘ m ``Co) →
                        -------------------------------
                        ∃₂ (λ Γ₂′ Γ₃′ → Γ₂′ ~ Γ₀ ⊞ Γ₂
                                      × Γ₃′ ~ Γ₀ ⊞ Γ₃
                                      × Γ ~ Γ₂′ ⊞ Γ₃′)
~⊞-contraction-assocʳ Γ~ Γ₁~ ⊢Γ₀ Co∈m
  with _ , _ , Γ₂′~ , Γ₃′~ , Γ~′ ← ~⊞-contraction-assocˡ (~⊞-commute Γ~) Γ₁~ ⊢Γ₀ Co∈m = -, -, ~⊞-commute Γ₂′~ , ~⊞-commute Γ₃′~ , Γ~′

~d⊞-preserves-is-del : d [ m ]is-del →
                       d [ m ]~d d₀ ⊞ d₁ →
                       --------------------------------
                       d₀ [ m ]is-del × d₁ [ m ]is-del
~d⊞-preserves-is-del dDel (contraction Co∈m) = dDel , dDel
~d⊞-preserves-is-del dDel to-left            = dDel , unusable
~d⊞-preserves-is-del dDel to-right           = unusable , dDel
~d⊞-preserves-is-del dDel unusable           = dDel , dDel

~d⊞⁻¹-preserves-is-del : d₀ [ m ]is-del →
                         d₁ [ m ]is-del →
                         d [ m ]~d d₀ ⊞ d₁ →
                         --------------------
                         d [ m ]is-del
~d⊞⁻¹-preserves-is-del d₀Del d₁Del (contraction Co∈m) = d₀Del
~d⊞⁻¹-preserves-is-del d₀Del d₁Del to-left            = d₀Del
~d⊞⁻¹-preserves-is-del d₀Del d₁Del to-right           = d₁Del
~d⊞⁻¹-preserves-is-del d₀Del d₁Del unusable           = d₀Del

~⊞-preserves-is-all-del : Γ is-all-del →
                          Γ ~ Γ₀ ⊞ Γ₁ →
                          ------------------------------
                          Γ₀ is-all-del × Γ₁ is-all-del
~⊞-preserves-is-all-del []            []               = [] , []
~⊞-preserves-is-all-del (dDel ∷ ΓDel) (d~ ∷ Γ~)
  with d₀Del , d₁Del ← ~d⊞-preserves-is-del dDel d~
     | Γ₀Del , Γ₁Del ← ~⊞-preserves-is-all-del ΓDel Γ~ = d₀Del ∷ Γ₀Del , d₁Del ∷ Γ₁Del

~⊞⁻¹-preserves-is-all-del : Γ₀ is-all-del →
                            Γ₁ is-all-del →
                            Γ ~ Γ₀ ⊞ Γ₁ →
                            ----------------
                            Γ is-all-del
~⊞⁻¹-preserves-is-all-del []              []              []        = []
~⊞⁻¹-preserves-is-all-del (d₀Del ∷ Γ₀Del) (d₁Del ∷ Γ₁Del) (d~ ∷ Γ~) = ~d⊞⁻¹-preserves-is-del d₀Del d₁Del d~ ∷ ~⊞⁻¹-preserves-is-all-del Γ₀Del Γ₁Del Γ~

is-del⇒∤d : ∀ m →
            d [ m₀ ]is-del →
            ------------------------------------------------
            ∃ (λ d′ → d [ m₀ ]∤[ m ]d d′ × d′ [ m₀ ]is-del)
is-del⇒∤d {m₀ = m₀} m dDel
  with m ≤?ₘ m₀
...  | no  ≰m₀ = -, delete ≰m₀ dDel , unusable
...  | yes ≤m₀ = -, keep ≤m₀ , dDel

is-all-del⇒∤ : ∀ m →
               Γ is-all-del →
               ---------------------------------------
               ∃ (λ Γ′ → Γ ∤[ m ] Γ′ × Γ′ is-all-del)
is-all-del⇒∤ m []                   = -, [] , []
is-all-del⇒∤ m (dDel ∷ ΓDel)
  with _ , d∤ , d′Del ← is-del⇒∤d m dDel
     | _ , Γ∤ , Γ′Del ← is-all-del⇒∤ m ΓDel = -, d∤ ∷ Γ∤ , d′Del ∷ Γ′Del

∤d⇒~d⊞-is-delʳ : d [ m₀ ]∤[ m ]d d′ →
                 ------------------------------------------------
                 ∃ (λ d₁ → d [ m₀ ]~d d′ ⊞ d₁ × d₁ [ m₀ ]is-del)
∤d⇒~d⊞-is-delʳ (delete ≰m₀ dDel) = -, ~d⊞-identityˡ _ , dDel
∤d⇒~d⊞-is-delʳ (keep ≤m₀)        = -, ~d⊞-identityʳ _ , unusable

∤⇒~⊞-is-all-delʳ : Γ ∤[ m ] Γ′ →
                   ---------------------------------------
                   ∃ (λ Γ₁ → Γ ~ Γ′ ⊞ Γ₁ × Γ₁ is-all-del)
∤⇒~⊞-is-all-delʳ []                         = -, [] , []
∤⇒~⊞-is-all-delʳ (d∤ ∷ Γ∤)
  with _ , d~ , d₁Del ← ∤d⇒~d⊞-is-delʳ d∤
     | _ , Γ~ , Γ₁Del ← ∤⇒~⊞-is-all-delʳ Γ∤ = -, d~ ∷ Γ~ , d₁Del ∷ Γ₁Del

length-respects-∤ : Γ ∤[ m ] Γ′ →
                    ---------------------
                    length Γ′ ≡ length Γ
length-respects-∤ []        = refl
length-respects-∤ (e∤ ∷ Γ∤) = cong suc (length-respects-∤ Γ∤)

∤d⁻¹-preserves-~d⊞ : d [ m₀ ]~d d₀ ⊞ d₁ →
                     d′ [ m₀ ]∤[ m ]d d →
                     --------------------------------------
                     ∃₂ (λ d′₀ d′₁ → d′ [ m₀ ]~d d′₀ ⊞ d′₁
                                   × d′₀ [ m₀ ]∤[ m ]d d₀
                                   × d′₁ [ m₀ ]∤[ m ]d d₁)
∤d⁻¹-preserves-~d⊞ d~       (keep ≤m₀)                     = -, -, d~ , keep ≤m₀ , keep ≤m₀
∤d⁻¹-preserves-~d⊞ unusable (delete ≰m₀ unusable)          = -, -, unusable , delete ≰m₀ unusable , delete ≰m₀ unusable
∤d⁻¹-preserves-~d⊞ unusable (delete ≰m₀ (weakening Wk∈m₀)) = -, -, to-left , delete ≰m₀ (weakening Wk∈m₀) , delete ≰m₀ unusable

∤⁻¹-preserves-~⊞ : Γ ~ Γ₀ ⊞ Γ₁ →
                   Γ′ ∤[ m ] Γ →
                   -------------------------------
                   ∃₂ (λ Γ′₀ Γ′₁ → Γ′ ~ Γ′₀ ⊞ Γ′₁
                                 × Γ′₀ ∤[ m ] Γ₀
                                 × Γ′₁ ∤[ m ] Γ₁)
∤⁻¹-preserves-~⊞ []        []                             = -, -, [] , [] , []
∤⁻¹-preserves-~⊞ (d~ ∷ Γ~) (∤d ∷ ∤Γ)
  with _ , _ , Γ′~ , ∤Γ₀ , ∤Γ₁ ← ∤⁻¹-preserves-~⊞ Γ~ ∤Γ
     | _ , _ , d′~ , ∤d₀ , ∤d₁ ← ∤d⁻¹-preserves-~d⊞ d~ ∤d = -, -, d′~ ∷ Γ′~ , ∤d₀ ∷ ∤Γ₀ , ∤d₁ ∷ ∤Γ₁

∤-preserves-++ : ∀ Δ →
                 Δ ++ Ψ ∤[ m ] Γ →
                 ---------------------------
                 ∃₂ (λ Δ′ Ψ′ → Γ ≡ Δ′ ++ Ψ′
                             × Δ ∤[ m ] Δ′
                             × Ψ ∤[ m ] Ψ′)
∤-preserves-++ []      Ψ∤                            = -, -, refl , [] , Ψ∤
∤-preserves-++ (_ ∷ Δ) (d∤ ∷ ΔΨ∤)
  with _ , _ , refl , Δ∤ , Ψ∤ ← ∤-preserves-++ Δ ΔΨ∤ = -, -, refl , d∤ ∷ Δ∤ , Ψ∤

~d⊞⁻¹-preserves-∤d : d₀ [ m₀ ]∤[ m ]d dS₀ → 
                     d₁ [ m₀ ]∤[ m ]d dS₁ → 
                     d [ m₀ ]~d d₀ ⊞ d₁ →
                     ------------------------------------------------------
                     ∃ (λ dS → d [ m₀ ]∤[ m ]d dS × dS [ m₀ ]~d dS₀ ⊞ dS₁)
~d⊞⁻¹-preserves-∤d (delete m≰ d₀Del) (delete _  d₁Del) d~ = -, delete m≰ (~d⊞⁻¹-preserves-is-del d₀Del d₁Del d~) , unusable
~d⊞⁻¹-preserves-∤d (delete m≰ d₀Del) (keep m≤)         d~ with () ← m≰ m≤
~d⊞⁻¹-preserves-∤d (keep m≤)         (delete m≰ d₁Del) d~ with () ← m≰ m≤
~d⊞⁻¹-preserves-∤d (keep m≤)         (keep _)          d~ = -, keep m≤ , d~

~⊞⁻¹-preserves-∤ : Γ₀ ∤[ m ] Δ₀ → 
                   Γ₁ ∤[ m ] Δ₁ → 
                   Γ ~ Γ₀ ⊞ Γ₁ →
                   -----------------------------------
                   ∃ (λ Δ → Γ ∤[ m ] Δ × Δ ~ Δ₀ ⊞ Δ₁)
~⊞⁻¹-preserves-∤ []          []          [] = -, [] , []
~⊞⁻¹-preserves-∤ (d₀∤ ∷ Γ₀∤) (d₁∤ ∷ Γ₁∤) (d~ ∷ Γ~)
  with _ , d∤ , dS~ ← ~d⊞⁻¹-preserves-∤d d₀∤ d₁∤ d~
     | _ , Γ∤ , Δ~ ← ~⊞⁻¹-preserves-∤ Γ₀∤ Γ₁∤ Γ~ = -, d∤ ∷ Γ∤ , dS~ ∷ Δ~

assoc-∤d : d [ m₀ ]∤[ m ]d d′ →
           d′ [ m₀ ]∤[ m′ ]d d″ →
           -----------------------------------------------------
           ∃ (λ d‴ → d [ m₀ ]∤[ m′ ]d d‴ × d‴ [ m₀ ]∤[ m ]d d″)
assoc-∤d (delete m≰ eDel) (delete m₀≰ e′Del) = -, delete m₀≰ eDel , delete m≰ e′Del
assoc-∤d (delete m≰ eDel) (keep m₀≤)         = -, keep m₀≤ , delete m≰ eDel
assoc-∤d (keep m≤)        d′∤                = -, d′∤ , keep m≤

assoc-∤ : Γ ∤[ m ] Γ′ →
          Γ′ ∤[ m₀ ] Γ″ →
          ---------------------------------------
          ∃ (λ Γ‴ → Γ ∤[ m₀ ] Γ‴ × Γ‴ ∤[ m ] Γ″)
assoc-∤ []        []                  = -, [] , []
assoc-∤ (d∤ ∷ Γ∤) (d′∤ ∷ Γ′∤)
  with _ , d∤′ , ∤d″ ← assoc-∤d d∤ d′∤
     | _ , Γ∤′ , ∤Γ″ ← assoc-∤ Γ∤ Γ′∤ = -, d∤′ ∷ Γ∤′ , ∤d″ ∷ ∤Γ″

∤-++⁺ : Γ ∤[ m ] Γ′ →
        Δ ∤[ m ] Δ′ →
        -----------------------
        Γ ++ Δ ∤[ m ] Γ′ ++ Δ′
∤-++⁺ []        Δ∤ = Δ∤
∤-++⁺ (e∤ ∷ Γ∤) Δ∤ = e∤ ∷ ∤-++⁺ Γ∤ Δ∤

∤d-preserves-is-del : d [ m₀ ]is-del →
                      d [ m₀ ]∤[ m ]d d′ →
                      ---------------------
                      d′ [ m₀ ]is-del
∤d-preserves-is-del dDel              (keep m≤)        = dDel
∤d-preserves-is-del unusable          (delete m≰ dDel) = dDel
∤d-preserves-is-del (weakening Wk∈m₀) (delete m≰ dDel) = unusable

∤d⁻¹-preserves-is-del : d′ [ m₀ ]is-del →
                        d [ m₀ ]∤[ m ]d d′ →
                        ---------------------
                        d [ m₀ ]is-del
∤d⁻¹-preserves-is-del dDel     (keep m≤)        = dDel
∤d⁻¹-preserves-is-del unusable (delete m≰ dDel) = dDel

∤-preserves-is-all-del : Γ is-all-del →
                         Γ ∤[ m ] Γ′ →
                         ---------------
                         Γ′ is-all-del
∤-preserves-is-all-del []            []        = []
∤-preserves-is-all-del (dDel ∷ ΓDel) (d∤ ∷ Γ∤) = ∤d-preserves-is-del dDel d∤ ∷ ∤-preserves-is-all-del ΓDel Γ∤

∤⁻¹-preserves-is-all-del : Γ′ is-all-del →
                           Γ ∤[ m ] Γ′ →
                           ----------------
                           Γ is-all-del
∤⁻¹-preserves-is-all-del []              []        = []
∤⁻¹-preserves-is-all-del (d′Del ∷ Γ′Del) (d∤ ∷ Γ∤) = ∤d⁻¹-preserves-is-del d′Del d∤ ∷ ∤⁻¹-preserves-is-all-del Γ′Del Γ∤

len∈-inversion : ∀ Δ →
                 length Δ ⦂[ m ] S ∈ Δ ++ (T , m₀ , d) ∷ Γ →
                 ------------------------------------------------
                 (Δ ++ Γ) is-all-del × T ≡ S × m₀ ≡ m × d ≡ true
len∈-inversion []      (here ΓDel) = ΓDel , refl , refl , refl
len∈-inversion (_ ∷ Δ) (there dDel lenΔ∈)
  with ΔΓDel , refl , refl , refl ← len∈-inversion Δ lenΔ∈ = dDel ∷ ΔΓDel , refl , refl , refl

∈⇒+-∈-++ : Ψ is-all-del →
           x ⦂[ m ] S ∈ Γ →
           -------------------------------
           length Ψ + x ⦂[ m ] S ∈ Ψ ++ Γ
∈⇒+-∈-++ []            x∈ = x∈
∈⇒+-∈-++ (eDel ∷ ΨDel) x∈ = there eDel (∈⇒+-∈-++ ΨDel x∈)

<∧∈-++⇒∈-++-++ : ∀ Δ →
                 Ψ is-all-del →
                 x ⦂[ m ] S ∈ Δ ++ Γ →
                 x ℕ.< length Δ →
                 -------------------------
                 x ⦂[ m ] S ∈ Δ ++ Ψ ++ Γ
<∧∈-++⇒∈-++-++ (_ ∷ Δ) ΨDel (here ΔΓDel)    x<       = here (All.++⁺ (All.++⁻ˡ Δ ΔΓDel) (All.++⁺ ΨDel (All.++⁻ʳ Δ ΔΓDel)))
<∧∈-++⇒∈-++-++ (e ∷ Δ) ΨDel (there eDel x∈) (s≤s x<) = there eDel (<∧∈-++⇒∈-++-++ Δ ΨDel x∈ x<)

≥∧∈-++⇒+-∈-++-++ : ∀ Δ →
                   Ψ is-all-del →
                   x ⦂[ m ] S ∈ Δ ++ Γ →
                   x ℕ.≥ length Δ →
                   ------------------------------------
                   length Ψ + x ⦂[ m ] S ∈ Δ ++ Ψ ++ Γ
≥∧∈-++⇒+-∈-++-++                     []      ΨDel x∈              x≥       = ∈⇒+-∈-++ ΨDel x∈
≥∧∈-++⇒+-∈-++-++ {Ψ = Ψ} {x = suc x} (e ∷ Δ) ΨDel (there eDel x∈) (s≤s x≥)
  rewrite ℕ.+-suc (length Ψ) x                                             = there eDel (≥∧∈-++⇒+-∈-++-++ Δ ΨDel x∈ x≥)

<∧∈-++-++⇒∈-++ : ∀ Δ Γ →
                 x ⦂[ m ] T ∈ Δ ++ Γ ++ Ψ →
                 x ℕ.< length Δ →
                 --------------------
                 x ⦂[ m ] T ∈ Δ ++ Ψ
<∧∈-++-++⇒∈-++ (_ ∷ Δ) Γ (here ΔΓΨDel)   x<       = here (All.++⁺ (All.++⁻ˡ Δ ΔΓΨDel) (All.++⁻ʳ Γ (All.++⁻ʳ Δ ΔΓΨDel)))
<∧∈-++-++⇒∈-++ (_ ∷ Δ) Γ (there dDel x∈) (s≤s x<) = there dDel (<∧∈-++-++⇒∈-++ Δ Γ x∈ x<)

≥∧∈-++⇒∈ : ∀ Δ →
           x ⦂[ m ] T ∈ Δ ++ Ψ →
           x ℕ.≥ length Δ →
           ----------------------------
           x ℕ.∸ length Δ ⦂[ m ] T ∈ Ψ
≥∧∈-++⇒∈ []      x∈           x≥       = x∈
≥∧∈-++⇒∈ (_ ∷ Δ) (there _ x∈) (s≤s x≥) = ≥∧∈-++⇒∈ Δ x∈ x≥

≥∧∈-++-++⇒∈-++ : ∀ Δ Γ →
                 x ⦂[ m ] T ∈ Δ ++ Γ ++ Ψ →
                 x ℕ.≥ length Δ + length Γ →
                 ---------------------------------
                 x ℕ.∸ length Γ ⦂[ m ] T ∈ Δ ++ Ψ
≥∧∈-++-++⇒∈-++ []      Γ x∈              x≥         = ≥∧∈-++⇒∈ Γ x∈ x≥
≥∧∈-++-++⇒∈-++ (_ ∷ Δ) Γ (there dDel x∈) (s≤s x≥)
  rewrite ℕ.+-∸-assoc 1 (ℕ.m+n≤o⇒n≤o (length Δ) x≥) = there dDel (≥∧∈-++-++⇒∈-++ Δ Γ x∈ x≥)

<∧∈-++⇒is-all-del : ∀ Δ →
                    x ⦂[ m ] T ∈ Δ ++ Ψ →
                    x ℕ.< length Δ →
                    ----------------------
                    Ψ is-all-del
<∧∈-++⇒is-all-del (_ ∷ Δ) (T.here ΔΨDel) x<       = All.++⁻ʳ Δ ΔΨDel
<∧∈-++⇒is-all-del (_ ∷ Δ) (T.there _ x∈) (s≤s x<) = <∧∈-++⇒is-all-del Δ x∈ x<

≥∧∈-++⇒is-all-del : ∀ Δ →
                    x ⦂[ m ] T ∈ Δ ++ Ψ →
                    x ℕ.≥ length Δ →
                    ----------------------
                    Δ is-all-del
≥∧∈-++⇒is-all-del []      x∈              x≥       = []
≥∧∈-++⇒is-all-del (_ ∷ Δ) (there dDel x∈) (s≤s x≥) = dDel ∷ ≥∧∈-++⇒is-all-del Δ x∈ x≥

~⊞-is-all-del∧∈⇒∈ʳ : Γ ~ Γ₀ ⊞ Γ₁ →
                     Γ₀ is-all-del →
                     x ⦂[ m ] S ∈ Γ₁ →
                     ------------------
                     x ⦂[ m ] S ∈ Γ
~⊞-is-all-del∧∈⇒∈ʳ (d~               ∷ Γ~) (d₀Del ∷ Γ₀Del) (there d₁Del x∈) = there (~d⊞⁻¹-preserves-is-del d₀Del d₁Del d~) (~⊞-is-all-del∧∈⇒∈ʳ Γ~ Γ₀Del x∈)
~⊞-is-all-del∧∈⇒∈ʳ (contraction Co∈m ∷ Γ~) (d₀Del ∷ Γ₀Del) (here Γ₁Del)     = here (~⊞⁻¹-preserves-is-all-del Γ₀Del Γ₁Del Γ~)
~⊞-is-all-del∧∈⇒∈ʳ (to-right         ∷ Γ~) (d₀Del ∷ Γ₀Del) (here Γ₁Del)     = here (~⊞⁻¹-preserves-is-all-del Γ₀Del Γ₁Del Γ~)

~⊞-is-all-del∧∈⇒∈ˡ : Γ ~ Γ₀ ⊞ Γ₁ →
                     Γ₁ is-all-del →
                     x ⦂[ m ] S ∈ Γ₀ →
                     ------------------
                     x ⦂[ m ] S ∈ Γ
~⊞-is-all-del∧∈⇒∈ˡ Γ~ Γ₁Del x∈ = ~⊞-is-all-del∧∈⇒∈ʳ (~⊞-commute Γ~) Γ₁Del x∈

∤⁻¹-preserves-∈ : ∀ Δ →
                  x ⦂[ m ] S ∈ Δ ++ Γ′ →
                  Γ ∤[ m₀ ] Γ′ →
                  -----------------------
                  x ⦂[ m ] S ∈ Δ ++ Γ
∤⁻¹-preserves-∈ []      (here Γ′Del)    (keep _ ∷ Γ∤) = here (∤⁻¹-preserves-is-all-del Γ′Del Γ∤)
∤⁻¹-preserves-∈ []      (there dDel x∈) (d∤ ∷ Γ∤)     = there (∤d⁻¹-preserves-is-del dDel d∤) (∤⁻¹-preserves-∈ [] x∈ Γ∤)
∤⁻¹-preserves-∈ (_ ∷ Δ) (here ΔΓ′Del)   Γ∤            = here (All.++⁺ (All.++⁻ˡ Δ ΔΓ′Del) (∤⁻¹-preserves-is-all-del (All.++⁻ʳ Δ ΔΓ′Del) Γ∤))
∤⁻¹-preserves-∈ (_ ∷ Δ) (there dDel x∈) Γ∤            = there dDel (∤⁻¹-preserves-∈ Δ x∈ Γ∤)

⊢d∧<ₘ⇒⊢d : [ m₀ ]⊢[ m ]d d →
           m′ <ₘ m →
           ------------------
           [ m₀ ]⊢[ m′ ]d d
⊢d∧<ₘ⇒⊢d (valid m≤) <m = valid (≤ₘ-trans (<ₘ⇒≤ₘ <m) m≤)
⊢d∧<ₘ⇒⊢d unusable   <m = unusable

⊢∧<ₘ⇒⊢ : ⊢[ m ] Γ →
         m₀ <ₘ m →
         -----------
         ⊢[ m₀ ] Γ
⊢∧<ₘ⇒⊢ []               <m = []
⊢∧<ₘ⇒⊢ ((⊢S , ⊢d) ∷ ⊢Γ) <m = (⊢S , ⊢d∧<ₘ⇒⊢d ⊢d <m) ∷ ⊢∧<ₘ⇒⊢ ⊢Γ <m

⊢d∧Wk≤⇒is-del : [ m₀ ]⊢[ m ]d d →
                m′ ≤ₘ m →
                Bool.T (stₘ m′ ``Wk) →
                -----------------------
                d [ m₀ ]is-del
⊢d∧Wk≤⇒is-del (valid m≤) m′≤ Wk∈m′ = weakening (isWellStructuredₘ _ _ ``Wk m≤ (isWellStructuredₘ _ _ ``Wk m′≤ Wk∈m′))
⊢d∧Wk≤⇒is-del unusable   m′≤ Wk∈m′ = unusable

⊢∧Wk≤⇒is-all-del : ⊢[ m ] Γ →
                   m′ ≤ₘ m →
                   Bool.T (stₘ m′ ``Wk) →
                   -----------------------
                   Γ is-all-del
⊢∧Wk≤⇒is-all-del []               m′≤ Wk∈m′ = []
⊢∧Wk≤⇒is-all-del ((⊢S , ⊢d) ∷ ⊢Γ) m′≤ Wk∈m′ = ⊢d∧Wk≤⇒is-del ⊢d m′≤ Wk∈m′ ∷ ⊢∧Wk≤⇒is-all-del ⊢Γ m′≤ Wk∈m′

⊢d∧-~d⊞-⇒⊢d : [ m₀ ]⊢[ m ]d dS →
              dS [ m₀ ]~d dS₀ ⊞ dS₁ →
              --------------------------------------
              [ m₀ ]⊢[ m ]d dS₀ × [ m₀ ]⊢[ m ]d dS₁
⊢d∧-~d⊞-⇒⊢d ⊢d         (contraction Co∈m₀) = ⊢d , ⊢d
⊢d∧-~d⊞-⇒⊢d (valid m≤) to-left             = valid m≤ , unusable
⊢d∧-~d⊞-⇒⊢d (valid m≤) to-right            = unusable , valid m≤
⊢d∧-~d⊞-⇒⊢d ⊢d         unusable            = ⊢d , ⊢d

⊢∧-~⊞-⇒⊢ : ⊢[ m ] Γ →
           Γ ~ Γ₀ ⊞ Γ₁ →
           ----------------------
           ⊢[ m ] Γ₀ × ⊢[ m ] Γ₁
⊢∧-~⊞-⇒⊢ []        []        = [] , []
⊢∧-~⊞-⇒⊢ ((⊢S , ⊢d) ∷ ⊢Γ) (d~ ∷ Γ~)
  with ⊢d₀ , ⊢d₁ ← ⊢d∧-~d⊞-⇒⊢d ⊢d d~
     | ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~    = (⊢S , ⊢d₀) ∷ ⊢Γ₀ , (⊢S , ⊢d₁) ∷ ⊢Γ₁

⊢∧-~⊞-⇒⊢ˡ : ⊢[ m ] Γ →
            Γ ~ Γ₀ ⊞ Γ₁ →
            --------------
            ⊢[ m ] Γ₀
⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~ = proj₁ (⊢∧-~⊞-⇒⊢ ⊢Γ Γ~)

⊢∧-~⊞-⇒⊢ʳ : ⊢[ m ] Γ →
            Γ ~ Γ₀ ⊞ Γ₁ →
            --------------
            ⊢[ m ] Γ₁
⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~ = proj₂ (⊢∧-~⊞-⇒⊢ ⊢Γ Γ~)

~⊞-is-all-del∧⊢⇒⊢ʳ : Γ ~ Γ₀ ⊞ Γ₁ →
                     Γ₀ is-all-del →
                     Γ₁ ⊢[ m ] L ⦂ S →
                     ------------------
                     Γ ⊢[ m ] L ⦂ S

~⊞-is-all-del∧⊢⇒⊢ʳ                           Γ~ Γ₀Del (`unit Γ₁Del)                          = `unit ΓDel
  where
    ΓDel = ~⊞⁻¹-preserves-is-all-del Γ₀Del Γ₁Del Γ~

~⊞-is-all-del∧⊢⇒⊢ʳ                           Γ~ Γ₀Del (`λ⦂-∘ ⊢L)                             = `λ⦂-∘ ⊢L′
  where
    ⊢L′ = ~⊞-is-all-del∧⊢⇒⊢ʳ (to-right ∷ Γ~) (unusable ∷ Γ₀Del) ⊢L

~⊞-is-all-del∧⊢⇒⊢ʳ                           Γ~ Γ₀Del (Γ₁~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with _ , Γ₁′~ , Γ~′ ← ~⊞-assocʳ Γ~ Γ₁~                                                     = Γ~′ ⊢ ⊢L′ ⦂ ⊢⊸ `$ ⊢M
  where
    ⊢L′ = ~⊞-is-all-del∧⊢⇒⊢ʳ Γ₁′~ Γ₀Del ⊢L

~⊞-is-all-del∧⊢⇒⊢ʳ                           Γ~ Γ₀Del (`lift[-⇒-] ⊢L)                        = `lift[-⇒-] ⊢L′
  where
    ⊢L′ = ~⊞-is-all-del∧⊢⇒⊢ʳ Γ~ Γ₀Del ⊢L

~⊞-is-all-del∧⊢⇒⊢ʳ {L = `unlift[ m₀ ⇒ _ ] L} Γ~ Γ₀Del (Γ₁∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)
  with _ , Γ₀∤ , Γ₀′Del ← is-all-del⇒∤ m₀ Γ₀Del
    with _ , Γ∤ , Γ′~ ← ~⊞⁻¹-preserves-∤ Γ₀∤ Γ₁∤ Γ~                                          = Γ∤ ⊢`unlift[-⇒-] ⊢L′ ⦂ ⊢↑
  where
    ⊢L′ = ~⊞-is-all-del∧⊢⇒⊢ʳ Γ′~ Γ₀′Del ⊢L

~⊞-is-all-del∧⊢⇒⊢ʳ {L = `return[ m₀ ⇒ _ ] L} Γ~ Γ₀Del (Γ₁∤ ⊢`return[-⇒-] ⊢L)
  with _ , Γ₀∤ , Γ₀′Del ← is-all-del⇒∤ m₀ Γ₀Del
    with _ , Γ∤ , Γ′~ ← ~⊞⁻¹-preserves-∤ Γ₀∤ Γ₁∤ Γ~                                          = Γ∤ ⊢`return[-⇒-] ⊢L′
  where
    ⊢L′ = ~⊞-is-all-del∧⊢⇒⊢ʳ Γ′~ Γ₀′Del ⊢L

~⊞-is-all-del∧⊢⇒⊢ʳ                           Γ~ Γ₀Del (Γ₁~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M)
  with _ , Γ₁′~ , Γ~′ ← ~⊞-assocʳ Γ~ Γ₁~                                                     = Γ~′ ⊢`let-return[-⇒-] ⊢L′ ⦂ ⊢↓ `in ⊢M
  where
    ⊢L′ = ~⊞-is-all-del∧⊢⇒⊢ʳ Γ₁′~ Γ₀Del ⊢L

~⊞-is-all-del∧⊢⇒⊢ʳ                           Γ~ Γ₀Del (`# x∈)                                = `# x∈′
  where
    x∈′ = ~⊞-is-all-del∧∈⇒∈ʳ Γ~ Γ₀Del x∈

~⊞-is-all-del∧⊢⇒⊢ˡ : Γ ~ Γ₀ ⊞ Γ₁ →
                     Γ₁ is-all-del →
                     Γ₀ ⊢[ m ] L ⦂ S →
                     ------------------
                     Γ ⊢[ m ] L ⦂ S
~⊞-is-all-del∧⊢⇒⊢ˡ Γ~ Γ₁Del ⊢L = ~⊞-is-all-del∧⊢⇒⊢ʳ (~⊞-commute Γ~) Γ₁Del ⊢L

⊢d∧∤d⇒⊢d : [ m₀ ]⊢[ m ]d d →
           d [ m₀ ]∤[ m′ ]d d′ →
           ----------------------
           [ m₀ ]⊢[ m′ ]d d′
⊢d∧∤d⇒⊢d ⊢d         (delete m′≰ dDel) = unusable
⊢d∧∤d⇒⊢d (valid m≤) (keep m′≤)        = valid m′≤
⊢d∧∤d⇒⊢d (unusable) (keep m′≤)        = unusable

⊢∧∤⇒⊢ : ⊢[ m ] Γ →
        Γ ∤[ m₀ ] Γ′ →
        ----------------
        ⊢[ m₀ ] Γ′
⊢∧∤⇒⊢ []        []        = []
⊢∧∤⇒⊢ ((⊢S , ⊢d) ∷ ⊢Γ) (d∤ ∷ Γ∤) = (⊢S , ⊢d∧∤d⇒⊢d ⊢d d∤) ∷ ⊢∧∤⇒⊢ ⊢Γ Γ∤

⊢d∧≤⇒∤d : [ m₀ ]⊢[ m ]d d →
          m′ ≤ₘ m →
          -------------------
          d [ m₀ ]∤[ m′ ]d d
⊢d∧≤⇒∤d                (valid m≤) ≤m = keep (≤ₘ-trans ≤m m≤)
⊢d∧≤⇒∤d {m₀} {m′ = m′} unusable   ≤m
  with m′ ≤?ₘ m₀
...  | no  m′≰ = delete m′≰ unusable
...  | yes m′≤ = keep m′≤

⊢∧≤⇒∤ : ⊢[ m ] Γ →
        m′ ≤ₘ m →
        ------------
        Γ ∤[ m′ ] Γ
⊢∧≤⇒∤ []               ≤m = []
⊢∧≤⇒∤ ((⊢S , ⊢d) ∷ ⊢Γ) ≤m = ⊢d∧≤⇒∤d ⊢d ≤m ∷ ⊢∧≤⇒∤ ⊢Γ ≤m

∤⁻¹-preserves-⊢ : ∀ Δ →
                  Δ ++ Γ′ ⊢[ m ] L ⦂ S →
                  Γ ∤[ m₀ ] Γ′ →
                  -----------------------
                  Δ ++ Γ ⊢[ m ] L ⦂ S

∤⁻¹-preserves-⊢ Δ (`unit ΔΓ′Del)                          Γ∤ = `unit ΔΓDel
  where
    ΔΓDel = All.++⁺ (All.++⁻ˡ Δ ΔΓ′Del) (∤⁻¹-preserves-is-all-del (All.++⁻ʳ Δ ΔΓ′Del) Γ∤)

∤⁻¹-preserves-⊢ Δ (`λ⦂-∘ ⊢L)                              Γ∤ = `λ⦂-∘ ⊢L′
  where
    ⊢L′ = ∤⁻¹-preserves-⊢ (_ ∷ Δ) ⊢L Γ∤

∤⁻¹-preserves-⊢ Δ (ΔΓ′~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                  Γ∤
  with _ , _ , _ , _ , refl , refl , Δ~ , Γ′~ ← ~⊞-preserves-++ Δ ΔΓ′~
    with _ , _ , Γ~ , Γ₀∤ , Γ₁∤ ← ∤⁻¹-preserves-~⊞ Γ′~ Γ∤    = ΔΓ~ ⊢ ⊢L′ ⦂ ⊢⊸ `$ ⊢M′
  where
    ΔΓ~ = ~⊞-++⁺ Δ~ Γ~
    ⊢L′ = ∤⁻¹-preserves-⊢ _ ⊢L Γ₀∤
    ⊢M′ = ∤⁻¹-preserves-⊢ _ ⊢M Γ₁∤

∤⁻¹-preserves-⊢ Δ (`lift[-⇒-] ⊢L)                         Γ∤ = `lift[-⇒-] ⊢L′
  where
    ⊢L′ = ∤⁻¹-preserves-⊢ Δ ⊢L Γ∤

∤⁻¹-preserves-⊢ Δ (ΔΓ′∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)            Γ∤
  with _ , _ , refl , Δ∤ , Γ′∤ ← ∤-preserves-++ Δ ΔΓ′∤
    with _ , Γ∤′ , ∤Γ″ ← assoc-∤ Γ∤ Γ′∤                      = ΔΓ∤ ⊢`unlift[-⇒-] ⊢L′ ⦂ ⊢↑
  where
    ΔΓ∤ = ∤-++⁺ Δ∤ Γ∤′
    ⊢L′ = ∤⁻¹-preserves-⊢ _ ⊢L ∤Γ″

∤⁻¹-preserves-⊢ Δ (ΔΓ′∤ ⊢`return[-⇒-] ⊢L)                 Γ∤
  with _ , _ , refl , Δ∤ , Γ′∤ ← ∤-preserves-++ Δ ΔΓ′∤
    with _ , Γ∤′ , ∤Γ″ ← assoc-∤ Γ∤ Γ′∤                      = ΔΓ∤ ⊢`return[-⇒-] ⊢L′
  where
    ΔΓ∤ = ∤-++⁺ Δ∤ Γ∤′
    ⊢L′ = ∤⁻¹-preserves-⊢ _ ⊢L ∤Γ″

∤⁻¹-preserves-⊢ Δ (ΔΓ′~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) Γ∤
  with _ , _ , _ , _ , refl , refl , Δ~ , Γ′~ ← ~⊞-preserves-++ Δ ΔΓ′~
    with _ , _ , Γ~ , Γ₀∤ , Γ₁∤ ← ∤⁻¹-preserves-~⊞ Γ′~ Γ∤    = ΔΓ~ ⊢`let-return[-⇒-] ⊢L′ ⦂ ⊢↓ `in ⊢M′
  where
    ΔΓ~ = ~⊞-++⁺ Δ~ Γ~
    ⊢L′ = ∤⁻¹-preserves-⊢ _ ⊢L Γ₀∤
    ⊢M′ = ∤⁻¹-preserves-⊢ _ ⊢M Γ₁∤

∤⁻¹-preserves-⊢ Δ (`# x∈)                                 Γ∤ = `# x∈′
  where
    x∈′ = ∤⁻¹-preserves-∈ Δ x∈ Γ∤
