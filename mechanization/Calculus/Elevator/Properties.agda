------------------------------------------------------------
-- Main Properties of Elevator
------------------------------------------------------------
--
-- This module includes the proof for the type safety of Elevator.
--

{-# OPTIONS --safe #-}
open import Calculus.Elevator.ModeSpec

module Calculus.Elevator.Properties {ℓ₁ ℓ₂} (ℳ : ModeSpec ℓ₁ ℓ₂) where
open ModeSpec ℳ

open import Data.Bool as Bool using (true; false)
open import Data.List as List using ([]; _∷_; _++_; length)
import Data.List.Properties as List
open import Data.List.Relation.Unary.All as All using ([]; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.Nat as ℕ using (suc; s≤s)
import Data.Nat.Induction as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product as × using (_,_; proj₁; proj₂; ∃; ∃₂; _×_; -,_)
open import Data.Sum as ⊎ using (_⊎_; inj₁; inj₂)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (dec-yes; dec-no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂; ≢-sym)

import Calculus.Elevator.Syntax as S
import Calculus.Elevator.Typing as T
import Calculus.Elevator.Typing.Properties as TP
import Calculus.Elevator.OpSem as O
import Calculus.Elevator.OpSem.Properties as OP
open S ℳ
open T ℳ
open TP ℳ
open O ℳ
open OP ℳ

-- Weakening property
--
subst-wk[-↑-] : x ≡ x′ →
                k ≡ k′ →
                ∀ L →
                Γ ⊢[ m ] wk[ x ↑ k ] L ⦂ S →
                -----------------------------
                Γ ⊢[ m ] wk[ x′ ↑ k′ ] L ⦂ S
subst-wk[-↑-] {Γ = Γ} {m} {S} eq₀ eq₁ L = subst₂ (λ x k → Γ ⊢[ m ] wk[ x ↑ k ] L ⦂ S) eq₀ eq₁

-- Weakening gives a well-typed result
⊢wk[-↑-] : ∀ Δ →
           Γ′ is-all-del →
           Δ ++ Γ ⊢[ m ] L ⦂ S →
           -----------------------------------------------------
           Δ ++ Γ′ ++ Γ ⊢[ m ] wk[ length Γ′ ↑ length Δ ] L ⦂ S

⊢wk[-↑-]                                         Δ Γ′Del (`unit ΔΓDel)                           = `unit ΔΓ′ΓDel
  where
    ΔΓ′ΓDel = All.++⁺ (All.++⁻ˡ Δ ΔΓDel) (All.++⁺ Γ′Del (All.++⁻ʳ Δ ΔΓDel))

⊢wk[-↑-]                                         Δ Γ′Del (`λ⦂-∘ ⊢L)                              = `λ⦂-∘ ⊢L′
  where
    ⊢L′ = ⊢wk[-↑-] (_ ∷ Δ) Γ′Del ⊢L

⊢wk[-↑-] {Γ′} {L = L `$ M}                        Δ Γ′Del (ΔΓ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with Δ₀ , Δ₁ , _ , _ , refl , refl , Δ~ , Γ~ ← ~⊞-preserves-++ Δ ΔΓ~
     | _ , Γ′~ ← left-bias-~⊞ Γ′
    with _    , Γ′₁Del ← ~⊞-preserves-is-all-del Γ′Del Γ′~
       | eqΔ₀ , eqΔ₁ ← length-respects-~⊞ Δ~                                                     = ΔΓ′Γ~ ⊢ ⊢L′ ⦂ ⊢⊸ `$ ⊢M′
  where
    ΔΓ′Γ~ = ~⊞-++⁺ Δ~ (~⊞-++⁺ Γ′~ Γ~)
    ⊢L′ =
      subst-wk[-↑-] refl eqΔ₀ L
        (⊢wk[-↑-] Δ₀ Γ′Del ⊢L)
    ⊢M′ =
      subst-wk[-↑-] (proj₂ (length-respects-~⊞ Γ′~)) eqΔ₁ M
        (⊢wk[-↑-] Δ₁ Γ′₁Del ⊢M)

⊢wk[-↑-]                                         Δ Γ′Del (`lift[-⇒-] ⊢L)                         = `lift[-⇒-] ⊢L′
  where
    ⊢L′ = ⊢wk[-↑-] Δ Γ′Del ⊢L

⊢wk[-↑-]     {L = `unlift[ m₀ ⇒ _ ] L}           Δ Γ′Del (ΔΓ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)
  with Δ′ , _ , refl , Δ∤ , Γ∤ ← ∤-preserves-++ Δ ΔΓ∤
     | _ , Γ′∤ , _ ← is-all-del⇒∤ m₀ Γ′Del                                                       = ΔΓ′Γ∤ ⊢`unlift[-⇒-] ⊢L′ ⦂ ⊢↑
  where
    ΔΓ′Γ∤ = ∤-++⁺ Δ∤ (∤-++⁺ Γ′∤ Γ∤)
    ⊢L′ =
      subst-wk[-↑-] (length-respects-∤ Γ′∤) (length-respects-∤ Δ∤) L
        (⊢wk[-↑-] Δ′ (∤-preserves-is-all-del Γ′Del Γ′∤) ⊢L)

⊢wk[-↑-]     {L = `return[ m₀ ⇒ _ ] L}           Δ Γ′Del (ΔΓ∤ ⊢`return[-⇒-] ⊢L)
  with Δ′ , _ , refl , Δ∤ , Γ∤ ← ∤-preserves-++ Δ ΔΓ∤
     | _ , Γ′∤ , _ ← is-all-del⇒∤ m₀ Γ′Del                                                       = ΔΓ′Γ∤ ⊢`return[-⇒-] ⊢L′
  where
    ΔΓ′Γ∤ = ∤-++⁺ Δ∤ (∤-++⁺ Γ′∤ Γ∤)
    ⊢L′ =
      subst-wk[-↑-] (length-respects-∤ Γ′∤) (length-respects-∤ Δ∤) L
        (⊢wk[-↑-] Δ′ (∤-preserves-is-all-del Γ′Del Γ′∤) ⊢L)

⊢wk[-↑-] {Γ′} {L = `let-return[ m₁ ⇒ _ ] L `in M} Δ Γ′Del (ΔΓ~ & Δ₀Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢L ⦂ ⊢↓ `in ⊢M)
  with Δ₀ , Δ₁ , Γ₀ , Γ₁ , refl , refl , Δ~ , Γ~ ← ~⊞-preserves-++ Δ ΔΓ~
     | Γ′₁ , Γ′~ ← left-bias-~⊞ Γ′
    with Δ₀′ , _ , refl , Δ₀∤ , Γ₀∤ ← ∤-preserves-++ Δ₀ Δ₀Γ₀∤
       | _ , Γ′∤ , Γ″Del ← is-all-del⇒∤ m₁ Γ′Del
       | _    , Γ′₁Del ← ~⊞-preserves-is-all-del Γ′Del Γ′~
       | eqΔ₀ , eqΔ₁ ← length-respects-~⊞ Δ~                                                     = ΔΓ′Γ~ & Δ₀Γ′Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢L′ ⦂ ⊢↓ `in ⊢M′
  where
    ΔΓ′Γ~ = ~⊞-++⁺ Δ~ (~⊞-++⁺ Γ′~ Γ~)
    Δ₀Γ′Γ₀∤ = ∤-++⁺ Δ₀∤ (∤-++⁺ Γ′∤ Γ₀∤)
    ⊢L′ =
      subst-wk[-↑-] (length-respects-∤ Γ′∤) (trans (length-respects-∤ Δ₀∤) eqΔ₀) L
        (⊢wk[-↑-] Δ₀′ Γ″Del ⊢L)
    ⊢M′ =
      subst-wk[-↑-] (proj₂ (length-respects-~⊞ Γ′~)) (cong suc eqΔ₁) M
        (⊢wk[-↑-] (_ ∷ Δ₁) Γ′₁Del ⊢M)

⊢wk[-↑-]                                         Δ Γ′Del (`#_ {x = x} x∈)
  with x ℕ.≥? length Δ
...  | yes x≥                                                                                    = `# ≥∧∈-++⇒+-∈-++-++ Δ Γ′Del x∈ x≥
...  | no  x≱                                                                                    = `# <∧∈-++⇒∈-++-++ Δ Γ′Del x∈ (ℕ.≰⇒> x≱)

-- Substitution property
--
subst-[/-] : x ≡ x′ →
             ∀ M →
             Γ ⊢[ m ] [ L /[ m₀ ] x ] M ⦂ T →
             ---------------------------------
             Γ ⊢[ m ] [ L /[ m₀ ] x′ ] M ⦂ T
subst-[/-] {Γ = Γ} {m} {L} {m₀} {T} eq M = subst (λ x → Γ ⊢[ m ] [ L /[ m₀ ] x ] M ⦂ T) eq

-- Substitution of an unused variable is strengthening
false⊢[/] : ∀ Δ₀ →
            Δ₀ ++ (S , m₀ , false) ∷ Δ′ ⊢[ m ] M ⦂ T →
            ----------------------------------------------
            Δ₀ ++ Δ′ ⊢[ m ] [ L /[ m₀ ] length Δ₀ ] M ⦂ T

false⊢[/]                                     Δ₀ (`unit Δ₀dΔ′Del)
  with Δ₀Del , _ ∷ Δ′Del ← All.++⁻ Δ₀ Δ₀dΔ′Del                                               = `unit Δ₀Δ′Del
  where
    Δ₀Δ′Del = All.++⁺ Δ₀Del Δ′Del

false⊢[/]                                     Δ₀ (`λ⦂-∘ ⊢M)                                  = `λ⦂-∘ ⊢M′
  where
    ⊢M′ = false⊢[/] (_ ∷ Δ₀) ⊢M

false⊢[/] {M = M `$ N}                        Δ₀ (Δ₀dΔ′~ ⊢ ⊢M ⦂ ⊢⊸ `$ ⊢N)
  with ⊢S `⊸[ _ ] _ ← ⊢⊸
     | Δ₀₀ , Δ₀₁ , _ ∷ Δ′₀ , _ ∷ Δ′₁ , refl , refl , Δ₀~ , unusable ∷ Δ′~ ← ~⊞-preserves-++ Δ₀ Δ₀dΔ′~
    with eqΔ₀₀ , eqΔ₀₁ ← length-respects-~⊞ Δ₀~                                              = Δ₀Δ′~ ⊢ ⊢M′ ⦂ ⊢⊸ `$ ⊢N′
  where
    Δ₀Δ′~ = ~⊞-++⁺ Δ₀~ Δ′~
    ⊢M′ = subst-[/-] eqΔ₀₀ M (false⊢[/] Δ₀₀ ⊢M)
    ⊢N′ = subst-[/-] eqΔ₀₁ N (false⊢[/] Δ₀₁ ⊢N)

false⊢[/]                                     Δ₀ (`lift[-⇒-] ⊢M)                             = `lift[-⇒-] ⊢M′
  where
    ⊢M′ = false⊢[/] Δ₀ ⊢M

false⊢[/] {M = `unlift[ _ ⇒ _ ] M}            Δ₀ (Δ₀dΔ′∤ ⊢`unlift[-⇒-] ⊢M ⦂ ⊢↑)
  with _ , _ ∷ _ , refl , Δ₀∤ , d∤ ∷ Δ′∤ ← ∤-preserves-++ Δ₀ Δ₀dΔ′∤
    with Δ₀Δ′∤ ← ∤-++⁺ Δ₀∤ Δ′∤
       | eqΔ₀ ← length-respects-∤ Δ₀∤
      with d∤
...      | keep m₁≤
        rewrite proj₂ (dec-yes (_ ≤?ₘ _) m₁≤)
          with ⊢M′ ← subst-[/-] eqΔ₀ M (false⊢[/] _ ⊢M)                                      = Δ₀Δ′∤ ⊢`unlift[-⇒-] ⊢M′ ⦂ ⊢↑
...      | delete m₁≰ dDel
        rewrite dec-no (_ ≤?ₘ _) m₁≰
          with ⊢M′ ← subst-[/-] eqΔ₀ M (false⊢[/] _ ⊢M)                                      = Δ₀Δ′∤ ⊢`unlift[-⇒-] ⊢M′ ⦂ ⊢↑

false⊢[/] {M = `return[ _ ⇒ _ ] M}            Δ₀ (Δ₀dΔ′∤ ⊢`return[-⇒-] ⊢M)
  with _ , _ , refl , Δ₀∤ , d∤ ∷ Δ′∤ ← ∤-preserves-++ Δ₀ Δ₀dΔ′∤
    with Δ₀Δ′∤ ← ∤-++⁺ Δ₀∤ Δ′∤
       | eqΔ₀ ← length-respects-∤ Δ₀∤
      with d∤
...      | keep m₁≤
        rewrite proj₂ (dec-yes (_ ≤?ₘ _) m₁≤)
          with ⊢M′ ← subst-[/-] eqΔ₀ M (false⊢[/] _ ⊢M)                                      = Δ₀Δ′∤ ⊢`return[-⇒-] ⊢M′
...      | delete m₁≰ dDel
        rewrite dec-no (_ ≤?ₘ _) m₁≰
          with ⊢M′ ← subst-[/-] eqΔ₀ M (false⊢[/] _ ⊢M)                                      = Δ₀Δ′∤ ⊢`return[-⇒-] ⊢M′

false⊢[/] {M = `let-return[ m₁ ⇒ _ ] M `in N} Δ₀ (Δ₀dΔ′~ & Δ₀₀d₀Δ′₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢M ⦂ ⊢↓ `in ⊢N)
  with Δ₀₀ , Δ₀₁ , _ ∷ Δ′₀ , _ ∷ Δ′₁ , refl , refl , Δ₀~ , unusable ∷ Δ′~ ← ~⊞-preserves-++ Δ₀ Δ₀dΔ′~
    with Δ₀Δ′~ ← ~⊞-++⁺ Δ₀~ Δ′~
       | Δ₀₀′ , _ ∷ _ , refl , Δ₀₀∤ , d₀∤ ∷ Δ′₀∤ ← ∤-preserves-++ Δ₀₀ Δ₀₀d₀Δ′₀∤
       | eqΔ₀₀ , eqΔ₀₁ ← length-respects-~⊞ Δ₀~
      with Δ₀₀Δ′₀∤ ← ∤-++⁺ Δ₀₀∤ Δ′₀∤
      with d₀∤
...      | keep m₁≤
        rewrite proj₂ (dec-yes (_ ≤?ₘ _) m₁≤)
          with ⊢M′ ← subst-[/-] (trans (length-respects-∤ Δ₀₀∤) eqΔ₀₀) M (false⊢[/] Δ₀₀′ ⊢M)
             | ⊢N′ ← subst-[/-] (cong suc eqΔ₀₁) N (false⊢[/] (_ ∷ Δ₀₁) ⊢N)                  = Δ₀Δ′~ & Δ₀₀Δ′₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢M′ ⦂ ⊢↓ `in ⊢N′
...      | delete m₁≰ d₀Del
        rewrite dec-no (_ ≤?ₘ _) m₁≰
          with ⊢M′ ← subst-[/-] (trans (length-respects-∤ Δ₀₀∤) eqΔ₀₀) M (false⊢[/] Δ₀₀′ ⊢M)
             | ⊢N′ ← subst-[/-] (cong suc eqΔ₀₁) N (false⊢[/] (_ ∷ Δ₀₁) ⊢N)                  = Δ₀Δ′~ & Δ₀₀Δ′₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢M′ ⦂ ⊢↓ `in ⊢N′

false⊢[/]                                     Δ₀ (`#_ {x = y} y∈)
  with y ℕ.≥? length Δ₀
...  | no  y≱
    with y∈′ ← <∧∈-++-++⇒∈-++ Δ₀ (_ ∷ []) y∈ (ℕ.≰⇒> y≱)                                      = `# y∈′
...  | yes y≥
    with y ℕ.≟ length Δ₀
...    | yes refl with _ , _ , _ , () ← len∈-inversion Δ₀ y∈
...    | no  y≢
    with y> ← subst (y ℕ.≥_) (ℕ.+-comm 1 _) (ℕ.≤∧≢⇒< y≥ (≢-sym y≢))
      with y∈′ ← ≥∧∈-++-++⇒∈-++ Δ₀ (_ ∷ []) y∈ y>                                            = `# y∈′

-- Substitution of a used variable gives a well-typed result
true⊢[/]ʳ : ∀ Δ₀ →
            Γ ~ Δ₀ ++ Δ′ ⊞ Γ₁ →
            ⊢[ m₀ ] Γ₁ →
            Γ₁ ⊢[ m₀ ] L ⦂ S →
            ⊢[ m ] T ⦂⋆ →
            Δ₀ ++ (S , m₀ , true) ∷ Δ′ ⊢[ m ] M ⦂ T →
            ------------------------------------------
            Γ ⊢[ m ] [ L /[ m₀ ] length Δ₀ ] M ⦂ T
true⊢[/]ˡ : ∀ Δ₁ →
            Γ ~ Γ₀ ⊞ Δ₁ ++ Δ′ →
            ⊢[ m₀ ] Γ₀ →
            Γ₀ ⊢[ m₀ ] L ⦂ S →
            ⊢[ m ] T ⦂⋆ →
            Δ₁ ++ (S , m₀ , true) ∷ Δ′ ⊢[ m ] M ⦂ T →
            ------------------------------------------
            Γ ⊢[ m ] [ L /[ m₀ ] length Δ₁ ] M ⦂ T

true⊢[/]ʳ                                    Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T                  (`unit Δ₀dΔ′Del)
  with Δ₀Del , weakening Wk∈m₀ ∷ Δ′Del ← All.++⁻ Δ₀ Δ₀dΔ′Del                                                            = `unit ΓDel
  where
    ΓDel = ~⊞⁻¹-preserves-is-all-del (All.++⁺ Δ₀Del Δ′Del) (⊢∧Wk≤⇒is-all-del ⊢Γ₁ ≤ₘ-refl Wk∈m₀) Γ~

true⊢[/]ʳ                                    Δ₀ Γ~ ⊢Γ₁ ⊢L (⊢T₀ `⊸[ _ ] ⊢T₁)   (`λ⦂-∘ ⊢M)                                = `λ⦂-∘ ⊢M′
  where
    ⊢M′ = true⊢[/]ʳ (_ ∷ Δ₀) (to-left ∷ Γ~) ((⊢T₀ , unusable) ∷ ⊢Γ₁) (⊢wk[-↑-] [] (unusable ∷ []) ⊢L) ⊢T₁ ⊢M

true⊢[/]ʳ {M = M `$ N}                       Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T (Δ₀dΔ′~ ⊢ ⊢M ⦂ ⊢⊸ `$ ⊢N)
  with ⊢T₀ `⊸[ _ ] _ ← ⊢⊸
     | _ , _ , _ , _ , refl , refl , Δ₀~ , d~ ∷ Δ′~ ← ~⊞-preserves-++ Δ₀ Δ₀dΔ′~
    with Δ₀Δ′~ ← ~⊞-++⁺ Δ₀~ Δ′~
       | eqΔ₀₀ , eqΔ₀₁ ← length-respects-~⊞ Δ₀~
      with d~
...      | contraction Co∈m₀
        with _ , _ , Γ₂′~ , Γ₃′~ , Γ~′ ← ~⊞-contraction-assocˡ Γ~ Δ₀Δ′~ ⊢Γ₁ Co∈m₀
          with ⊢M′ ← subst-[/-] eqΔ₀₀ M (true⊢[/]ʳ _ Γ₂′~ ⊢Γ₁ ⊢L ⊢⊸ ⊢M)
             | ⊢N′ ← subst-[/-] eqΔ₀₁ N (true⊢[/]ʳ _ Γ₃′~ ⊢Γ₁ ⊢L ⊢T₀ ⊢N)                                                = Γ~′ ⊢ ⊢M′ ⦂ ⊢⊸ `$ ⊢N′
...      | to-left
        with _ , Γ₁′~ , Γ~′ ← ~⊞-assocʳ (~⊞-commute Γ~) Δ₀Δ′~
          with ⊢M′ ← subst-[/-] eqΔ₀₀ M (true⊢[/]ˡ _ Γ₁′~ ⊢Γ₁ ⊢L ⊢⊸ ⊢M)
             | ⊢N′ ← subst-[/-] eqΔ₀₁ N (false⊢[/] _ ⊢N)                                                                = Γ~′ ⊢ ⊢M′ ⦂ ⊢⊸ `$ ⊢N′
...      | to-right
        with _ , Γ₁′~ , Γ~′ ← ~⊞-assocˡ Γ~ Δ₀Δ′~
          with ⊢M′ ← subst-[/-] eqΔ₀₀ M (false⊢[/] _ ⊢M)
             | ⊢N′ ← subst-[/-] eqΔ₀₁ N (true⊢[/]ʳ _ Γ₁′~ ⊢Γ₁ ⊢L ⊢T₀ ⊢N)                                                = Γ~′ ⊢ ⊢M′ ⦂ ⊢⊸ `$ ⊢N′

true⊢[/]ʳ                                    Δ₀ Γ~ ⊢Γ₁ ⊢L (`↑[-⇒ _ ][ _ ] ⊢T) (`lift[-⇒-] ⊢M)                           = `lift[-⇒-] ⊢M′
  where
    ⊢M′ = true⊢[/]ʳ Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T ⊢M

true⊢[/]ʳ {M = `unlift[ _ ⇒ _ ] M}           Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T                  (Δ₀dΔ′∤ ⊢`unlift[-⇒-] ⊢M ⦂ ⊢↑)
  with _ , _ , refl , Δ₀∤ , d∤ ∷ Δ′∤ ← ∤-preserves-++ Δ₀ Δ₀dΔ′∤
    with Δ₀Δ′∤ ← ∤-++⁺ Δ₀∤ Δ′∤
       | eqΔ₀′ ← length-respects-∤ Δ₀∤
      with d∤
...      | keep m₁≤
        rewrite proj₂ (dec-yes (_ ≤?ₘ _) m₁≤)
          with _ , Γ∤ , Γ′~ ← ~⊞⁻¹-preserves-∤ Δ₀Δ′∤ (⊢∧≤⇒∤ ⊢Γ₁ m₁≤) Γ~
            with ⊢M′ ← subst-[/-] eqΔ₀′ M (true⊢[/]ʳ _ Γ′~ ⊢Γ₁ ⊢L ⊢↑ ⊢M)                                                = Γ∤ ⊢`unlift[-⇒-] ⊢M′ ⦂ ⊢↑
...      | delete m₁≰ (weakening Wk∈m₀)
        rewrite dec-no (_ ≤?ₘ _) m₁≰
          with Γ₁Del ← ⊢∧Wk≤⇒is-all-del ⊢Γ₁ ≤ₘ-refl Wk∈m₀
             | ⊢M′ ← subst-[/-] eqΔ₀′ M (false⊢[/] _ ⊢M)                                                                = ~⊞-is-all-del∧⊢⇒⊢ˡ Γ~ Γ₁Del (Δ₀Δ′∤ ⊢`unlift[-⇒-] ⊢M′ ⦂ ⊢↑)

true⊢[/]ʳ {M = `return[ _ ⇒ _ ] M}           Δ₀ Γ~ ⊢Γ₁ ⊢L (`↓[-⇒ _ ][ _ ] ⊢T) (Δ₀dΔ′∤ ⊢`return[-⇒-] ⊢M)
  with _ , _ , refl , Δ₀∤ , d∤ ∷ Δ′∤ ← ∤-preserves-++ Δ₀ Δ₀dΔ′∤
    with Δ₀Δ′∤ ← ∤-++⁺ Δ₀∤ Δ′∤
       | eqΔ₀′ ← length-respects-∤ Δ₀∤
      with d∤
...      | keep m₁≤
        rewrite proj₂ (dec-yes (_ ≤?ₘ _) m₁≤)
          with _ , Γ∤ , Γ′~ ← ~⊞⁻¹-preserves-∤ Δ₀Δ′∤ (⊢∧≤⇒∤ ⊢Γ₁ m₁≤) Γ~
            with ⊢M′ ← subst-[/-] eqΔ₀′ M (true⊢[/]ʳ _ Γ′~ ⊢Γ₁ ⊢L ⊢T ⊢M)                                                = Γ∤ ⊢`return[-⇒-] ⊢M′
...      | delete m₁≰ (weakening Wk∈m₀)
        rewrite dec-no (_ ≤?ₘ _) m₁≰
          with Γ₁Del ← ⊢∧Wk≤⇒is-all-del ⊢Γ₁ ≤ₘ-refl Wk∈m₀
             | ⊢M′ ← subst-[/-] eqΔ₀′ M (false⊢[/] _ ⊢M)                                                                = ~⊞-is-all-del∧⊢⇒⊢ˡ Γ~ Γ₁Del (Δ₀Δ′∤ ⊢`return[-⇒-] ⊢M′)

true⊢[/]ʳ {M = `let-return[ m₁ ⇒ _ ] M `in N} Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T                  (Δ₀dΔ′~ & Δ₀₀d₀Δ′₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢M ⦂ ⊢↓ `in ⊢N)
  with `↓[-⇒ _ ][ _ ] ⊢T₀ ← ⊢↓
     | Δ₀₀ , _ , _ , _ , refl , refl , Δ₀~ , d~ ∷ Δ′~ ← ~⊞-preserves-++ Δ₀ Δ₀dΔ′~
    with _ , _ , refl , Δ₀₀∤ , d₀∤ ∷ Δ′₀∤ ← ∤-preserves-++ Δ₀₀ Δ₀₀d₀Δ′₀∤
       | Δ₀Δ′~ ← ~⊞-++⁺ Δ₀~ Δ′~
       | eqΔ₀₀ , eqΔ₀₁ ← length-respects-~⊞ Δ₀~
      with Δ₀₀Δ′₀∤ ← ∤-++⁺ Δ₀₀∤ Δ′₀∤
         | eqΔ₀₀′ ← length-respects-∤ Δ₀₀∤
        with d~ | d₀∤
...        | contraction Co∈m₀ | keep m₁≤
          rewrite proj₂ (dec-yes (_ ≤?ₘ _) m₁≤)
            with _ , _ , Γ₂′~ , Γ₃′~ , Γ~′ ← ~⊞-contraction-assocˡ Γ~ Δ₀Δ′~ ⊢Γ₁ Co∈m₀
              with _ , Γ₀∤ , Γ₀′~ ← ~⊞⁻¹-preserves-∤ Δ₀₀Δ′₀∤ (⊢∧≤⇒∤ ⊢Γ₁ m₁≤) Γ₂′~
                 | ⊢N′ ← subst-[/-] (cong suc eqΔ₀₁) N (true⊢[/]ʳ _ (to-left ∷ Γ₃′~) ((⊢T₀ , unusable) ∷ ⊢Γ₁) (⊢wk[-↑-] [] (unusable ∷ []) ⊢L) ⊢T ⊢N)
                with ⊢M′ ← subst-[/-] (trans eqΔ₀₀′ eqΔ₀₀) M (true⊢[/]ʳ _ Γ₀′~ ⊢Γ₁ ⊢L ⊢↓ ⊢M) = Γ~′ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢M′ ⦂ ⊢↓ `in ⊢N′
...        | contraction Co∈m₀ | delete m₁≰ (weakening Wk∈m₀)
          rewrite dec-no (_ ≤?ₘ _) m₁≰
            with _ , _ , Γ₂′~ , Γ₃′~ , Γ~′ ← ~⊞-contraction-assocˡ Γ~ Δ₀Δ′~ ⊢Γ₁ Co∈m₀
               | _ , Γ₁∤ , Γ₁′Del ← is-all-del⇒∤ m₁ (⊢∧Wk≤⇒is-all-del ⊢Γ₁ ≤ₘ-refl Wk∈m₀)
              with _ , Γ₂′∤ , Γ₂″~ ← ~⊞⁻¹-preserves-∤ Δ₀₀Δ′₀∤ Γ₁∤ Γ₂′~
                 | ⊢N′ ← subst-[/-] (cong suc eqΔ₀₁) N (true⊢[/]ʳ _ (to-left ∷ Γ₃′~) ((⊢T₀ , unusable) ∷ ⊢Γ₁) (⊢wk[-↑-] [] (unusable ∷ []) ⊢L) ⊢T ⊢N)
                 | ⊢M′ ← subst-[/-] (trans eqΔ₀₀′ eqΔ₀₀) M (false⊢[/] _ ⊢M)                                                = Γ~′ & Γ₂′∤ ⊢`let-return[ m≤m₁ ⇒-] ~⊞-is-all-del∧⊢⇒⊢ˡ Γ₂″~ Γ₁′Del ⊢M′ ⦂ ⊢↓ `in ⊢N′
...        | to-left           | keep m₁≤
          rewrite proj₂ (dec-yes (_ ≤?ₘ _) m₁≤)
            with Γ₁′ , Γ₁′~ , Γ~′ ← ~⊞-assocʳ (~⊞-commute Γ~) Δ₀Δ′~
              with _ , Γ₁′∤ , Γ₁″~ ← ~⊞⁻¹-preserves-∤ (⊢∧≤⇒∤ ⊢Γ₁ m₁≤) Δ₀₀Δ′₀∤ Γ₁′~
                 | ⊢N′ ← subst-[/-] (cong suc eqΔ₀₁) N (false⊢[/] _ ⊢N)
                with ⊢M′ ← subst-[/-] (trans eqΔ₀₀′ eqΔ₀₀) M (true⊢[/]ˡ _ Γ₁″~ ⊢Γ₁ ⊢L ⊢↓ ⊢M) = Γ~′ & Γ₁′∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢M′ ⦂ ⊢↓ `in ⊢N′
...        | to-left           | delete m₁≰ (weakening Wk∈m₀)
          rewrite dec-no (_ ≤?ₘ _) m₁≰
            with Γ₁′ , Γ₁′~ , Γ~′ ← ~⊞-assocʳ (~⊞-commute Γ~) Δ₀Δ′~
              with _ , Γ₁∤ , Γ₁′Del ← is-all-del⇒∤ m₁ (⊢∧Wk≤⇒is-all-del ⊢Γ₁ ≤ₘ-refl Wk∈m₀)
                with _ , Γ₁′∤ , Γ₁″~ ← ~⊞⁻¹-preserves-∤ Γ₁∤ Δ₀₀Δ′₀∤ Γ₁′~
                   | ⊢N′ ← subst-[/-] (cong suc eqΔ₀₁) N (false⊢[/] _ ⊢N)
                   | ⊢M′ ← subst-[/-] (trans eqΔ₀₀′ eqΔ₀₀) M (false⊢[/] _ ⊢M) = Γ~′ & Γ₁′∤ ⊢`let-return[ m≤m₁ ⇒-] ~⊞-is-all-del∧⊢⇒⊢ʳ Γ₁″~ Γ₁′Del ⊢M′ ⦂ ⊢↓ `in ⊢N′
...        | to-right          | keep m₁≤
          rewrite proj₂ (dec-yes (_ ≤?ₘ _) m₁≤)
            with Γ₁′ , Γ₁′~ , Γ~′ ← ~⊞-assocˡ Γ~ Δ₀Δ′~
              with ⊢N′ ← subst-[/-] (cong suc eqΔ₀₁) N (true⊢[/]ʳ _ (to-left ∷ Γ₁′~) ((⊢T₀ , unusable) ∷ ⊢Γ₁) (⊢wk[-↑-] [] (unusable ∷ []) ⊢L) ⊢T ⊢N)
                 | ⊢M′ ← subst-[/-] (trans eqΔ₀₀′ eqΔ₀₀) M (false⊢[/] _ ⊢M) = Γ~′ & Δ₀₀Δ′₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢M′ ⦂ ⊢↓ `in ⊢N′
...        | to-right          | delete m₁≰ unusable
          rewrite dec-no (_ ≤?ₘ _) m₁≰
            with Γ₁′ , Γ₁′~ , Γ~′ ← ~⊞-assocˡ Γ~ Δ₀Δ′~
              with ⊢N′ ← subst-[/-] (cong suc eqΔ₀₁) N (true⊢[/]ʳ _ (to-left ∷ Γ₁′~) ((⊢T₀ , unusable) ∷ ⊢Γ₁) (⊢wk[-↑-] [] (unusable ∷ []) ⊢L) ⊢T ⊢N)
                 | ⊢M′ ← subst-[/-] (trans eqΔ₀₀′ eqΔ₀₀) M (false⊢[/] _ ⊢M)                                 = Γ~′ & Δ₀₀Δ′₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢M′ ⦂ ⊢↓ `in ⊢N′

true⊢[/]ʳ                                    Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T                  (`#_ {x = y} y∈)
  with y ℕ.≥? length Δ₀
...  | no  y≱
    with y< ← ℕ.≰⇒> y≱
      with weakening Wk∈m₀ ∷ _ ← <∧∈-++⇒is-all-del Δ₀ y∈ y<
         | y∈′ ← <∧∈-++-++⇒∈-++ Δ₀ (_ ∷ []) y∈ y<
        with y∈″ ← ~⊞-is-all-del∧∈⇒∈ˡ Γ~ (⊢∧Wk≤⇒is-all-del ⊢Γ₁ ≤ₘ-refl Wk∈m₀) y∈′                                      = `# y∈″
...  | yes y≥
    with y ℕ.≟ length Δ₀
...    | yes refl
      with Δ₀Δ′Del , refl , refl , refl ← len∈-inversion Δ₀ y∈                                                         = ~⊞-is-all-del∧⊢⇒⊢ʳ Γ~ Δ₀Δ′Del ⊢L
...    | no  y≢
      with y∈′ ← subst (_ ⦂[ _ ] _ ∈_) (sym (List.++-assoc Δ₀ (_ ∷ []) _)) y∈
         | y> ← subst (y ℕ.≥_) (ℕ.+-comm 1 _) (ℕ.≤∧≢⇒< y≥ (≢-sym y≢))
        with y∈″ ← ≥∧∈-++-++⇒∈-++ Δ₀ (_ ∷ []) y∈ y>
           | Δ₀dDel ← ≥∧∈-++⇒is-all-del _ y∈′ (subst (y ℕ.≥_) (sym (List.length-++ Δ₀)) y>)
          with weakening Wk∈m₀ ∷ _ ← All.++⁻ʳ Δ₀ Δ₀dDel
            with y∈‴ ← ~⊞-is-all-del∧∈⇒∈ˡ Γ~ (⊢∧Wk≤⇒is-all-del ⊢Γ₁ ≤ₘ-refl Wk∈m₀) y∈″                                  = `# y∈‴

true⊢[/]ˡ Δ₁ Γ~ ⊢Γ₀ ⊢L ⊢T ⊢M = true⊢[/]ʳ Δ₁ (~⊞-commute Γ~) ⊢Γ₀ ⊢L ⊢T ⊢M

-- Preservation
--
-- Note that they requires a general version that may allow a non-empty context
-- because of `let-return_`in_ (which introduces a variable of a higher mode
-- from a lower mode expression)
--
preservation    : ⊢[ m ] Γ →
                  ⊢[ m ] S ⦂⋆ →
                  Γ ⊢[ m ] L ⦂ S →
                  L ⟶ L′ →
                  -----------------
                  Γ ⊢[ m ] L′ ⦂ S
preservation[≤] : ⊢[ m ] Γ →
                  ⊢[ m ] S ⦂⋆ →
                  Γ ⊢[ m ] L ⦂ S →
                  L ⟶[ m₀ ≤] L′ →
                  -----------------
                  Γ ⊢[ m ] L′ ⦂ S

preservation ⊢Γ ⊢S                     (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                                                  ξ- L⟶ `$?                   = Γ~ ⊢ ⊢L′ ⦂ ⊢⊸ `$ ⊢M
  where
    ⊢L′ = preservation (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) ⊢⊸ ⊢L L⟶

preservation ⊢Γ ⊢S                     (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                                                  (ξ-! VL `$ M⟶)
  with ⊢T `⊸[ _ ] _ ← ⊢⊸                                                                                                                 = Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M′
  where
    ⊢M′ = preservation (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢T ⊢M M⟶

preservation ⊢Γ ⊢S                     (Γ~ ⊢ `λ⦂-∘ ⊢L ⦂ ⊢⊸ `$ ⊢M)                                            (β-`⊸ VM)                   = true⊢[/]ʳ [] Γ~ (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢M ⊢S ⊢L
preservation ⊢Γ (`↑[-⇒ <m ][ ↑∈m ] ⊢S) (`lift[-⇒-] ⊢L)                                                       (ξ-`lift[-⇒-] L⟶[≤])        = `lift[-⇒-] ⊢L′
  where
    ⊢L′ = preservation[≤] (⊢∧<ₘ⇒⊢ ⊢Γ <m) ⊢S ⊢L L⟶[≤]

preservation ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)                                            (ξ-`unlift[-⇒-] L⟶)         = Γ∤ ⊢`unlift[-⇒-] ⊢L′ ⦂ ⊢↑
  where
    ⊢L′ = preservation (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L L⟶

preservation ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[-⇒-] ⊢L ⦂ ⊢↑)                                 (β-`↑ WL)                   = ∤⁻¹-preserves-⊢ [] ⊢L Γ∤
preservation ⊢Γ (`↓[-⇒ m₁< ][ ↓∈m ] ⊢S) (Γ∤ ⊢`return[-⇒-] ⊢L)                                                 (ξ-`return[-⇒-] L⟶)         = Γ∤ ⊢`return[-⇒-] ⊢L′
  where
    ⊢L′ = preservation (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L L⟶

preservation ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢L ⦂ ⊢↓ `in ⊢M)                      ξ-`let-return[-⇒-] L⟶ `in-  = Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢L′ ⦂ ⊢↓ `in ⊢M
  where
    ⊢L′ = preservation (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) ⊢↓ ⊢L L⟶

preservation ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] (Γ₀′∤ ⊢`return[-⇒-] ⊢L) ⦂ ⊢↓ `in ⊢M) (β-`↓ VL)
  with `↓[-⇒ m₁< ][ _ ] ⊢T ← ⊢↓
     | Γ₀₁ , Γ₀~ , Γ₀₁Del ← ∤⇒~⊞-is-all-delʳ Γ₀∤
     | Γ₀′₁ , Γ₀′~ , Γ₀′₁Del ← ∤⇒~⊞-is-all-delʳ Γ₀′∤
    with Γ″ , Γ″~ , Γ~′ ← ~⊞-assocˡ Γ~ Γ₀~
      with Γ‴ , Γ‴~ , Γ~″ ← ~⊞-assocˡ Γ~′ Γ₀′~
        with ⊢Γ₀″ ← ⊢∧∤⇒⊢ (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) Γ₀′∤
           | ⊢M′ ← ~⊞-is-all-del∧⊢⇒⊢ʳ (to-right ∷ Γ‴~) (unusable ∷ Γ₀′₁Del) (~⊞-is-all-del∧⊢⇒⊢ʳ (to-right ∷ Γ″~) (unusable ∷ Γ₀₁Del) ⊢M) = true⊢[/]ˡ [] Γ~″ ⊢Γ₀″ ⊢L ⊢S ⊢M′

preservation[≤] ⊢Γ ⊢S                   (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                             ξ- L⟶[≤] `$?                            = Γ~ ⊢ ⊢L′ ⦂ ⊢⊸ `$ ⊢M
  where
    ⊢L′ = preservation[≤] (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) ⊢⊸ ⊢L L⟶[≤]

preservation[≤] ⊢Γ ⊢S                   (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                             (ξ-! WL `$ M⟶[≤])
  with ⊢T `⊸[ _ ] _ ← ⊢⊸                                                                                                         = Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M′
  where
    ⊢M′ = preservation[≤] (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢T ⊢M M⟶[≤]

preservation[≤] ⊢Γ (`↑[-⇒ <m ][ _ ] ⊢S) (`lift[-⇒-] ⊢L)                                  (ξ-`lift[-⇒-] L⟶[≤])                    = `lift[-⇒-] ⊢L′
  where
    ⊢L′ = preservation[≤] (⊢∧<ₘ⇒⊢ ⊢Γ <m) ⊢S ⊢L L⟶[≤] 

preservation[≤] ⊢Γ ⊢S                   (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)                       (ξ-`unlift[≰ ≰m₀ ⇒-] L⟶[≤])             = Γ∤ ⊢`unlift[-⇒-] ⊢L′ ⦂ ⊢↑
  where
    ⊢L′ = preservation[≤] (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L L⟶[≤]

preservation[≤] ⊢Γ ⊢S                   (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)                       (ξ-`unlift[≤ ≤m₀ ⇒-] L⟶)                = Γ∤ ⊢`unlift[-⇒-] ⊢L′ ⦂ ⊢↑
  where
    ⊢L′ = preservation (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L L⟶

preservation[≤] ⊢Γ ⊢S                   (Γ∤ ⊢`unlift[-⇒-] `lift[-⇒-] ⊢L ⦂ ⊢↑)            (β-`↑ m₀≤ WL)                           = ∤⁻¹-preserves-⊢ [] ⊢L Γ∤

preservation[≤] ⊢Γ (`↓[-⇒ _ ][ _ ] ⊢S)  (Γ∤ ⊢`return[-⇒-] ⊢L)                            (ξ-`return[≰ ≰m₀ ⇒-] L⟶[≤])             = Γ∤ ⊢`return[-⇒-] ⊢L′
  where
    ⊢L′ = preservation[≤] (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L L⟶[≤]

preservation[≤] ⊢Γ (`↓[-⇒ _ ][ _ ] ⊢S)  (Γ∤ ⊢`return[-⇒-] ⊢L)                            (ξ-`return[≤ ≤m₀ ⇒-] L⟶)                = Γ∤ ⊢`return[-⇒-] ⊢L′
  where
    ⊢L′ = preservation (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L L⟶

preservation[≤] ⊢Γ ⊢S                   (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) ξ-`let-return[≰ m₀≰ ⇒-] L⟶[≤] `in?      = Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢L′ ⦂ ⊢↓ `in ⊢M
  where
    ⊢L′ = preservation[≤] (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) ⊢↓ ⊢L L⟶[≤]

preservation[≤] ⊢Γ ⊢S                   (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) ξ-`let-return[≤ m₀≤ ⇒-] L⟶ `in?         = Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢L′ ⦂ ⊢↓ `in ⊢M
  where
    ⊢L′ = preservation (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) ⊢↓ ⊢L L⟶

preservation[≤] ⊢Γ ⊢S                   (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) (ξ-`let-return[≰ m₀≰ ⇒-]! WL `in M⟶[≤])
  with `↓[-⇒ m₁< ][ _ ] ⊢T ← ⊢↓                                                                                                   = Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢L ⦂ ⊢↓ `in ⊢M′
  where
    ⊢M′ = preservation[≤] ((⊢T , valid (≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m₁<))) ∷ ⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢S ⊢M M⟶[≤]

preservation[≤] ⊢Γ ⊢S                   (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) (ξ-`let-return[≤ m₀≤ ⇒-]! VL `in M⟶[≤])
  with `↓[-⇒ m₁< ][ _ ] ⊢T ← ⊢↓                                                                                                   = Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢L ⦂ ⊢↓ `in ⊢M′
  where
    ⊢M′ = preservation[≤] ((⊢T , valid (≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m₁<))) ∷ ⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢S ⊢M M⟶[≤]

preservation[≤] ⊢Γ (⊢S `⊸[ _ ] ⊢T)      (`λ⦂-∘ ⊢L)                                       (ξ-`λ⦂[-]-∘ L⟶[≤])                      = `λ⦂-∘ ⊢L′
  where
    ⊢L′ = preservation[≤] ((⊢S , valid ≤ₘ-refl) ∷ ⊢Γ) ⊢T ⊢L L⟶[≤]


-- Canonical form lemmas
--
canonoical-⊸ : Γ ⊢[ m ] L ⦂ S `⊸ T →
               WeakNorm L →
               -----------------------------------------------
               ∃₂ (λ S L′ → L ≡ `λ⦂[ m ] S ∘ L′) ⊎ WeakNeut L
canonoical-⊸ (`λ⦂-∘ ⊢L) (`λ⦂[ _ ] _ ∘ _) = inj₁ (-, -, refl)
canonoical-⊸ _          (`neut NL)       = inj₂ NL

canonoical-↑ : Γ ⊢[ m ] L ⦂ `↑[ m₀ ⇒ m ] S →
               WeakNorm L →
               -----------------------------------------------------------------------
               ∃ (λ L′ → L ≡ `lift[ m₀ ⇒ m ] L′ × DeferredTerm[ m ≤] L′) ⊎ WeakNeut L
canonoical-↑ (`lift[-⇒-] ⊢L) (`lift[ _ ⇒ _ ] WL) = inj₁ (-, refl , WL)
canonoical-↑ _               (`neut NL)          = inj₂ NL

canonoical-↓ : Γ ⊢[ m ] L ⦂ `↓[ m₀ ⇒ m ] S →
               WeakNorm L →
               ---------------------------------------------------------------
               ∃ (λ L′ → L ≡ `return[ m₀ ⇒ m ] L′ × WeakNorm L′) ⊎ WeakNeut L
canonoical-↓ (_ ⊢`return[-⇒-] ⊢L) (`return[ _ ⇒ _ ] VL) = inj₁ (-, refl , VL)
canonoical-↓ _                    (`neut NL)            = inj₂ NL


-- Progress
--
-- Again, they requires a general version that may allow a non-empty context.
--
progress    : ⊢[ m ] Γ →
              ⊢[ m ] S ⦂⋆ →
              Γ ⊢[ m ] L ⦂ S →
              -------------------------------
              WeakNorm L ⊎ ∃ (λ L′ → L ⟶ L′)
progress[≤] : ∀ m₀ →
              ⊢[ m ] Γ →
              ⊢[ m ] S ⦂⋆ →
              Γ ⊢[ m ] L ⦂ S →
              -------------------------------------------------
              DeferredTerm[ m₀ ≤] L ⊎ ∃ (λ L′ → L ⟶[ m₀ ≤] L′)


progress ⊢Γ ⊢S                            (`unit ΓDel)                          = inj₁ `unit
progress ⊢Γ ⊢S                            (`λ⦂-∘ ⊢L)                            = inj₁ (`λ⦂[ _ ] _ ∘ _)
progress ⊢Γ ⊢S                            (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with ⊢T `⊸[ _ ] _ ← ⊢⊸
     | ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~
    with progress ⊢Γ₀ ⊢⊸ ⊢L
...    | inj₂ (_ , L⟶)                                                          = inj₂ (-, ξ- L⟶ `$?)
...    | inj₁ VL
      with progress ⊢Γ₁ ⊢T ⊢M
...      | inj₂ (_ , M⟶)                                                        = inj₂ (-, ξ-! VL `$ M⟶)
...      | inj₁ VM
        with canonoical-⊸ ⊢L VL
...        | inj₂ NL                                                            = inj₁ (`neut (NL `$ VM))
...        | inj₁ (_ , _ , refl)                                                = inj₂ (-, β-`⊸ VM)

progress ⊢Γ (`↑[-⇒_][_]_ {m = m} <m _ ⊢S) (`lift[-⇒-] ⊢L)
  with progress[≤] m (⊢∧<ₘ⇒⊢ ⊢Γ <m) ⊢S ⊢L
...  | inj₂ (_ , L⟶[≤])                                                         = inj₂ (-, ξ-`lift[-⇒-] L⟶[≤])
...  | inj₁ WL                                                                  = inj₁ (`lift[ _ ⇒ _ ] WL)

progress ⊢Γ ⊢S                            (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)
  with progress (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L
...  | inj₂ (_ , L⟶)                                                            = inj₂ (-, ξ-`unlift[-⇒-] L⟶)
...  | inj₁ VL
    with canonoical-↑ ⊢L VL
...    | inj₂ NL                                                                = inj₁ (`neut (`unlift[ _ ⇒ _ ] NL))
...    | inj₁ (_ , refl , WL′)                                                  = inj₂ (-, β-`↑ WL′)

progress ⊢Γ (`↓[-⇒ _ ][ _ ] ⊢S)           (Γ∤ ⊢`return[-⇒-] ⊢L)
  with progress (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L
...  | inj₂ (_ , L⟶)                                                            = inj₂ (-, ξ-`return[-⇒-] L⟶)
...  | inj₁ VL                                                                  = inj₁ (`return[ _ ⇒ _ ] VL)

progress ⊢Γ ⊢S                            (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢L ⦂ ⊢↓ `in ⊢M)
  with `↓[-⇒ _ ][ _ ] ⊢T ← ⊢↓
     | ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~
    with ⊢Γ₀′ ← ⊢∧∤⇒⊢ ⊢Γ₀ Γ₀∤
      with progress ⊢Γ₀′ ⊢↓ ⊢L
...      | inj₂ (_ , L⟶)                                                        = inj₂ (-, ξ-`let-return[-⇒-] L⟶ `in-)
...      | inj₁ VL
        with canonoical-↓ ⊢L VL
...        | inj₂ NL                                                            = inj₁ (`neut (`let-return[ _ ⇒ _ ] NL `in _))
...        | inj₁ (_ , refl , VL′)                                              = inj₂ (-, β-`↓ VL′)

progress ⊢Γ ⊢S                            (`# x∈)                               = inj₁ (`neut (`# _))


progress[≤]                           m₀ ⊢Γ ⊢S                    (`unit ΓDel)                         = inj₁ `unit
progress[≤]                           m₀ ⊢Γ (⊢S `⊸[ _ ] ⊢T)       (`λ⦂-∘ ⊢L)
  with progress[≤] m₀ ((⊢S , valid ≤ₘ-refl) ∷ ⊢Γ) ⊢T ⊢L
...  | inj₂ (_ , L⟶[≤])                                                                                = inj₂ (-, ξ-`λ⦂[-]-∘ L⟶[≤])
...  | inj₁ WL                                                                                         = inj₁ (`λ⦂[ _ ] _ ∘ WL)

progress[≤]                           m₀ ⊢Γ ⊢S                    (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with ⊢T `⊸[ _ ] _ ← ⊢⊸
     | ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~
    with progress[≤] m₀ ⊢Γ₀ ⊢⊸ ⊢L
...    | inj₂ (_ , L⟶[≤])                                                                              = inj₂ (-, ξ- L⟶[≤] `$?)
...    | inj₁ WL
      with progress[≤] m₀ ⊢Γ₁ ⊢T ⊢M
...      | inj₂ (_ , M⟶[≤])                                                                            = inj₂ (-, ξ-! WL `$ M⟶[≤])
...      | inj₁ WM                                                                                     = inj₁ (WL `$ WM)

progress[≤]                           m₀ ⊢Γ (`↑[-⇒ <m ][ _ ] ⊢S) (`lift[-⇒-] ⊢L)
  with progress[≤] m₀ (⊢∧<ₘ⇒⊢ ⊢Γ <m) ⊢S ⊢L
...  | inj₂ (_ , L⟶[≤])                                                                                = inj₂ (-, ξ-`lift[-⇒-] L⟶[≤])
...  | inj₁ WL                                                                                         = inj₁ (`lift[ _ ⇒ _ ] WL)

progress[≤] {L = `unlift[ m₁ ⇒ _ ] L} m₀ ⊢Γ ⊢S                   (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)
  with m₀ ≤?ₘ m₁
...  | no  m₀≰
    with progress[≤] m₀ (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L
...    | inj₂ (_ , L⟶[≤])                                                                              = inj₂ (-, (ξ-`unlift[≰ m₀≰ ⇒-] L⟶[≤]))
...    | inj₁ WL                                                                                       = inj₁ (`unlift[≰ m₀≰ ⇒ _ ] WL)

progress[≤] {L = `unlift[ m₁ ⇒ _ ] L} m₀ ⊢Γ ⊢S                   (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)
     | yes m₀≤
    with progress (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L
...    | inj₂ (_ , L⟶)                                                                                 = inj₂ (-, ξ-`unlift[≤ m₀≤ ⇒-] L⟶)
...    | inj₁ VL
      with ≢lift[-⇒-]? L
...      | no ¬≢liftL
        with _ , _ , _ , refl ← ¬≢lift[-⇒-]⇒≡lift[-⇒-] L ¬≢liftL
          with `lift[-⇒-] ⊢L′ ← ⊢L
             | `lift[ _ ⇒ _ ] VL′ ← VL                                                                 = inj₂ (-, β-`↑ m₀≤ VL′)
...      | yes ≢liftL                                                                                  = inj₁ (`unlift[≤ m₀≤ ⇒ _ ] VL {≢liftL})

progress[≤] {L = `return[ m₁ ⇒ _ ] L} m₀ ⊢Γ (`↓[-⇒ _ ][ _ ] ⊢S)  (Γ∤ ⊢`return[-⇒-] ⊢L)
  with m₀ ≤?ₘ m₁
...  | no  m₀≰
    with progress[≤] m₀ (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L
...    | inj₂ (_ , L⟶[≤])                                                                              = inj₂ (-, (ξ-`return[≰ m₀≰ ⇒-] L⟶[≤]))
...    | inj₁ WL                                                                                       = inj₁ (`return[≰ m₀≰ ⇒ _ ] WL)

progress[≤] {L = `return[ m₁ ⇒ _ ] L} m₀ ⊢Γ (`↓[-⇒ _ ][ _ ] ⊢S)  (Γ∤ ⊢`return[-⇒-] ⊢L)
     | yes m₀≤
    with progress (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L
...    | inj₂ (_ , L⟶)                                                                                 = inj₂ (-, ξ-`return[≤ m₀≤ ⇒-] L⟶)
...    | inj₁ VL                                                                                       = inj₁ (`return[≤ m₀≤ ⇒ _ ] VL)

progress[≤] {L = `let-return[ m₁ ⇒ _ ] L `in M} m₀ ⊢Γ ⊢S                   (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢L ⦂ ⊢↓ `in ⊢M)
  with `↓[-⇒ m< ][ _ ] ⊢T ← ⊢↓
     | ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~
    with ⊢Γ₀′ ← ⊢∧∤⇒⊢ ⊢Γ₀ Γ₀∤
      with m₀ ≤?ₘ m₁
...      | no  m₀≰
      with progress[≤] m₀ ⊢Γ₀′ ⊢↓ ⊢L
...      | inj₂ (_ , L⟶[≤])                                                                            = inj₂ (-, ξ-`let-return[≰ m₀≰ ⇒-] L⟶[≤] `in?)
...      | inj₁ WL
        with progress[≤] m₀ ((⊢T , valid (≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m<))) ∷ ⊢Γ₁) ⊢S ⊢M
...        | inj₂ (_ , M⟶[≤])                                                                          = inj₂ (-, ξ-`let-return[≰ m₀≰ ⇒-]! WL `in M⟶[≤])
...        | inj₁ WM                                                                                   = inj₁ (`let-return[≰ m₀≰ ⇒ _ ] WL `in WM)
progress[≤] {L = `let-return[ m₁ ⇒ _ ] L `in M} m₀ ⊢Γ ⊢S                   (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] ⊢L ⦂ ⊢↓ `in ⊢M)
         | yes m₀≤
      with progress ⊢Γ₀′ ⊢↓ ⊢L
...      | inj₂ (_ , L⟶)                                                                               = inj₂ (-, ξ-`let-return[≤ m₀≤ ⇒-] L⟶ `in?)
...      | inj₁ VL
        with progress[≤] m₀ ((⊢T , valid (≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m<))) ∷ ⊢Γ₁) ⊢S ⊢M
...        | inj₂ (_ , M⟶[≤])                                                                          = inj₂ (-, ξ-`let-return[≤ m₀≤ ⇒-]! VL `in M⟶[≤])
...        | inj₁ WM                                                                                   = inj₁ (`let-return[≤ m₀≤ ⇒ _ ] VL `in WM)

progress[≤]                          m₀ ⊢Γ ⊢S                   (`# x∈)                                = inj₁ (`# _)


-- Weakening property for equivalence
--
subst-wk[-↑-]≈wk[-↑-] : x ≡ x′ →
                        k ≡ k′ →
                        ∀ L L′ →
                        Γ ⊢[ m ] wk[ x ↑ k ] L ≈[≥ m′ ] wk[ x ↑ k ] L′ ⦂ S →
                        -------------------------------------------------------
                        Γ ⊢[ m ] wk[ x′ ↑ k′ ] L ≈[≥ m′ ] wk[ x′ ↑ k′ ] L′ ⦂ S
subst-wk[-↑-]≈wk[-↑-] {Γ = Γ} {m} {m′} {S} eq₀ eq₁ L L′ = subst₂ (λ x k → Γ ⊢[ m ] wk[ x ↑ k ] L ≈[≥ m′ ] wk[ x ↑ k ] L′ ⦂ S) eq₀ eq₁

-- Weakening preserves equivalence
wk[-↑-]≈wk[-↑-] : ∀ Δ →
                  Γ′ is-all-del →
                  Δ ++ Γ ⊢[ m ] L ≈[≥ m′ ] L′ ⦂ S →
                  --------------------------------------------------------------------------------------------
                  Δ ++ Γ′ ++ Γ ⊢[ m ] wk[ length Γ′ ↑ length Δ ] L ≈[≥ m′ ] wk[ length Γ′ ↑ length Δ ] L′ ⦂ S
wk[-↑-]≈wk[-↑-]                                                                                Δ Γ′Del (`unit ΔΓDel)                             = `unit ΔΓ′ΓDel
  where
    ΔΓ′ΓDel = All.++⁺ (All.++⁻ˡ Δ ΔΓDel) (All.++⁺ Γ′Del (All.++⁻ʳ Δ ΔΓDel))
wk[-↑-]≈wk[-↑-]                                                                                Δ Γ′Del (`lift[≤ m′≤m ⇒-] L≈L′)                   = `lift[≤ m′≤m ⇒-] (wk[-↑-]≈wk[-↑-] Δ Γ′Del L≈L′)
wk[-↑-]≈wk[-↑-]                                                                                Δ Γ′Del (`lift[≰ m′≰m ⇒-] ⊢L ⊢L′)                 = `lift[≰ m′≰m ⇒-] (⊢wk[-↑-] Δ Γ′Del ⊢L) (⊢wk[-↑-] Δ Γ′Del ⊢L′)
wk[-↑-]≈wk[-↑-]      {L = `unlift[ m₀ ⇒ _ ] L}           {L′ = `unlift[ _ ⇒ _ ] L′}            Δ Γ′Del (ΔΓ∤ ⊢`unlift[-⇒-] L≈L′ ⦂ ⊢↑)
    with Δ′ , _ , refl , Δ∤ , Γ∤ ← ∤-preserves-++ Δ ΔΓ∤
       | _ , Γ′∤ , _ ← is-all-del⇒∤ m₀ Γ′Del                                                                                                     = ΔΓ′Γ∤ ⊢`unlift[-⇒-] L≈L′′ ⦂ ⊢↑
  where
    ΔΓ′Γ∤ = ∤-++⁺ Δ∤ (∤-++⁺ Γ′∤ Γ∤)
    L≈L′′ = subst-wk[-↑-]≈wk[-↑-] (length-respects-∤ Γ′∤) (length-respects-∤ Δ∤) L L′ (wk[-↑-]≈wk[-↑-] Δ′ (∤-preserves-is-all-del Γ′Del Γ′∤) L≈L′)
wk[-↑-]≈wk[-↑-]      {L = `return[ m₀ ⇒ _ ] L}           {L′ = `return[ _ ⇒ _ ] L′}            Δ Γ′Del (ΔΓ∤ ⊢`return[-⇒-] L≈L′)
  with Δ′ , _ , refl , Δ∤ , Γ∤ ← ∤-preserves-++ Δ ΔΓ∤
     | _ , Γ′∤ , _ ← is-all-del⇒∤ m₀ Γ′Del                                                                                                       = ΔΓ′Γ∤ ⊢`return[-⇒-] L≈L′′
  where
    ΔΓ′Γ∤ = ∤-++⁺ Δ∤ (∤-++⁺ Γ′∤ Γ∤)
    L≈L′′ = subst-wk[-↑-]≈wk[-↑-] (length-respects-∤ Γ′∤) (length-respects-∤ Δ∤) L L′ (wk[-↑-]≈wk[-↑-] Δ′ (∤-preserves-is-all-del Γ′Del Γ′∤) L≈L′)
wk[-↑-]≈wk[-↑-] {Γ′} {L = `let-return[ m₁ ⇒ _ ] L `in M} {L′ = `let-return[ _ ⇒ _ ] L′ `in M′} Δ Γ′Del (ΔΓ~ & Δ₀Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L≈L′ ⦂ ⊢↓ `in M≈M′)
    with Δ₀ , Δ₁ , Γ₀ , Γ₁ , refl , refl , Δ~ , Γ~ ← ~⊞-preserves-++ Δ ΔΓ~
       | Γ′₁ , Γ′~ ← left-bias-~⊞ Γ′
      with Δ₀′ , _ , refl , Δ₀∤ , Γ₀∤ ← ∤-preserves-++ Δ₀ Δ₀Γ₀∤
         | _ , Γ′∤ , Γ″Del ← is-all-del⇒∤ m₁ Γ′Del
         | _    , Γ′₁Del ← ~⊞-preserves-is-all-del Γ′Del Γ′~
         | eqΔ₀ , eqΔ₁ ← length-respects-~⊞ Δ~                                                                                                   = ΔΓ′Γ~ & Δ₀Γ′Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L≈L′′ ⦂ ⊢↓ `in M≈M′′
  where
    ΔΓ′Γ~ = ~⊞-++⁺ Δ~ (~⊞-++⁺ Γ′~ Γ~)
    Δ₀Γ′Γ₀∤ = ∤-++⁺ Δ₀∤ (∤-++⁺ Γ′∤ Γ₀∤)
    L≈L′′ = subst-wk[-↑-]≈wk[-↑-] (length-respects-∤ Γ′∤) (trans (length-respects-∤ Δ₀∤) eqΔ₀) L L′ (wk[-↑-]≈wk[-↑-] Δ₀′ Γ″Del L≈L′)
    M≈M′′ = subst-wk[-↑-]≈wk[-↑-] (proj₂ (length-respects-~⊞ Γ′~)) (cong suc eqΔ₁) M M′ (wk[-↑-]≈wk[-↑-] (_ ∷ Δ₁) Γ′₁Del M≈M′)
wk[-↑-]≈wk[-↑-]                                                                               Δ Γ′Del (`λ⦂-∘ L≈L′)                               = `λ⦂-∘ L≈L′′
  where
    L≈L′′ = wk[-↑-]≈wk[-↑-] (_ ∷ Δ) Γ′Del L≈L′
wk[-↑-]≈wk[-↑-] {Γ′} {L = L `$ M}                        {L′ = L′ `$ M′}                      Δ Γ′Del (ΔΓ~ ⊢ L≈L′ ⦂ ⊢⊸ `$ M≈M′)
  with Δ₀ , Δ₁ , _ , _ , refl , refl , Δ~ , Γ~ ← ~⊞-preserves-++ Δ ΔΓ~
     | _ , Γ′~ ← left-bias-~⊞ Γ′
    with _    , Γ′₁Del ← ~⊞-preserves-is-all-del Γ′Del Γ′~
       | eqΔ₀ , eqΔ₁ ← length-respects-~⊞ Δ~                                                                                                     = ΔΓ′Γ~ ⊢ L≈L′′ ⦂ ⊢⊸ `$ M≈M′′
  where
    ΔΓ′Γ~ = ~⊞-++⁺ Δ~ (~⊞-++⁺ Γ′~ Γ~)
    L≈L′′ = subst-wk[-↑-]≈wk[-↑-] refl eqΔ₀ L L′ (wk[-↑-]≈wk[-↑-] Δ₀ Γ′Del L≈L′)
    M≈M′′ = subst-wk[-↑-]≈wk[-↑-] (proj₂ (length-respects-~⊞ Γ′~)) eqΔ₁ M M′ (wk[-↑-]≈wk[-↑-] Δ₁ Γ′₁Del M≈M′)
wk[-↑-]≈wk[-↑-]                                                                               Δ Γ′Del (`#_ {x = x} x∈)
  with x ℕ.≥? length Δ
...  | yes x≥                                                                                                                                    = `# ≥∧∈-++⇒+-∈-++-++ Δ Γ′Del x∈ x≥
...  | no  x≱                                                                                                                                    = `# <∧∈-++⇒∈-++-++ Δ Γ′Del x∈ (ℕ.≰⇒> x≱)

-- Substitution property for equivalence
--
subst-[/-]≈[/-] : x ≡ x′ →
                  ∀ M M′ →
                  Γ ⊢[ m ] [ L /[ m₀ ] x ] M ≈[≥ m′ ] [ L′ /[ m₀ ] x ] M′ ⦂ T →
                  --------------------------------------------------------------
                  Γ ⊢[ m ] [ L /[ m₀ ] x′ ] M ≈[≥ m′ ] [ L′ /[ m₀ ] x′ ] M′ ⦂ T
subst-[/-]≈[/-] {Γ = Γ} {m} {L} {m₀} {m′} {L′} {T} eq M M′ = subst (λ x → Γ ⊢[ m ] [ L /[ m₀ ] x ] M ≈[≥ m′ ] [ L′ /[ m₀ ] x ] M′ ⦂ T) eq

-- Strengthening preserves equivalence
false⊢[/]≈[/] : ∀ Δ₀ →
                Δ₀ ++ (S , m₀ , false) ∷ Δ′ ⊢[ m ] M ≈[≥ m′ ] M′ ⦂ T →
                -----------------------------------------------------------------------------------
                Δ₀ ++ Δ′ ⊢[ m ] [ L /[ m₀ ] length Δ₀ ] M ≈[≥ m′ ] [ L′ /[ m₀ ] length Δ₀ ] M′ ⦂ T
false⊢[/]≈[/]                                                                           Δ₀ (`unit Δ₀dΔ′Del)
  with Δ₀Del , _ ∷ Δ′Del ← All.++⁻ Δ₀ Δ₀dΔ′Del                                                                                          = `unit Δ₀Δ′Del
  where
    Δ₀Δ′Del = All.++⁺ Δ₀Del Δ′Del

false⊢[/]≈[/]                                                                           Δ₀ (`lift[≤ m′≤m ⇒-] M≈M′)                      = `lift[≤ m′≤m ⇒-] M≈M′′
  where
    M≈M′′ = false⊢[/]≈[/] Δ₀ M≈M′
false⊢[/]≈[/]                                                                           Δ₀ (`lift[≰ m′≰m ⇒-] ⊢M ⊢M′)                    = `lift[≰ m′≰m ⇒-] (false⊢[/] Δ₀ ⊢M) (false⊢[/] Δ₀ ⊢M′)

false⊢[/]≈[/] {M = `unlift[ _ ⇒ _ ] M}            {M′ = `unlift[ _ ⇒ _ ] M′}            Δ₀ (Δ₀dΔ′∤ ⊢`unlift[-⇒-] M≈M′ ⦂ ⊢↑)
  with _ , _ ∷ _ , refl , Δ₀∤ , d∤ ∷ Δ′∤ ← ∤-preserves-++ Δ₀ Δ₀dΔ′∤
    with Δ₀Δ′∤ ← ∤-++⁺ Δ₀∤ Δ′∤
       | eqΔ₀ ← length-respects-∤ Δ₀∤
      with d∤
...      | keep m₁≤
        rewrite proj₂ (dec-yes (_ ≤?ₘ _) m₁≤)
          with M≈M′′ ← subst-[/-]≈[/-] eqΔ₀ M M′ (false⊢[/]≈[/] _ M≈M′)                                                                 = Δ₀Δ′∤ ⊢`unlift[-⇒-] M≈M′′ ⦂ ⊢↑
...      | delete m₁≰ dDel
        rewrite dec-no (_ ≤?ₘ _) m₁≰
          with M≈M′′ ← subst-[/-]≈[/-] eqΔ₀ M M′ (false⊢[/]≈[/] _ M≈M′)                                                                 = Δ₀Δ′∤ ⊢`unlift[-⇒-] M≈M′′ ⦂ ⊢↑

false⊢[/]≈[/] {M = `return[ _ ⇒ _ ] M}            {M′ = `return[ _ ⇒ _ ] M′}            Δ₀ (Δ₀dΔ′∤ ⊢`return[-⇒-] M≈M′)
  with _ , _ ∷ _ , refl , Δ₀∤ , d∤ ∷ Δ′∤ ← ∤-preserves-++ Δ₀ Δ₀dΔ′∤
    with Δ₀Δ′∤ ← ∤-++⁺ Δ₀∤ Δ′∤
       | eqΔ₀ ← length-respects-∤ Δ₀∤
      with d∤
...      | keep m₁≤
        rewrite proj₂ (dec-yes (_ ≤?ₘ _) m₁≤)
          with M≈M′′ ← subst-[/-]≈[/-] eqΔ₀ M M′ (false⊢[/]≈[/] _ M≈M′)                                                                 = Δ₀Δ′∤ ⊢`return[-⇒-] M≈M′′
...      | delete m₁≰ dDel
        rewrite dec-no (_ ≤?ₘ _) m₁≰
          with M≈M′′ ← subst-[/-]≈[/-] eqΔ₀ M M′ (false⊢[/]≈[/] _ M≈M′)                                                                 = Δ₀Δ′∤ ⊢`return[-⇒-] M≈M′′

false⊢[/]≈[/] {M = `let-return[ m₁ ⇒ _ ] M `in N} {M′ = `let-return[ _ ⇒ _ ] M′ `in N′} Δ₀ (Δ₀dΔ′~ & Δ₀₀d₀Δ′₀∤ ⊢`let-return[ m≤m₁ ⇒-] M≈M′ ⦂ ⊢↓ `in N≈N′)
  with Δ₀₀ , Δ₀₁ , _ ∷ Δ′₀ , _ ∷ Δ′₁ , refl , refl , Δ₀~ , unusable ∷ Δ′~ ← ~⊞-preserves-++ Δ₀ Δ₀dΔ′~
    with Δ₀Δ′~ ← ~⊞-++⁺ Δ₀~ Δ′~
       | Δ₀₀′ , _ ∷ _ , refl , Δ₀₀∤ , d₀∤ ∷ Δ′₀∤ ← ∤-preserves-++ Δ₀₀ Δ₀₀d₀Δ′₀∤
       | eqΔ₀₀ , eqΔ₀₁ ← length-respects-~⊞ Δ₀~
      with Δ₀₀Δ′₀∤ ← ∤-++⁺ Δ₀₀∤ Δ′₀∤
      with d₀∤
...      | keep m₁≤
        rewrite proj₂ (dec-yes (_ ≤?ₘ _) m₁≤)
          with M≈M′′ ← subst-[/-]≈[/-] (trans (length-respects-∤ Δ₀₀∤) eqΔ₀₀) M M′ (false⊢[/]≈[/] Δ₀₀′ M≈M′)
             | N≈N′′ ← subst-[/-]≈[/-] (cong suc eqΔ₀₁) N N′ (false⊢[/]≈[/] (_ ∷ Δ₀₁) N≈N′)                                             = Δ₀Δ′~ & Δ₀₀Δ′₀∤ ⊢`let-return[ m≤m₁ ⇒-] M≈M′′ ⦂ ⊢↓ `in N≈N′′
...      | delete m₁≰ d₀Del
        rewrite dec-no (_ ≤?ₘ _) m₁≰
          with M≈M′′ ← subst-[/-]≈[/-] (trans (length-respects-∤ Δ₀₀∤) eqΔ₀₀) M M′ (false⊢[/]≈[/] Δ₀₀′ M≈M′)
             | N≈N′′ ← subst-[/-]≈[/-] (cong suc eqΔ₀₁) N N′ (false⊢[/]≈[/] (_ ∷ Δ₀₁) N≈N′)                                             = Δ₀Δ′~ & Δ₀₀Δ′₀∤ ⊢`let-return[ m≤m₁ ⇒-] M≈M′′ ⦂ ⊢↓ `in N≈N′′

false⊢[/]≈[/]                                                                          Δ₀ (`λ⦂-∘ M≈M′)                                  = `λ⦂-∘ M≈M′′
  where
    M≈M′′ = false⊢[/]≈[/] (_ ∷ Δ₀) M≈M′

false⊢[/]≈[/] {M = M `$ N}                        {M′ = M′ `$ N′}                      Δ₀ (Δ₀dΔ′~ ⊢ M≈M′ ⦂ ⊢⊸ `$ N≈N′)
  with ⊢S `⊸[ _ ] _ ← ⊢⊸
     | Δ₀₀ , Δ₀₁ , _ ∷ Δ′₀ , _ ∷ Δ′₁ , refl , refl , Δ₀~ , unusable ∷ Δ′~ ← ~⊞-preserves-++ Δ₀ Δ₀dΔ′~
    with eqΔ₀₀ , eqΔ₀₁ ← length-respects-~⊞ Δ₀~                                                                                         = Δ₀Δ′~ ⊢ M≈M′′ ⦂ ⊢⊸ `$ N≈N′′
  where
    Δ₀Δ′~ = ~⊞-++⁺ Δ₀~ Δ′~
    M≈M′′ = subst-[/-]≈[/-] eqΔ₀₀ M M′ (false⊢[/]≈[/] Δ₀₀ M≈M′)
    N≈N′′ = subst-[/-]≈[/-] eqΔ₀₁ N N′ (false⊢[/]≈[/] Δ₀₁ N≈N′)

false⊢[/]≈[/]                                                                          Δ₀ (`#_ {x = y} y∈)
  with y ℕ.≥? length Δ₀
...  | no  y≱
    with y∈′ ← <∧∈-++-++⇒∈-++ Δ₀ (_ ∷ []) y∈ (ℕ.≰⇒> y≱)                                                                                 = `# y∈′
...  | yes y≥
    with y ℕ.≟ length Δ₀
...    | yes refl with _ , _ , _ , () ← len∈-inversion Δ₀ y∈
...    | no  y≢
    with y> ← subst (y ℕ.≥_) (ℕ.+-comm 1 _) (ℕ.≤∧≢⇒< y≥ (≢-sym y≢))
      with y∈′ ← ≥∧∈-++-++⇒∈-++ Δ₀ (_ ∷ []) y∈ y>                                                                                       = `# y∈′

-- Substitution on a used variable preserves equivalence
true⊢[/]≈[/]ʳ : ∀ Δ₀ →
                Γ ~ Δ₀ ++ Δ′ ⊞ Γ₁ →
                ⊢[ m₀ ] Γ₁ →
                Γ₁ ⊢[ m₀ ] L ≈[≥ m′ ] L′ ⦂ S →
                ⊢[ m ] T ⦂⋆ →
                Δ₀ ++ (S , m₀ , true) ∷ Δ′ ⊢[ m ] M ≈[≥ m′ ] M′ ⦂ T →
                ----------------------------------------------------------------------------
                Γ ⊢[ m ] [ L /[ m₀ ] length Δ₀ ] M ≈[≥ m′ ] [ L′ /[ m₀ ] length Δ₀ ] M′ ⦂ T
true⊢[/]≈[/]ˡ : ∀ Δ₁ →
                Γ ~ Γ₀ ⊞ Δ₁ ++ Δ′ →
                ⊢[ m₀ ] Γ₀ →
                Γ₀ ⊢[ m₀ ] L ≈[≥ m′ ] L′ ⦂ S →
                ⊢[ m ] T ⦂⋆ →
                Δ₁ ++ (S , m₀ , true) ∷ Δ′ ⊢[ m ] M ≈[≥ m′ ] M′ ⦂ T →
                ----------------------------------------------------------------------------
                Γ ⊢[ m ] [ L /[ m₀ ] length Δ₁ ] M ≈[≥ m′ ] [ L′ /[ m₀ ] length Δ₁ ] M′ ⦂ T
true⊢[/]≈[/]ʳ                                                                           Δ₀ Γ~ ⊢Γ₁ L≈L′ ⊢T                  (`unit Δ₀dΔ′Del)
  with Δ₀Del , weakening Wk∈m₀ ∷ Δ′Del ← All.++⁻ Δ₀ Δ₀dΔ′Del                                                                                                            = `unit ΓDel
  where
    ΓDel = ~⊞⁻¹-preserves-is-all-del (All.++⁺ Δ₀Del Δ′Del) (⊢∧Wk≤⇒is-all-del ⊢Γ₁ ≤ₘ-refl Wk∈m₀) Γ~

true⊢[/]≈[/]ʳ                                                                           Δ₀ Γ~ ⊢Γ₁ L≈L′ (`↑[-⇒ _ ][ _ ] ⊢T) (`lift[≤ m′≤m ⇒-] M≈M′)                      = `lift[≤ m′≤m ⇒-] M≈M′′
  where
    M≈M′′ = true⊢[/]≈[/]ʳ Δ₀ Γ~ ⊢Γ₁ L≈L′ ⊢T M≈M′

true⊢[/]≈[/]ʳ                                                                           Δ₀ Γ~ ⊢Γ₁ L≈L′ (`↑[-⇒ _ ][ _ ] ⊢T) (`lift[≰ m′≰m ⇒-] ⊢M ⊢M′)
  with ⊢L , ⊢L′ ← ≈⇒⊢ L≈L′                                                                                                                                              = `lift[≰ m′≰m ⇒-] (true⊢[/]ʳ Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T ⊢M) (true⊢[/]ʳ Δ₀ Γ~ ⊢Γ₁ ⊢L′ ⊢T ⊢M′)

true⊢[/]≈[/]ʳ {M = `unlift[ _ ⇒ _ ] M}            {M′ = `unlift[ _ ⇒ _ ] M′}            Δ₀ Γ~ ⊢Γ₁ L≈L′ ⊢T                  (Δ₀dΔ′∤ ⊢`unlift[-⇒-] M≈M′ ⦂ ⊢↑)
  with _ , _ , refl , Δ₀∤ , d∤ ∷ Δ′∤ ← ∤-preserves-++ Δ₀ Δ₀dΔ′∤
    with Δ₀Δ′∤ ← ∤-++⁺ Δ₀∤ Δ′∤
       | eqΔ₀′ ← length-respects-∤ Δ₀∤
      with d∤
...      | keep m₁≤
        rewrite proj₂ (dec-yes (_ ≤?ₘ _) m₁≤)
          with _ , Γ∤ , Γ′~ ← ~⊞⁻¹-preserves-∤ Δ₀Δ′∤ (⊢∧≤⇒∤ ⊢Γ₁ m₁≤) Γ~
            with M≈M′′ ← subst-[/-]≈[/-] eqΔ₀′ M M′ (true⊢[/]≈[/]ʳ _ Γ′~ ⊢Γ₁ L≈L′ ⊢↑ M≈M′)                                                                              = Γ∤ ⊢`unlift[-⇒-] M≈M′′ ⦂ ⊢↑
...      | delete m₁≰ (weakening Wk∈m₀)
        rewrite dec-no (_ ≤?ₘ _) m₁≰
          with Γ₁Del ← ⊢∧Wk≤⇒is-all-del ⊢Γ₁ ≤ₘ-refl Wk∈m₀
             | M≈M′′ ← subst-[/-]≈[/-] eqΔ₀′ M M′ (false⊢[/]≈[/] _ M≈M′)                                                                                                = ~⊞-is-all-del∧⊢⇒≈ˡ Γ~ Γ₁Del (Δ₀Δ′∤ ⊢`unlift[-⇒-] M≈M′′ ⦂ ⊢↑)

true⊢[/]≈[/]ʳ {M = `return[ _ ⇒ _ ] M}            {M′ = `return[ _ ⇒ _ ] M′}            Δ₀ Γ~ ⊢Γ₁ L≈L′ (`↓[-⇒ _ ][ _ ] ⊢T) (Δ₀dΔ′∤ ⊢`return[-⇒-] M≈M′)
  with _ , _ , refl , Δ₀∤ , d∤ ∷ Δ′∤ ← ∤-preserves-++ Δ₀ Δ₀dΔ′∤
    with Δ₀Δ′∤ ← ∤-++⁺ Δ₀∤ Δ′∤
       | eqΔ₀′ ← length-respects-∤ Δ₀∤
      with d∤
...      | keep m₁≤
        rewrite proj₂ (dec-yes (_ ≤?ₘ _) m₁≤)
          with _ , Γ∤ , Γ′~ ← ~⊞⁻¹-preserves-∤ Δ₀Δ′∤ (⊢∧≤⇒∤ ⊢Γ₁ m₁≤) Γ~
            with M≈M′′ ← subst-[/-]≈[/-] eqΔ₀′ M M′ (true⊢[/]≈[/]ʳ _ Γ′~ ⊢Γ₁ L≈L′ ⊢T M≈M′)                                                                              = Γ∤ ⊢`return[-⇒-] M≈M′′
...      | delete m₁≰ (weakening Wk∈m₀)
        rewrite dec-no (_ ≤?ₘ _) m₁≰
          with Γ₁Del ← ⊢∧Wk≤⇒is-all-del ⊢Γ₁ ≤ₘ-refl Wk∈m₀
             | M≈M′′ ← subst-[/-]≈[/-] eqΔ₀′ M M′ (false⊢[/]≈[/] _ M≈M′)                                                                                                = ~⊞-is-all-del∧⊢⇒≈ˡ Γ~ Γ₁Del (Δ₀Δ′∤ ⊢`return[-⇒-] M≈M′′)

true⊢[/]≈[/]ʳ {M = `let-return[ m₁ ⇒ _ ] M `in N} {M′ = `let-return[ _ ⇒ _ ] M′ `in N′} Δ₀ Γ~ ⊢Γ₁ L≈L′ ⊢T                  (Δ₀dΔ′~ & Δ₀₀d₀Δ′₀∤ ⊢`let-return[ m≤m₁ ⇒-] M≈M′ ⦂ ⊢↓ `in N≈N′)
  with `↓[-⇒ _ ][ _ ] ⊢T₀ ← ⊢↓
     | Δ₀₀ , _ , _ , _ , refl , refl , Δ₀~ , d~ ∷ Δ′~ ← ~⊞-preserves-++ Δ₀ Δ₀dΔ′~
    with _ , _ , refl , Δ₀₀∤ , d₀∤ ∷ Δ′₀∤ ← ∤-preserves-++ Δ₀₀ Δ₀₀d₀Δ′₀∤
       | Δ₀Δ′~ ← ~⊞-++⁺ Δ₀~ Δ′~
       | eqΔ₀₀ , eqΔ₀₁ ← length-respects-~⊞ Δ₀~
      with Δ₀₀Δ′₀∤ ← ∤-++⁺ Δ₀₀∤ Δ′₀∤
         | eqΔ₀₀′ ← length-respects-∤ Δ₀₀∤
        with d~ | d₀∤
...        | contraction Co∈m₀ | keep m₁≤
          rewrite proj₂ (dec-yes (_ ≤?ₘ _) m₁≤)
            with _ , _ , Γ₂′~ , Γ₃′~ , Γ~′ ← ~⊞-contraction-assocˡ Γ~ Δ₀Δ′~ ⊢Γ₁ Co∈m₀
              with _ , Γ₀∤ , Γ₀′~ ← ~⊞⁻¹-preserves-∤ Δ₀₀Δ′₀∤ (⊢∧≤⇒∤ ⊢Γ₁ m₁≤) Γ₂′~
                 | N≈N′′ ← subst-[/-]≈[/-] (cong suc eqΔ₀₁) N N′ (true⊢[/]≈[/]ʳ _ (to-left ∷ Γ₃′~) ((⊢T₀ , unusable) ∷ ⊢Γ₁) (wk[-↑-]≈wk[-↑-] [] (unusable ∷ []) L≈L′) ⊢T N≈N′)
                with M≈M′′ ← subst-[/-]≈[/-] (trans eqΔ₀₀′ eqΔ₀₀) M M′ (true⊢[/]≈[/]ʳ _ Γ₀′~ ⊢Γ₁ L≈L′ ⊢↓ M≈M′) = Γ~′ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] M≈M′′ ⦂ ⊢↓ `in N≈N′′
...        | contraction Co∈m₀ | delete m₁≰ (weakening Wk∈m₀)
          rewrite dec-no (_ ≤?ₘ _) m₁≰
            with _ , _ , Γ₂′~ , Γ₃′~ , Γ~′ ← ~⊞-contraction-assocˡ Γ~ Δ₀Δ′~ ⊢Γ₁ Co∈m₀
               | _ , Γ₁∤ , Γ₁′Del ← is-all-del⇒∤ m₁ (⊢∧Wk≤⇒is-all-del ⊢Γ₁ ≤ₘ-refl Wk∈m₀)
              with _ , Γ₂′∤ , Γ₂″~ ← ~⊞⁻¹-preserves-∤ Δ₀₀Δ′₀∤ Γ₁∤ Γ₂′~
                 | N≈N′′ ← subst-[/-]≈[/-] (cong suc eqΔ₀₁) N N′ (true⊢[/]≈[/]ʳ _ (to-left ∷ Γ₃′~) ((⊢T₀ , unusable) ∷ ⊢Γ₁) (wk[-↑-]≈wk[-↑-] [] (unusable ∷ []) L≈L′) ⊢T N≈N′)
                 | M≈M′′ ← subst-[/-]≈[/-] (trans eqΔ₀₀′ eqΔ₀₀) M M′ (false⊢[/]≈[/] _ M≈M′)                                                = Γ~′ & Γ₂′∤ ⊢`let-return[ m≤m₁ ⇒-] ~⊞-is-all-del∧⊢⇒≈ˡ Γ₂″~ Γ₁′Del M≈M′′ ⦂ ⊢↓ `in N≈N′′
...        | to-left           | keep m₁≤
          rewrite proj₂ (dec-yes (_ ≤?ₘ _) m₁≤)
            with Γ₁′ , Γ₁′~ , Γ~′ ← ~⊞-assocʳ (~⊞-commute Γ~) Δ₀Δ′~
              with _ , Γ₁′∤ , Γ₁″~ ← ~⊞⁻¹-preserves-∤ (⊢∧≤⇒∤ ⊢Γ₁ m₁≤) Δ₀₀Δ′₀∤ Γ₁′~
                 | N≈N′′ ← subst-[/-]≈[/-] (cong suc eqΔ₀₁) N N′ (false⊢[/]≈[/] _ N≈N′)
                with M≈M′′ ← subst-[/-]≈[/-] (trans eqΔ₀₀′ eqΔ₀₀) M M′ (true⊢[/]≈[/]ˡ _ Γ₁″~ ⊢Γ₁ L≈L′ ⊢↓ M≈M′) = Γ~′ & Γ₁′∤ ⊢`let-return[ m≤m₁ ⇒-] M≈M′′ ⦂ ⊢↓ `in N≈N′′
...        | to-left           | delete m₁≰ (weakening Wk∈m₀)
          rewrite dec-no (_ ≤?ₘ _) m₁≰
            with Γ₁′ , Γ₁′~ , Γ~′ ← ~⊞-assocʳ (~⊞-commute Γ~) Δ₀Δ′~
              with _ , Γ₁∤ , Γ₁′Del ← is-all-del⇒∤ m₁ (⊢∧Wk≤⇒is-all-del ⊢Γ₁ ≤ₘ-refl Wk∈m₀)
                with _ , Γ₁′∤ , Γ₁″~ ← ~⊞⁻¹-preserves-∤ Γ₁∤ Δ₀₀Δ′₀∤ Γ₁′~
                   | N≈N′′ ← subst-[/-]≈[/-] (cong suc eqΔ₀₁) N N′ (false⊢[/]≈[/] _ N≈N′)
                   | M≈M′′ ← subst-[/-]≈[/-] (trans eqΔ₀₀′ eqΔ₀₀) M M′ (false⊢[/]≈[/] _ M≈M′) = Γ~′ & Γ₁′∤ ⊢`let-return[ m≤m₁ ⇒-] ~⊞-is-all-del∧⊢⇒≈ʳ Γ₁″~ Γ₁′Del M≈M′′ ⦂ ⊢↓ `in N≈N′′
...        | to-right          | keep m₁≤
          rewrite proj₂ (dec-yes (_ ≤?ₘ _) m₁≤)
            with Γ₁′ , Γ₁′~ , Γ~′ ← ~⊞-assocˡ Γ~ Δ₀Δ′~
              with N≈N′′ ← subst-[/-]≈[/-] (cong suc eqΔ₀₁) N N′ (true⊢[/]≈[/]ʳ _ (to-left ∷ Γ₁′~) ((⊢T₀ , unusable) ∷ ⊢Γ₁) (wk[-↑-]≈wk[-↑-] [] (unusable ∷ []) L≈L′) ⊢T N≈N′)
                 | M≈M′′ ← subst-[/-]≈[/-] (trans eqΔ₀₀′ eqΔ₀₀) M M′ (false⊢[/]≈[/] _ M≈M′) = Γ~′ & Δ₀₀Δ′₀∤ ⊢`let-return[ m≤m₁ ⇒-] M≈M′′ ⦂ ⊢↓ `in N≈N′′
...        | to-right          | delete m₁≰ unusable
          rewrite dec-no (_ ≤?ₘ _) m₁≰
            with Γ₁′ , Γ₁′~ , Γ~′ ← ~⊞-assocˡ Γ~ Δ₀Δ′~
              with N≈N′′ ← subst-[/-]≈[/-] (cong suc eqΔ₀₁) N N′ (true⊢[/]≈[/]ʳ _ (to-left ∷ Γ₁′~) ((⊢T₀ , unusable) ∷ ⊢Γ₁) (wk[-↑-]≈wk[-↑-] [] (unusable ∷ []) L≈L′) ⊢T N≈N′)
                 | M≈M′′ ← subst-[/-]≈[/-] (trans eqΔ₀₀′ eqΔ₀₀) M M′ (false⊢[/]≈[/] _ M≈M′)                                 = Γ~′ & Δ₀₀Δ′₀∤ ⊢`let-return[ m≤m₁ ⇒-] M≈M′′ ⦂ ⊢↓ `in N≈N′′

true⊢[/]≈[/]ʳ                                                                           Δ₀ Γ~ ⊢Γ₁ L≈L′ (⊢T₀ `⊸[ _ ] ⊢T₁)   (`λ⦂-∘ M≈M′)                                 = `λ⦂-∘ L≈L′′
  where
    L≈L′′ = true⊢[/]≈[/]ʳ (_ ∷ Δ₀) (to-left ∷ Γ~) ((⊢T₀ , unusable) ∷ ⊢Γ₁) (wk[-↑-]≈wk[-↑-] [] (unusable ∷ []) L≈L′) ⊢T₁ M≈M′

true⊢[/]≈[/]ʳ {M = M `$ N}                        {M′ = M′ `$ N′}                       Δ₀ Γ~ ⊢Γ₁ L≈L′ ⊢T                  (Δ₀dΔ′~ ⊢ M≈M′ ⦂ ⊢⊸ `$ N≈N′)
  with ⊢T₀ `⊸[ _ ] _ ← ⊢⊸
     | _ , _ , _ , _ , refl , refl , Δ₀~ , d~ ∷ Δ′~ ← ~⊞-preserves-++ Δ₀ Δ₀dΔ′~
    with Δ₀Δ′~ ← ~⊞-++⁺ Δ₀~ Δ′~
       | eqΔ₀₀ , eqΔ₀₁ ← length-respects-~⊞ Δ₀~
      with d~
...      | contraction Co∈m₀
        with _ , _ , Γ₂′~ , Γ₃′~ , Γ~′ ← ~⊞-contraction-assocˡ Γ~ Δ₀Δ′~ ⊢Γ₁ Co∈m₀
          with M≈M′′ ← subst-[/-]≈[/-] eqΔ₀₀ M M′ (true⊢[/]≈[/]ʳ _ Γ₂′~ ⊢Γ₁ L≈L′ ⊢⊸ M≈M′)
             | N≈N′′ ← subst-[/-]≈[/-] eqΔ₀₁ N N′ (true⊢[/]≈[/]ʳ _ Γ₃′~ ⊢Γ₁ L≈L′ ⊢T₀ N≈N′)                                                                              = Γ~′ ⊢ M≈M′′ ⦂ ⊢⊸ `$ N≈N′′
...      | to-left
        with _ , Γ₁′~ , Γ~′ ← ~⊞-assocʳ (~⊞-commute Γ~) Δ₀Δ′~
          with M≈M′′ ← subst-[/-]≈[/-] eqΔ₀₀ M M′ (true⊢[/]≈[/]ˡ _ Γ₁′~ ⊢Γ₁ L≈L′ ⊢⊸ M≈M′)
             | N≈N′′ ← subst-[/-]≈[/-] eqΔ₀₁ N N′ (false⊢[/]≈[/] _ N≈N′)                                                                                                = Γ~′ ⊢ M≈M′′ ⦂ ⊢⊸ `$ N≈N′′
...      | to-right
        with _ , Γ₁′~ , Γ~′ ← ~⊞-assocˡ Γ~ Δ₀Δ′~
          with M≈M′′ ← subst-[/-]≈[/-] eqΔ₀₀ M M′ (false⊢[/]≈[/] _ M≈M′)
             | N≈N′′ ← subst-[/-]≈[/-] eqΔ₀₁ N N′ (true⊢[/]≈[/]ʳ _ Γ₁′~ ⊢Γ₁ L≈L′ ⊢T₀ N≈N′)                                                                              = Γ~′ ⊢ M≈M′′ ⦂ ⊢⊸ `$ N≈N′′

true⊢[/]≈[/]ʳ                                                                           Δ₀ Γ~ ⊢Γ₁ L≈L′ ⊢T                  (`#_ {x = y} y∈)
  with y ℕ.≥? length Δ₀
...  | no  y≱
    with y< ← ℕ.≰⇒> y≱
      with weakening Wk∈m₀ ∷ _ ← <∧∈-++⇒is-all-del Δ₀ y∈ y<
         | y∈′ ← <∧∈-++-++⇒∈-++ Δ₀ (_ ∷ []) y∈ y<
        with y∈″ ← ~⊞-is-all-del∧∈⇒∈ˡ Γ~ (⊢∧Wk≤⇒is-all-del ⊢Γ₁ ≤ₘ-refl Wk∈m₀) y∈′                                                                                       = `# y∈″
...  | yes y≥
    with y ℕ.≟ length Δ₀
...    | yes refl
      with Δ₀Δ′Del , refl , refl , refl ← len∈-inversion Δ₀ y∈                                                                                                          = ~⊞-is-all-del∧⊢⇒≈ʳ Γ~ Δ₀Δ′Del L≈L′
...    | no  y≢
      with y∈′ ← subst (_ ⦂[ _ ] _ ∈_) (sym (List.++-assoc Δ₀ (_ ∷ []) _)) y∈
         | y> ← subst (y ℕ.≥_) (ℕ.+-comm 1 _) (ℕ.≤∧≢⇒< y≥ (≢-sym y≢))
        with y∈″ ← ≥∧∈-++-++⇒∈-++ Δ₀ (_ ∷ []) y∈ y>
           | Δ₀dDel ← ≥∧∈-++⇒is-all-del _ y∈′ (subst (y ℕ.≥_) (sym (List.length-++ Δ₀)) y>)
          with weakening Wk∈m₀ ∷ _ ← All.++⁻ʳ Δ₀ Δ₀dDel
            with y∈‴ ← ~⊞-is-all-del∧∈⇒∈ˡ Γ~ (⊢∧Wk≤⇒is-all-del ⊢Γ₁ ≤ₘ-refl Wk∈m₀) y∈″                                                                                   = `# y∈‴

true⊢[/]≈[/]ˡ Δ₁ Γ~ ⊢Γ₀ L≈L′ ⊢T M≈M′ = true⊢[/]≈[/]ʳ Δ₁ (~⊞-commute Γ~) ⊢Γ₀ L≈L′ ⊢T M≈M′


-- Properties of stepping relations about equivalence
--

WeakNorm≈⟶ : ⊢[ m ] Γ →
             ⊢[ m ] S ⦂⋆ →
             Γ ⊢[ m ] L ≈[≥ m′ ] M ⦂ S →
             WeakNorm L →
             M ⟶ M′ →
             ----------------------------
             Γ ⊢[ m ] L ≈[≥ m′ ] M′ ⦂ S
DeferredTerm≈⟶[≤] : ⊢[ m ] Γ →
                    ⊢[ m ] S ⦂⋆ →
                    Γ ⊢[ m ] L ≈[≥ m′ ] M ⦂ S →
                    DeferredTerm[ m₀ ≤] L →
                    M ⟶[ m₀ ≤] M′ →
                    ----------------------------
                    Γ ⊢[ m ] L ≈[≥ m′ ] M′ ⦂ S

WeakNorm≈⟶ ⊢Γ (`↑[-⇒ m₀<m ][ _ ] ⊢S) (`lift[≤ m′≤m₀ ⇒-] L≈M)                                                   (`lift[ _ ⇒ _ ] WL)                       (ξ-`lift[-⇒-] M⟶[≤])        = `lift[≤ m′≤m₀ ⇒-] (DeferredTerm≈⟶[≤] (⊢∧<ₘ⇒⊢ ⊢Γ m₀<m) ⊢S L≈M WL M⟶[≤])
WeakNorm≈⟶ ⊢Γ (`↑[-⇒ m₀<m ][ _ ] ⊢S) (`lift[≰ m′≰m₀ ⇒-] ⊢L ⊢M)                                                 VL                                        (ξ-`lift[-⇒-] M⟶[≤])        = `lift[≰ m′≰m₀ ⇒-] ⊢L (preservation[≤] (⊢∧<ₘ⇒⊢ ⊢Γ m₀<m) ⊢S ⊢M M⟶[≤])
WeakNorm≈⟶ ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] L≈M ⦂ ⊢↑)                                               (`neut (`unlift[ _ ⇒ _ ] NL))             (ξ-`unlift[-⇒-] M⟶)         = Γ∤ ⊢`unlift[-⇒-] (WeakNorm≈⟶ (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ L≈M (`neut NL) M⟶) ⦂ ⊢↑
WeakNorm≈⟶ ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[≤ m′≤m ⇒-] L≈M ⦂ ⊢↑)                              (`neut (`unlift[ _ ⇒ _ ] ()))             (β-`↑ WM)
WeakNorm≈⟶ ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[≰ m′≰m ⇒-] ⊢L ⊢M ⦂ ⊢↑)                            (`neut (`unlift[ _ ⇒ _ ] ()))             (β-`↑ WM)
WeakNorm≈⟶ ⊢Γ (`↓[-⇒ _ ][ _ ] ⊢S)    (Γ∤ ⊢`return[-⇒-] L≈M)                                                    (`return[ _ ⇒ _ ] VL)                     (ξ-`return[-⇒-] M⟶)         = Γ∤ ⊢`return[-⇒-] (WeakNorm≈⟶ (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S L≈M VL M⟶)
WeakNorm≈⟶ ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁)                    (`neut (`let-return[ x ⇒ _ ] NL₀ `in L₁)) ξ-`let-return[-⇒-] M₀⟶ `in- = Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] WeakNorm≈⟶ (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) ⊢↓ L₀≈M₀ (`neut NL₀) M₀⟶ ⦂ ⊢↓ `in L₁≈M₁
WeakNorm≈⟶ ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] Γ₀′∤ ⊢`return[-⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁) (`neut (`let-return[ _ ⇒ _ ] () `in _))   (β-`↓ VM₀)
WeakNorm≈⟶ ⊢Γ ⊢S                     (Γ~ ⊢ L₀≈M₀ ⦂ ⊢⊸ `$ L₁≈M₁)                                                (`neut (NL₀ `$ VL₁))                      ξ- M₀⟶ `$?                  = Γ~ ⊢ WeakNorm≈⟶ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) ⊢⊸ L₀≈M₀ (`neut NL₀) M₀⟶ ⦂ ⊢⊸ `$ L₁≈M₁
WeakNorm≈⟶ ⊢Γ ⊢S                     (Γ~ ⊢ L₀≈M₀ ⦂ ⊢⊸@(⊢T `⊸[ _ ] _) `$ L₁≈M₁)                                 (`neut (NL₀ `$ VL₁))                      (ξ-! VM₀ `$ M₁⟶)            = Γ~ ⊢ L₀≈M₀ ⦂ ⊢⊸ `$ WeakNorm≈⟶ (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢T L₁≈M₁ VL₁ M₁⟶
WeakNorm≈⟶ ⊢Γ ⊢S                     (Γ~ ⊢ `λ⦂-∘ L₀≈M₀ ⦂ ⊢⊸ `$ L₁≈M₁)                                          (`neut (() `$ VL₁))                       (β-`⊸ VM₁)

DeferredTerm≈⟶[≤] ⊢Γ (`↑[-⇒ m₀<m ][ _ ] ⊢S) (`lift[≤ m′≤m₀ ⇒-] L≈M)                                (`lift[ _ ⇒ _ ] WL)                     (ξ-`lift[-⇒-] M⟶[≤])                        = `lift[≤ m′≤m₀ ⇒-] (DeferredTerm≈⟶[≤] (⊢∧<ₘ⇒⊢ ⊢Γ m₀<m) ⊢S L≈M WL M⟶[≤])
DeferredTerm≈⟶[≤] ⊢Γ (`↑[-⇒ m₀<m ][ _ ] ⊢S) (`lift[≰ m′≰m₀ ⇒-] ⊢L ⊢M)                              WL                                      (ξ-`lift[-⇒-] M⟶[≤])                        = `lift[≰ m′≰m₀ ⇒-] ⊢L (preservation[≤] (⊢∧<ₘ⇒⊢ ⊢Γ m₀<m) ⊢S ⊢M M⟶[≤])
DeferredTerm≈⟶[≤] ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] L≈M ⦂ ⊢↑)                            WL                                      (ξ-`unlift[≰ m₀≰m₁ ⇒-] M⟶[≤])
  -- For some reason direct pattern match in the head gives an incomplete pattern error.
  with WL
...  | `unlift[≰ _ ⇒ _ ] WL                                                                                                                                                            = Γ∤ ⊢`unlift[-⇒-] DeferredTerm≈⟶[≤] (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ L≈M WL M⟶[≤] ⦂ ⊢↑
...  | `unlift[≤ m₀≤m₁ ⇒ _ ] VL                                                                                                                                                        with () ← m₀≰m₁ m₀≤m₁
DeferredTerm≈⟶[≤] ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] L≈M ⦂ ⊢↑)                            WL                                      (ξ-`unlift[≤ m₀≤m₁ ⇒-] M⟶)
  -- For some reason direct pattern match in the head gives an incomplete pattern error.
  with WL
...  | `unlift[≰ m₀≰m₁ ⇒ _ ] WL                                                                                                                                                        with () ← m₀≰m₁ m₀≤m₁
...  | `unlift[≤ _ ⇒ _ ] VL                                                                                                                                                            = Γ∤ ⊢`unlift[-⇒-] WeakNorm≈⟶ (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ L≈M VL M⟶ ⦂ ⊢↑
DeferredTerm≈⟶[≤] ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[≤ _ ⇒-] L≈M ⦂ ⊢↑)              (`unlift[≰ m₀≰m₁ ⇒ _ ] WL)              (β-`↑ m₀≤m₁ WM)                             with () ← m₀≰m₁ m₀≤m₁
DeferredTerm≈⟶[≤] ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[≰ _ ⇒-] ⊢L ⊢M ⦂ ⊢↑)            (`unlift[≰ m₀≰m₁ ⇒ _ ] WL)              (β-`↑ m₀≤m₁ WM)                             with () ← m₀≰m₁ m₀≤m₁
DeferredTerm≈⟶[≤] ⊢Γ (`↓[-⇒ _ ][ _ ] ⊢S)    (Γ∤ ⊢`return[-⇒-] L≈M)                                 (`return[≰ m₀≰m₁ ⇒ _ ] WL)              (ξ-`return[≰ _ ⇒-] M⟶[≤])                   = Γ∤ ⊢`return[-⇒-] (DeferredTerm≈⟶[≤] (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S L≈M WL M⟶[≤])
DeferredTerm≈⟶[≤] ⊢Γ (`↓[-⇒ _ ][ _ ] ⊢S)    (Γ∤ ⊢`return[-⇒-] L≈M)                                 (`return[≤ m₀≤m₁ ⇒ _ ] VL)              (ξ-`return[≰ m₀≰m₁ ⇒-] M⟶[≤])               with () ← m₀≰m₁ m₀≤m₁
DeferredTerm≈⟶[≤] ⊢Γ (`↓[-⇒ _ ][ _ ] ⊢S)    (Γ∤ ⊢`return[-⇒-] L≈M)                                 (`return[≰ m₀≰m₁ ⇒ _ ] WL)              (ξ-`return[≤ m₀≤m₁ ⇒-] M⟶)                  with () ← m₀≰m₁ m₀≤m₁
DeferredTerm≈⟶[≤] ⊢Γ (`↓[-⇒ _ ][ _ ] ⊢S)    (Γ∤ ⊢`return[-⇒-] L≈M)                                 (`return[≤ m₀≤m₁ ⇒ _ ] VL)              (ξ-`return[≤ _ ⇒-] M⟶)                      = Γ∤ ⊢`return[-⇒-] WeakNorm≈⟶ (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S L≈M VL M⟶
DeferredTerm≈⟶[≤] ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁) (`let-return[≰ m₀≰m₁ ⇒ _ ] WL₀ `in WL₁) ξ-`let-return[≰ _ ⇒-] M₀⟶[≤] `in?           = Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] DeferredTerm≈⟶[≤] (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) ⊢↓ L₀≈M₀ WL₀ M₀⟶[≤] ⦂ ⊢↓ `in L₁≈M₁
DeferredTerm≈⟶[≤] ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁) (`let-return[≰ m₀≰m₁ ⇒ _ ] WL₀ `in WL₁) ξ-`let-return[≤ m₀≤m₁ ⇒-] M₀⟶ `in?          with () ← m₀≰m₁ m₀≤m₁
DeferredTerm≈⟶[≤] ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁) (`let-return[≤ m₀≤m₁ ⇒ _ ] VL₀ `in WL₁) ξ-`let-return[≰ m₀≰m₁ ⇒-] M₀⟶[≤] `in?       with () ← m₀≰m₁ m₀≤m₁
DeferredTerm≈⟶[≤] ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁) (`let-return[≤ m₀≤m₁ ⇒ _ ] VL₀ `in WL₁) ξ-`let-return[≤ _ ⇒-] M₀⟶ `in?              = Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] WeakNorm≈⟶ (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) ⊢↓ L₀≈M₀ VL₀ M₀⟶ ⦂ ⊢↓ `in L₁≈M₁ 
DeferredTerm≈⟶[≤] ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁) (`let-return[≰ m₀≰m₁ ⇒ _ ] WL₀ `in WL₁) (ξ-`let-return[≰ _ ⇒-]! WM₀ `in M₁⟶[≤])
  with `↓[-⇒ m₁<m₀ ][ _ ] ⊢T ← ⊢↓                                                                                                                                                       = Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in DeferredTerm≈⟶[≤] ((⊢T , valid (≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m₁<m₀))) ∷ (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~)) ⊢S L₁≈M₁ WL₁ M₁⟶[≤]
DeferredTerm≈⟶[≤] ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁) (`let-return[≰ m₀≰m₁ ⇒ _ ] VL₀ `in WL₁) (ξ-`let-return[≤ m₀≤m₁ ⇒-]! VM₀ `in M₁⟶[≤]) with () ← m₀≰m₁ m₀≤m₁
DeferredTerm≈⟶[≤] ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁) (`let-return[≤ m₀≤m₁ ⇒ _ ] WL₀ `in WL₁) (ξ-`let-return[≰ m₀≰m₁ ⇒-]! WM₀ `in M₁⟶[≤]) with () ← m₀≰m₁ m₀≤m₁
DeferredTerm≈⟶[≤] ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁) (`let-return[≤ m₀≤m₁ ⇒ _ ] VL₀ `in WL₁) (ξ-`let-return[≤ _ ⇒-]! VM₀ `in M₁⟶[≤])
  with `↓[-⇒ m₁<m₀ ][ _ ] ⊢T ← ⊢↓                                                                                                                                = Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in DeferredTerm≈⟶[≤] ((⊢T , valid (≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m₁<m₀))) ∷ (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~)) ⊢S L₁≈M₁ WL₁ M₁⟶[≤]
DeferredTerm≈⟶[≤] ⊢Γ (⊢T `⊸[ _ ] ⊢S)        (`λ⦂-∘ L≈M)                                            (`λ⦂[ _ ] _ ∘ WL)                       (ξ-`λ⦂[-]-∘ M⟶[≤])                  = `λ⦂-∘ DeferredTerm≈⟶[≤] ((⊢T , valid ≤ₘ-refl) ∷ ⊢Γ) ⊢S L≈M WL M⟶[≤]
DeferredTerm≈⟶[≤] ⊢Γ ⊢S                     (Γ~ ⊢ L₀≈M₀ ⦂ ⊢⊸ `$ L₁≈M₁)                             (WL₀ `$ WL₁)                            ξ- M₀⟶[≤] `$?                       = Γ~ ⊢ DeferredTerm≈⟶[≤] (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) ⊢⊸ L₀≈M₀ WL₀ M₀⟶[≤] ⦂ ⊢⊸ `$ L₁≈M₁
DeferredTerm≈⟶[≤] ⊢Γ ⊢S                     (Γ~ ⊢ L₀≈M₀ ⦂ ⊢⊸@(⊢T `⊸[ _ ] _) `$ L₁≈M₁)              (WL₀ `$ WL₁)                            (ξ-! WM₀ `$ M₁⟶[≤])                 = Γ~ ⊢ L₀≈M₀ ⦂ ⊢⊸ `$ DeferredTerm≈⟶[≤] (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢T L₁≈M₁ WL₁ M₁⟶[≤]

WeakNorm≈⟶* : ⊢[ m ] Γ →
              ⊢[ m ] S ⦂⋆ →
              Γ ⊢[ m ] L ≈[≥ m′ ] M ⦂ S →
              WeakNorm L →
              M ⟶* M′ →
              ----------------------------
              Γ ⊢[ m ] L ≈[≥ m′ ] M′ ⦂ S
WeakNorm≈⟶* ⊢Γ ⊢S L≈M VL ε = L≈M
WeakNorm≈⟶* ⊢Γ ⊢S L≈M VL (M⟶ ◅ M⟶*) = WeakNorm≈⟶* ⊢Γ ⊢S (WeakNorm≈⟶ ⊢Γ ⊢S L≈M VL M⟶) VL M⟶*

DeferredTerm≈⟶[≤]* : ⊢[ m ] Γ →
                     ⊢[ m ] S ⦂⋆ →
                     Γ ⊢[ m ] L ≈[≥ m′ ] M ⦂ S →
                     DeferredTerm[ m₀ ≤] L →
                     M ⟶[ m₀ ≤]* M′ →
                     ----------------------------
                     Γ ⊢[ m ] L ≈[≥ m′ ] M′ ⦂ S
DeferredTerm≈⟶[≤]* ⊢Γ ⊢S L≈M WL ε = L≈M
DeferredTerm≈⟶[≤]* ⊢Γ ⊢S L≈M WL (M⟶[≤] ◅ M′⟶[≤]*) = DeferredTerm≈⟶[≤]* ⊢Γ ⊢S (DeferredTerm≈⟶[≤] ⊢Γ ⊢S L≈M WL M⟶[≤]) WL M′⟶[≤]*

-- Diamond property modulo _⊢[_]_≈[≥_]_
--
≈-diamond : m′ ≤ₘ m →
            ⊢[ m ] Γ →
            ⊢[ m ] S ⦂⋆ →
            Γ ⊢[ m ] L ≈[≥ m′ ] M ⦂ S →
            L ⟶ L′ →
            M ⟶ M′ →
            halt L′ →
            halt M′ →
            -------------------------------------------
            ∃₂ (λ L″ M″ → L′ ⟶* L″
                        × M′ ⟶* M″
                        × Γ ⊢[ m ] L″ ≈[≥ m′ ] M″ ⦂ S)
≈-diamond[≤] : m′ ≤ₘ m →
               ⊢[ m ] Γ →
               ⊢[ m ] S ⦂⋆ →
               Γ ⊢[ m ] L ≈[≥ m′ ] M ⦂ S →
               L ⟶[ m″ ≤] L′ →
               M ⟶[ m″ ≤] M′ →
               halt[ m″ ≤] L′ →
               halt[ m″ ≤] M′ →
               -------------------------------------------
               ∃₂ (λ L″ M″ → L′ ⟶[ m″ ≤]* L″
                           × M′ ⟶[ m″ ≤]* M″
                           × Γ ⊢[ m ] L″ ≈[≥ m′ ] M″ ⦂ S)

≈-diamond m′≤m ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] L≈M ⦂ ⊢↑)                                   (ξ-`unlift[-⇒-] L⟶)                          (ξ-`unlift[-⇒-] M⟶)                          huL′  huM′
  with `↑[-⇒ m<m₀ ][ _ ] _ ← ⊢↑
    with m′≤m₀ ← ≤ₘ-trans m′≤m (<ₘ⇒≤ₘ m<m₀)
       | hL′ ← halt-`unlift-inversion huL′
       | hM′ ← halt-`unlift-inversion huM′
      with _ , _ , L′⟶* , M′⟶* , L″≈M″ ← ≈-diamond m′≤m₀ (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ L≈M L⟶ M⟶ hL′ hM′                                                                                                                  = -, -, ξ-of-⟶* `unlift[ _ ⇒ _ ] ξ-`unlift[-⇒-] L′⟶*
                                                                                                                                                                                                             , ξ-of-⟶* `unlift[ _ ⇒ _ ] ξ-`unlift[-⇒-] M′⟶*
                                                                                                                                                                                                             , Γ∤ ⊢`unlift[-⇒-] L″≈M″ ⦂ ⊢↑
≈-diamond m′≤m ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[≤ _ ⇒-] L≈M ⦂ ⊢↑)                     (ξ-`unlift[-⇒-] (ξ-`lift[-⇒-] L⟶[≤]))        (β-`↑ WM)                                    hulL′ hM′
  with `↑[-⇒ m<m₀ ][ _ ] _ ← ⊢↑
     | _ , L′⟶[≤]* , WL″ ← halt-`lift-inversion (halt-`unlift-inversion hulL′)                                                                                                                               = -, -, ξ-of-⟶* `unlift[ _ ⇒ _ ] ξ-`unlift[-⇒-]
                                                                                                                                                                                                                 (ξ-of-↝*-⟶* _⟶[ _ ≤]_ `lift[ _ ⇒ _ ] ξ-`lift[-⇒-] L′⟶[≤]*)
                                                                                                                                                                                                                 ◅◅ β-`↑ WL″ ◅ ε
                                                                                                                                                                                                             , ε
                                                                                                                                                                                                             , ∤⁻¹-preserves-≈ [] (≈-sym (DeferredTerm≈⟶[≤]* (⊢∧<ₘ⇒⊢ (⊢∧∤⇒⊢ ⊢Γ Γ∤) m<m₀) ⊢S (≈-sym L≈M) WM (L⟶[≤] ◅ L′⟶[≤]*))) Γ∤
≈-diamond m′≤m ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[≤ _ ⇒-] L≈M ⦂ ⊢↑)                     (β-`↑ WL)                                    (ξ-`unlift[-⇒-] (ξ-`lift[-⇒-] M⟶[≤]))        hL′   hulM′
  with `↑[-⇒ m<m₀ ][ _ ] _ ← ⊢↑
     | _ , M′⟶[≤]* , WM″ ← halt-`lift-inversion (halt-`unlift-inversion hulM′)                                                                                                                               = -, -, ε
                                                                                                                                                                                                             , ξ-of-⟶* `unlift[ _ ⇒ _ ] ξ-`unlift[-⇒-]
                                                                                                                                                                                                                 (ξ-of-↝*-⟶* _⟶[ _ ≤]_ `lift[ _ ⇒ _ ] ξ-`lift[-⇒-] M′⟶[≤]*)
                                                                                                                                                                                                                 ◅◅ β-`↑ WM″ ◅ ε
                                                                                                                                                                                                             , ∤⁻¹-preserves-≈ [] (DeferredTerm≈⟶[≤]* (⊢∧<ₘ⇒⊢ (⊢∧∤⇒⊢ ⊢Γ Γ∤) m<m₀) ⊢S L≈M WL (M⟶[≤] ◅ M′⟶[≤]*)) Γ∤
≈-diamond m′≤m ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[≤ _ ⇒-] L≈M ⦂ ⊢↑)                     (β-`↑ _)                                     (β-`↑ _)                                     hL′   hM′   = -, -, ε
                                                                                                                                                                                                             , ε
                                                                                                                                                                                                             , ∤⁻¹-preserves-≈ [] L≈M Γ∤
≈-diamond m′≤m ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[≰ m′≰m ⇒-] _ _ ⦂ ⊢↑)                  L⟶                                           M⟶                                           hL′   hM′   with () ← m′≰m m′≤m
≈-diamond m′≤m ⊢Γ (`↓[-⇒ m<m₀ ][ _ ] ⊢S) (Γ∤ ⊢`return[-⇒-] L≈M)                                        (ξ-`return[-⇒-] L⟶)                          (ξ-`return[-⇒-] M⟶)                          hrL′  hrM′
  with m′≤m₀ ← ≤ₘ-trans m′≤m (<ₘ⇒≤ₘ m<m₀)
     | hL′ ← halt-`return-inversion hrL′
     | hM′ ← halt-`return-inversion hrM′
    with _ , _ , L′⟶* , M′⟶* , L″≈M″ ← ≈-diamond m′≤m₀ (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S L≈M L⟶ M⟶ hL′ hM′                                                                                                                    = -, -, ξ-of-⟶* `return[ _ ⇒ _ ] ξ-`return[-⇒-] L′⟶*
                                                                                                                                                                                                             , ξ-of-⟶* `return[ _ ⇒ _ ] ξ-`return[-⇒-] M′⟶*
                                                                                                                                                                                                             , Γ∤ ⊢`return[-⇒-] L″≈M″
≈-diamond m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁)                   ξ-`let-return[-⇒-] L₀⟶ `in-                  ξ-`let-return[-⇒-] M₀⟶ `in-                  hL′   hM′
  with hL₀′ ← halt-`let-return-`in-inversion hL′
     | hM₀′ ← halt-`let-return-`in-inversion hM′
    with _ , _ , L₀′⟶* , M₀′⟶* , L₀″≈M₀″ ← ≈-diamond (≤ₘ-trans m′≤m m≤m₁) (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) ⊢↓ L₀≈M₀ L₀⟶ M₀⟶ hL₀′ hM₀′                                                                                                       = -, -, ξ-of-⟶* (`let-return[ _ ⇒ _ ]_`in _) ξ-`let-return[-⇒-]_`in- L₀′⟶*
                                                                                                                                                                                                             , ξ-of-⟶* (`let-return[ _ ⇒ _ ]_`in _) ξ-`let-return[-⇒-]_`in- M₀′⟶*
                                                                                                                                                                                                             , (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀″≈M₀″ ⦂ ⊢↓ `in L₁≈M₁)
≈-diamond m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] Γ₀′∤ ⊢`return[-⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁) ξ-`let-return[-⇒-] (ξ-`return[-⇒-] L₀⟶) `in- (β-`↓ VM₀)                                   hL′   hM′
  with `↓[-⇒ m<m₀ ][ _ ] ⊢T ← ⊢↓
     | _ , L₀′⟶* , VL₀″ ← halt-`return-inversion (halt-`let-return-`in-inversion hL′)
     | Γ₀₁ , Γ₀~ , Γ₀₁Del ← ∤⇒~⊞-is-all-delʳ Γ₀∤
     | Γ₀′₁ , Γ₀′~ , Γ₀′₁Del ← ∤⇒~⊞-is-all-delʳ Γ₀′∤
    with Γ″ , Γ″~ , Γ~′ ← ~⊞-assocˡ Γ~ Γ₀~
      with Γ‴ , Γ‴~ , Γ~″ ← ~⊞-assocˡ Γ~′ Γ₀′~                                                                                                                                                               = -, -, ξ-of-⟶* (`let-return[ _ ⇒ _ ]_`in _) ξ-`let-return[-⇒-]_`in-
                                                                                                                                                                                                                 (ξ-of-⟶* `return[ _ ⇒ _ ] ξ-`return[-⇒-] L₀′⟶*)
                                                                                                                                                                                                                 ◅◅ β-`↓ VL₀″ ◅ ε
                                                                                                                                                                                                             , ε
                                                                                                                                                                                                             , true⊢[/]≈[/]ˡ
                                                                                                                                                                                                                 []
                                                                                                                                                                                                                 Γ~″
                                                                                                                                                                                                                 (⊢∧∤⇒⊢ (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) Γ₀′∤)
                                                                                                                                                                                                                 (≈-sym (WeakNorm≈⟶* (⊢∧∤⇒⊢ (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) Γ₀′∤) ⊢T (≈-sym L₀≈M₀) VM₀ (L₀⟶ ◅ L₀′⟶*)))
                                                                                                                                                                                                                 ⊢S
                                                                                                                                                                                                                 (~⊞-is-all-del∧⊢⇒≈ʳ (to-right ∷ Γ‴~) (unusable ∷ Γ₀′₁Del)
                                                                                                                                                                                                                    (~⊞-is-all-del∧⊢⇒≈ʳ (to-right ∷ Γ″~) (unusable ∷ Γ₀₁Del) L₁≈M₁))
≈-diamond m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] Γ₀′∤ ⊢`return[-⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁) (β-`↓ VL₀)                                   ξ-`let-return[-⇒-] (ξ-`return[-⇒-] M₀⟶) `in- hL′   hM′
  with `↓[-⇒ m<m₀ ][ _ ] ⊢T ← ⊢↓
     | _ , M₀′⟶* , VM₀″ ← halt-`return-inversion (halt-`let-return-`in-inversion hM′)
     | Γ₀₁ , Γ₀~ , Γ₀₁Del ← ∤⇒~⊞-is-all-delʳ Γ₀∤
     | Γ₀′₁ , Γ₀′~ , Γ₀′₁Del ← ∤⇒~⊞-is-all-delʳ Γ₀′∤
    with Γ″ , Γ″~ , Γ~′ ← ~⊞-assocˡ Γ~ Γ₀~
      with Γ‴ , Γ‴~ , Γ~″ ← ~⊞-assocˡ Γ~′ Γ₀′~                                                                                                                                                               = -, -, ε
                                                                                                                                                                                                             , ξ-of-⟶* (`let-return[ _ ⇒ _ ]_`in _) ξ-`let-return[-⇒-]_`in-
                                                                                                                                                                                                                 (ξ-of-⟶* `return[ _ ⇒ _ ] ξ-`return[-⇒-] M₀′⟶*)
                                                                                                                                                                                                                 ◅◅ β-`↓ VM₀″ ◅ ε
                                                                                                                                                                                                             , true⊢[/]≈[/]ˡ
                                                                                                                                                                                                                 []
                                                                                                                                                                                                                 Γ~″
                                                                                                                                                                                                                 (⊢∧∤⇒⊢ (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) Γ₀′∤)
                                                                                                                                                                                                                 (WeakNorm≈⟶* (⊢∧∤⇒⊢ (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) Γ₀′∤) ⊢T L₀≈M₀ VL₀ (M₀⟶ ◅ M₀′⟶*))
                                                                                                                                                                                                                 ⊢S
                                                                                                                                                                                                                 (~⊞-is-all-del∧⊢⇒≈ʳ (to-right ∷ Γ‴~) (unusable ∷ Γ₀′₁Del)
                                                                                                                                                                                                                    (~⊞-is-all-del∧⊢⇒≈ʳ (to-right ∷ Γ″~) (unusable ∷ Γ₀₁Del) L₁≈M₁))
≈-diamond m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] Γ₀′∤ ⊢`return[-⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁) (β-`↓ VL₀)                                   (β-`↓ VM₀)                                   hL′   hM′
  with Γ₀₁ , Γ₀~ , Γ₀₁Del ← ∤⇒~⊞-is-all-delʳ Γ₀∤
     | Γ₀′₁ , Γ₀′~ , Γ₀′₁Del ← ∤⇒~⊞-is-all-delʳ Γ₀′∤
    with Γ″ , Γ″~ , Γ~′ ← ~⊞-assocˡ Γ~ Γ₀~
      with Γ‴ , Γ‴~ , Γ~″ ← ~⊞-assocˡ Γ~′ Γ₀′~                                                                                                                                                               = -, -, ε
                                                                                                                                                                                                             , ε
                                                                                                                                                                                                             , true⊢[/]≈[/]ˡ
                                                                                                                                                                                                                 []
                                                                                                                                                                                                                 Γ~″
                                                                                                                                                                                                                 (⊢∧∤⇒⊢ (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) Γ₀′∤)
                                                                                                                                                                                                                 L₀≈M₀
                                                                                                                                                                                                                 ⊢S
                                                                                                                                                                                                                 (~⊞-is-all-del∧⊢⇒≈ʳ (to-right ∷ Γ‴~) (unusable ∷ Γ₀′₁Del)
                                                                                                                                                                                                                   (~⊞-is-all-del∧⊢⇒≈ʳ (to-right ∷ Γ″~) (unusable ∷ Γ₀₁Del) L₁≈M₁))
≈-diamond m′≤m ⊢Γ ⊢S                     (Γ~ ⊢ L₀≈M₀ ⦂ ⊢⊸ `$ L₁≈M₁)                                    ξ- L₀⟶ `$?                                   ξ- M₀⟶ `$?                                   hL′   hM′
  with hL₀′ , _ ← halt-`$-inversion hL′
     | hM₀′ , _ ← halt-`$-inversion hM′
    with _ , _ , L₀′⟶* , M₀′⟶* , L₀″≈M₀″ ← ≈-diamond m′≤m (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) ⊢⊸ L₀≈M₀ L₀⟶ M₀⟶ hL₀′ hM₀′                                                                                                       = -, -, ξ-of-⟶* (_`$ _) ξ-_`$? L₀′⟶*
                                                                                                                                                                                                             , ξ-of-⟶* (_`$ _) ξ-_`$? M₀′⟶*
                                                                                                                                                                                                             , Γ~ ⊢ L₀″≈M₀″ ⦂ ⊢⊸ `$ L₁≈M₁
≈-diamond m′≤m ⊢Γ ⊢S                     (Γ~ ⊢ L₀≈M₀ ⦂ ⊢⊸ `$ L₁≈M₁)                                    ξ- L₀⟶ `$?                                   (ξ-! VM₀ `$ M₁⟶)                             hL′   hM′
  with ⊢T `⊸[ _ ] _ ← ⊢⊸
     | (_ , L₀′⟶* , VL₀″) , hL₁ ← halt-`$-inversion hL′
     | hM₀ , hM₁′ ← halt-`$-inversion hM′
    with L₀″≈M₀ ← ≈-sym (WeakNorm≈⟶* (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) ⊢⊸ (≈-sym L₀≈M₀) VM₀ (L₀⟶ ◅ L₀′⟶*))
      with hL₁
...      | _ , ε , VL₁
        with L₁≈M₁′ ← WeakNorm≈⟶ (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢T L₁≈M₁ VL₁ M₁⟶                                                                                                                                          = -, -, ξ-of-⟶* (_`$ _) ξ-_`$? L₀′⟶*
                                                                                                                                                                                                             , ε
                                                                                                                                                                                                             , Γ~ ⊢ L₀″≈M₀ ⦂ ⊢⊸ `$ L₁≈M₁′
...      | _ , L₁⟶ ◅ L₁′⟶* , VL₁″
        with _ , _ , L₁′⟶*′ , M₁′⟶* , L₁″≈M₁″ ← ≈-diamond m′≤m (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢T L₁≈M₁ L₁⟶ M₁⟶ (-, L₁′⟶* , VL₁″) hM₁′                                                                                     = -, -, ξ-of-⟶* (_`$ _) ξ-_`$? L₀′⟶*
                                                                                                                                                                                                                 ◅◅ ξ-of-⟶* (_ `$_) ξ-! VL₀″ `$_ (L₁⟶ ◅ L₁′⟶*′)
                                                                                                                                                                                                             , ξ-of-⟶* (_ `$_) ξ-! VM₀ `$_ M₁′⟶*
                                                                                                                                                                                                             , Γ~ ⊢ L₀″≈M₀ ⦂ ⊢⊸ `$ L₁″≈M₁″
≈-diamond m′≤m ⊢Γ ⊢S                     (Γ~ ⊢ `λ⦂-∘ L₀≈M₀ ⦂ ⊢⊸ `$ L₁≈M₁)                              ξ- () `$?                                    (β-`⊸ VM₁)                                   hL′   hM′
≈-diamond m′≤m ⊢Γ ⊢S                     (Γ~ ⊢ L₀≈M₀ ⦂ ⊢⊸ `$ L₁≈M₁)                                    (ξ-! VL₀ `$ L₁⟶)                             ξ- M₀⟶ `$?                                   hL′   hM′
  with ⊢T `⊸[ _ ] _ ← ⊢⊸
     | hL₀ , hL₁′ ← halt-`$-inversion hL′
     | (_ , M₀′⟶* , VM₀″) , hM₁ ← halt-`$-inversion hM′
    with L₀≈M₀″ ← WeakNorm≈⟶* (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) ⊢⊸ L₀≈M₀ VL₀ (M₀⟶ ◅ M₀′⟶*)
      with hM₁
...      | _ , ε , VM₁
        with L₁′≈M₁ ← ≈-sym (WeakNorm≈⟶ (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢T (≈-sym L₁≈M₁) VM₁ L₁⟶)                                                                                                                          = -, -, ε
                                                                                                                                                                                                             , ξ-of-⟶* (_`$ _) ξ-_`$? M₀′⟶*
                                                                                                                                                                                                             , Γ~ ⊢ L₀≈M₀″ ⦂ ⊢⊸ `$ L₁′≈M₁
...      | _ , M₁⟶ ◅ M₁′⟶* , VM₁″
        with _ , _ , L₁′⟶* , M₁′⟶*′ , L₁″≈M₁″ ← ≈-diamond m′≤m (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢T L₁≈M₁ L₁⟶ M₁⟶ hL₁′ (-, M₁′⟶* , VM₁″)                                                                                     = -, -, ξ-of-⟶* (_ `$_) ξ-! VL₀ `$_ L₁′⟶*
                                                                                                                                                                                                             , ξ-of-⟶* (_`$ _) ξ-_`$? M₀′⟶*
                                                                                                                                                                                                                 ◅◅ ξ-of-⟶* (_ `$_) ξ-! VM₀″ `$_ (M₁⟶ ◅ M₁′⟶*′)
                                                                                                                                                                                                             , Γ~ ⊢ L₀≈M₀″ ⦂ ⊢⊸ `$ L₁″≈M₁″
≈-diamond m′≤m ⊢Γ ⊢S                     (Γ~ ⊢ L₀≈M₀ ⦂ ⊢⊸ `$ L₁≈M₁)                                    (ξ-! VL₀ `$ L₁⟶)                             (ξ-! VM₀ `$ M₁⟶)                             hL′   hM′
  with ⊢T `⊸[ _ ] _ ← ⊢⊸
     | _ , hL₁′ ← halt-`$-inversion hL′
     | _ , hM₁′ ← halt-`$-inversion hM′
    with _ , _ , L₁′⟶* , M₁′⟶* , L₁″≈M₁″ ← ≈-diamond m′≤m (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢T L₁≈M₁ L₁⟶ M₁⟶ hL₁′ hM₁′                                                                                                       = -, -, ξ-of-⟶* (_ `$_) ξ-! VL₀ `$_ L₁′⟶*
                                                                                                                                                                                                             , ξ-of-⟶* (_ `$_) ξ-! VM₀ `$_ M₁′⟶*
                                                                                                                                                                                                             , Γ~ ⊢ L₀≈M₀ ⦂ ⊢⊸ `$ L₁″≈M₁″
≈-diamond m′≤m ⊢Γ ⊢S                     (Γ~ ⊢ `λ⦂-∘ L₀≈M₀ ⦂ ⊢⊸ `$ L₁≈M₁)                              (ξ-! VL₀ `$ L₁⟶)                             (β-`⊸ VM₁)                                   hL′   hM′
  with ⊢T `⊸[ _ ] _ ← ⊢⊸
     | hL₀ , (_ , L₁′⟶* , VL₁″) ← halt-`$-inversion hL′                                                                                                                                                      = -, -, ξ-of-⟶* (_ `$_) ξ-! VL₀ `$_ L₁′⟶*
                                                                                                                                                                                                                 ◅◅ β-`⊸ VL₁″ ◅ ε
                                                                                                                                                                                                             , ε
                                                                                                                                                                                                             , true⊢[/]≈[/]ʳ
                                                                                                                                                                                                                 []
                                                                                                                                                                                                                 Γ~
                                                                                                                                                                                                                 (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~)
                                                                                                                                                                                                                 (≈-sym (WeakNorm≈⟶* (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢T (≈-sym L₁≈M₁) VM₁ (L₁⟶ ◅ L₁′⟶*)))
                                                                                                                                                                                                                 ⊢S
                                                                                                                                                                                                                 L₀≈M₀
≈-diamond m′≤m ⊢Γ ⊢S                     (Γ~ ⊢ `λ⦂-∘ L₀≈M₀ ⦂ ⊢⊸ `$ L₁≈M₁)                              (β-`⊸ VL₁)                                   ξ- () `$?                                    hL′   hM′
≈-diamond m′≤m ⊢Γ ⊢S                     (Γ~ ⊢ `λ⦂-∘ L₀≈M₀ ⦂ ⊢⊸ `$ L₁≈M₁)                              (β-`⊸ VL₁)                                   (ξ-! VM₀ `$ M₁⟶)                             hL′   hM′
  with ⊢T `⊸[ _ ] _ ← ⊢⊸
     | hM₀ , (_ , M₁′⟶* , VM₁″) ← halt-`$-inversion hM′                                                                                                                                                      = -, -, ε
                                                                                                                                                                                                             , ξ-of-⟶* (_ `$_) ξ-! VM₀ `$_ M₁′⟶*
                                                                                                                                                                                                                 ◅◅ β-`⊸ VM₁″ ◅ ε
                                                                                                                                                                                                             , true⊢[/]≈[/]ʳ
                                                                                                                                                                                                                 []
                                                                                                                                                                                                                 Γ~
                                                                                                                                                                                                                 (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~)
                                                                                                                                                                                                                 (WeakNorm≈⟶* (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢T L₁≈M₁ VL₁ (M₁⟶ ◅ M₁′⟶*))
                                                                                                                                                                                                                 ⊢S
                                                                                                                                                                                                                 L₀≈M₀
≈-diamond m′≤m ⊢Γ ⊢S                     (Γ~ ⊢ `λ⦂-∘ L₀≈M₀ ⦂ ⊢⊸ `$ L₁≈M₁)                              (β-`⊸ VL₁)                                   (β-`⊸ VM₁)                                   hL′   hM′   = -, -, ε
                                                                                                                                                                                                             , ε
                                                                                                                                                                                                             , true⊢[/]≈[/]ʳ
                                                                                                                                                                                                                 []
                                                                                                                                                                                                                 Γ~
                                                                                                                                                                                                                 (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~)
                                                                                                                                                                                                                 L₁≈M₁
                                                                                                                                                                                                                 ⊢S
                                                                                                                                                                                                                 L₀≈M₀
≈-diamond m′≤m ⊢Γ (`↑[-⇒ m₀<m ][ _ ] ⊢S) (`lift[≤ m′≤m₀ ⇒-] L≈M)                                       (ξ-`lift[-⇒-] L⟶[≤])                         (ξ-`lift[-⇒-] M⟶[≤])                         hlL′  hlM′
  with h[≤]L′ ← halt-`lift-inversion hlL′
     | h[≤]M′ ← halt-`lift-inversion hlM′
    with _ , _ , L′⟶[≤]* , M′⟶[≤]* , L″≈M″ ← ≈-diamond[≤] m′≤m₀ (⊢∧<ₘ⇒⊢ ⊢Γ m₀<m) ⊢S L≈M L⟶[≤] M⟶[≤] h[≤]L′ h[≤]M′                                                                                            = -, -, ξ-of-↝*-⟶* _⟶[ _ ≤]_ `lift[ _ ⇒ _ ] ξ-`lift[-⇒-] L′⟶[≤]*
                                                                                                                                                                                                             , ξ-of-↝*-⟶* _⟶[ _ ≤]_ `lift[ _ ⇒ _ ] ξ-`lift[-⇒-] M′⟶[≤]*
                                                                                                                                                                                                             , `lift[≤ m′≤m₀ ⇒-] L″≈M″
≈-diamond m′≤m ⊢Γ (`↑[-⇒ m₀<m ][ _ ] ⊢S) (`lift[≰ m′≰m₀ ⇒-] ⊢L ⊢M)                                     (ξ-`lift[-⇒-] L⟶[≤])                         (ξ-`lift[-⇒-] M⟶[≤])                         hlL′  hlM′  = -, -, ε
                                                                                                                                                                                                             , ε
                                                                                                                                                                                                             , `lift[≰ m′≰m₀ ⇒-]
                                                                                                                                                                                                                 (preservation[≤] (⊢∧<ₘ⇒⊢ ⊢Γ m₀<m) ⊢S ⊢L L⟶[≤])
                                                                                                                                                                                                                 (preservation[≤] (⊢∧<ₘ⇒⊢ ⊢Γ m₀<m) ⊢S ⊢M M⟶[≤])

≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] L≈M ⦂ ⊢↑)                    (ξ-`unlift[≰ m″≰m₀ ⇒-] L⟶[≤])                (ξ-`unlift[≰ _ ⇒-] M⟶[≤])                h[≤]uL′  h[≤]uM′
  with `↑[-⇒ m<m₀ ][ _ ] _ ← ⊢↑
    with m′≤m₀ ← ≤ₘ-trans m′≤m (<ₘ⇒≤ₘ m<m₀)
       | h[≤]L′ ← halt[≤]-`unlift-inversion-≰ m″≰m₀ h[≤]uL′
       | h[≤]M′ ← halt[≤]-`unlift-inversion-≰ m″≰m₀ h[≤]uM′
      with _ , _ , L′⟶[≤]* , M′⟶[≤]* , L″≈M″ ← ≈-diamond[≤] m′≤m₀ (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ L≈M L⟶[≤] M⟶[≤] h[≤]L′ h[≤]M′                                                                                   = -, -, ξ-of-⟶[ _ ≤]* `unlift[ _ ⇒ _ ] ξ-`unlift[≰ m″≰m₀ ⇒-] L′⟶[≤]*
                                                                                                                                                                                                   , ξ-of-⟶[ _ ≤]* `unlift[ _ ⇒ _ ] ξ-`unlift[≰ m″≰m₀ ⇒-] M′⟶[≤]*
                                                                                                                                                                                                   , Γ∤ ⊢`unlift[-⇒-] L″≈M″ ⦂ ⊢↑
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] L≈M ⦂ ⊢↑)                    (ξ-`unlift[≰ m″≰m₀ ⇒-] L⟶[≤])                (ξ-`unlift[≤ m″≤m₀ ⇒-] M⟶)               h[≤]uL′  h[≤]uM′  with () ← m″≰m₀ m″≤m₀
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] L≈M ⦂ ⊢↑)                    (ξ-`unlift[≰ m″≰m₀ ⇒-] L⟶[≤])                (β-`↑ m″≤m₀ WM)                          h[≤]ulL′ h[≤]M′   with () ← m″≰m₀ m″≤m₀
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] L≈M ⦂ ⊢↑)                    (ξ-`unlift[≤ m″≤m₀ ⇒-] L⟶)                   (ξ-`unlift[≰ m″≰m₀ ⇒-] M⟶[≤])            h[≤]uL′  h[≤]uM′  with () ← m″≰m₀ m″≤m₀
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] L≈M ⦂ ⊢↑)                    (ξ-`unlift[≤ m″≤m₀ ⇒-] L⟶)                   (ξ-`unlift[≤ _ ⇒-] M⟶)                   h[≤]uL′  h[≤]uM′
  with `↑[-⇒ m<m₀ ][ _ ] _ ← ⊢↑
    with m′≤m₀ ← ≤ₘ-trans m′≤m (<ₘ⇒≤ₘ m<m₀)
       | hL′ ← halt[≤]-`unlift-inversion-≤ m″≤m₀ h[≤]uL′
       | hM′ ← halt[≤]-`unlift-inversion-≤ m″≤m₀ h[≤]uM′
      with _ , _ , L′⟶* , M′⟶* , L″≈M″ ← ≈-diamond m′≤m₀ (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ L≈M L⟶ M⟶ hL′ hM′                                                                                                        = -, -, ξ-of-↝*-⟶[ _ ≤]* _⟶_ `unlift[ _ ⇒ _ ] ξ-`unlift[≤ m″≤m₀ ⇒-] L′⟶*
                                                                                                                                                                                                   , ξ-of-↝*-⟶[ _ ≤]* _⟶_ `unlift[ _ ⇒ _ ] ξ-`unlift[≤ m″≤m₀ ⇒-] M′⟶*
                                                                                                                                                                                                   , Γ∤ ⊢`unlift[-⇒-] L″≈M″ ⦂ ⊢↑
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[≤ _ ⇒-] L≈M ⦂ ⊢↑)      (ξ-`unlift[≤ m″≤m₀ ⇒-] (ξ-`lift[-⇒-] L⟶[≤])) (β-`↑ _ WM)                              h[≤]ulL′ h[≤]M′
  with `↑[-⇒ m<m₀ ][ _ ] _ ← ⊢↑
     | _ , L′⟶[≤]* , WL″ ← halt-`lift-inversion (halt[≤]-`unlift-inversion-≤ m″≤m₀ h[≤]ulL′)                                                                                                       = -, -, ξ-of-↝*-⟶[ _ ≤]* _⟶_ `unlift[ _ ⇒ _ ] ξ-`unlift[≤ m″≤m₀ ⇒-]
                                                                                                                                                                                                       (ξ-of-↝*-⟶* _⟶[ _ ≤]_ `lift[ _ ⇒ _ ] ξ-`lift[-⇒-] L′⟶[≤]*)
                                                                                                                                                                                                       ◅◅ β-`↑ m″≤m₀ WL″ ◅ ε
                                                                                                                                                                                                   , ε
                                                                                                                                                                                                   , ∤⁻¹-preserves-≈ [] (≈-sym (DeferredTerm≈⟶[≤]* (⊢∧<ₘ⇒⊢ (⊢∧∤⇒⊢ ⊢Γ Γ∤) m<m₀) ⊢S (≈-sym L≈M) WM (L⟶[≤] ◅ L′⟶[≤]*))) Γ∤
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] L≈M ⦂ ⊢↑)                    (β-`↑ m″≤m₀ WL)                              (ξ-`unlift[≰ m″≰m₀ ⇒-] M⟶[≤])            h[≤]L′   h[≤]ulM′ with () ← m″≰m₀ m″≤m₀
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[≤ _ ⇒-] L≈M ⦂ ⊢↑)      (β-`↑ m″≤m₀ WL)                              (ξ-`unlift[≤ _ ⇒-] (ξ-`lift[-⇒-] M⟶[≤])) h[≤]L′   h[≤]ulM′
  with `↑[-⇒ m<m₀ ][ _ ] _ ← ⊢↑
     | _ , M′⟶[≤]* , WM″ ← halt-`lift-inversion (halt[≤]-`unlift-inversion-≤ m″≤m₀ h[≤]ulM′)                                                                                                       = -, -, ε
                                                                                                                                                                                                   , ξ-of-↝*-⟶[ _ ≤]* _⟶_ `unlift[ _ ⇒ _ ] ξ-`unlift[≤ m″≤m₀ ⇒-]
                                                                                                                                                                                                       (ξ-of-↝*-⟶* _⟶[ _ ≤]_ `lift[ _ ⇒ _ ] ξ-`lift[-⇒-] M′⟶[≤]*)
                                                                                                                                                                                                       ◅◅ β-`↑ m″≤m₀ WM″ ◅ ε
                                                                                                                                                                                                   , ∤⁻¹-preserves-≈ [] (DeferredTerm≈⟶[≤]* (⊢∧<ₘ⇒⊢ (⊢∧∤⇒⊢ ⊢Γ Γ∤) m<m₀) ⊢S L≈M WL (M⟶[≤] ◅ M′⟶[≤]*)) Γ∤
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[≤ _ ⇒-] L≈M ⦂ ⊢↑)      (β-`↑ m″≤m₀ WL)                              (β-`↑ _ WM)                              h[≤]L′   h[≤]M′   = -, -, ε , ε , ∤⁻¹-preserves-≈ [] L≈M Γ∤
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[≰ m′≰m ⇒-] ⊢L ⊢M ⦂ ⊢↑) L⟶[≤]                                        M⟶[≤]                                    h[≤]L′   h[≤]M′   with () ← m′≰m m′≤m
≈-diamond[≤] m′≤m ⊢Γ (`↓[-⇒ m<m₀ ][ _ ] ⊢S) (Γ∤ ⊢`return[-⇒-] L≈M)                         (ξ-`return[≰ m″≰m₀ ⇒-] L⟶[≤])                (ξ-`return[≰ _ ⇒-] M⟶[≤])                h[≤]rL′  h[≤]rM′
  with m′≤m₀ ← ≤ₘ-trans m′≤m (<ₘ⇒≤ₘ m<m₀)
     | h[≤]L′ ← halt[≤]-`return-inversion-≰ m″≰m₀ h[≤]rL′
     | h[≤]M′ ← halt[≤]-`return-inversion-≰ m″≰m₀ h[≤]rM′
    with _ , _ , L′⟶[≤]* , M′⟶[≤]* , L″≈M″ ← ≈-diamond[≤] m′≤m₀ (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S L≈M L⟶[≤] M⟶[≤] h[≤]L′ h[≤]M′                                                                                     = -, -, ξ-of-⟶[ _ ≤]* `return[ _ ⇒ _ ] ξ-`return[≰ m″≰m₀ ⇒-] L′⟶[≤]*
                                                                                                                                                                                                   , ξ-of-⟶[ _ ≤]* `return[ _ ⇒ _ ] ξ-`return[≰ m″≰m₀ ⇒-] M′⟶[≤]*
                                                                                                                                                                                                   , Γ∤ ⊢`return[-⇒-] L″≈M″
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ∤ ⊢`return[-⇒-] L≈M)                         (ξ-`return[≰ m″≰m₀ ⇒-] L⟶[≤])                (ξ-`return[≤ m″≤m₀ ⇒-] M⟶)               h[≤]rL′  h[≤]rM′  with () ← m″≰m₀ m″≤m₀
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ∤ ⊢`return[-⇒-] L≈M)                         (ξ-`return[≤ m″≤m₀ ⇒-] L⟶)                   (ξ-`return[≰ m″≰m₀ ⇒-] M⟶[≤])            h[≤]rL′  h[≤]rM′  with () ← m″≰m₀ m″≤m₀
≈-diamond[≤] m′≤m ⊢Γ (`↓[-⇒ m<m₀ ][ _ ] ⊢S) (Γ∤ ⊢`return[-⇒-] L≈M)                         (ξ-`return[≤ m″≤m₀ ⇒-] L⟶)                   (ξ-`return[≤ _ ⇒-] M⟶)                   h[≤]rL′  h[≤]rM′
  with m′≤m₀ ← ≤ₘ-trans m′≤m (<ₘ⇒≤ₘ m<m₀)
     | hL′ ← halt[≤]-`return-inversion-≤ m″≤m₀ h[≤]rL′
     | hM′ ← halt[≤]-`return-inversion-≤ m″≤m₀ h[≤]rM′
    with _ , _ , L′⟶* , M′⟶* , L″≈M″ ← ≈-diamond m′≤m₀ (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S L≈M L⟶ M⟶ hL′ hM′                                                                                                          = -, -, ξ-of-↝*-⟶[ _ ≤]* _⟶_ `return[ _ ⇒ _ ] ξ-`return[≤ m″≤m₀ ⇒-] L′⟶*
                                                                                                                                                                                                   , ξ-of-↝*-⟶[ _ ≤]* _⟶_ `return[ _ ⇒ _ ] ξ-`return[≤ m″≤m₀ ⇒-] M′⟶*
                                                                                                                                                                                                   , Γ∤ ⊢`return[-⇒-] L″≈M″
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁)    ξ-`let-return[≰ m₀≰m₁ ⇒-] L₀⟶[≤] `in?               ξ-`let-return[≰ _ ⇒-] M₀⟶[≤] `in?           h[≤]L′   h[≤]M′
  with h[≤]L₀′ , _ ← halt[≤]-`let-return[≰]-`in-inversion m₀≰m₁ h[≤]L′
     | h[≤]M₀′ , _ ← halt[≤]-`let-return[≰]-`in-inversion m₀≰m₁ h[≤]M′
    with _ , _ , L₀′⟶[≤]* , M₀′⟶[≤]* , L₀″≈M₀″ ← ≈-diamond[≤] (≤ₘ-trans m′≤m m≤m₁) (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) ⊢↓ L₀≈M₀ L₀⟶[≤] M₀⟶[≤] h[≤]L₀′ h[≤]M₀′                                            = -, -, ξ-of-⟶[ _ ≤]* (`let-return[ _ ⇒ _ ]_`in _) ξ-`let-return[≰ m₀≰m₁ ⇒-]_`in? L₀′⟶[≤]*
                                                                                                                                                                                                   , ξ-of-⟶[ _ ≤]* (`let-return[ _ ⇒ _ ]_`in _) ξ-`let-return[≰ m₀≰m₁ ⇒-]_`in? M₀′⟶[≤]*
                                                                                                                                                                                                   , Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀″≈M₀″ ⦂ ⊢↓ `in L₁≈M₁
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁)    ξ-`let-return[≰ m₀≰m₁ ⇒-] L₀⟶[≤] `in?               ξ-`let-return[≤ m₀≤m₁ ⇒-] M₀⟶ `in?           h[≤]L′   h[≤]M′ with () ← m₀≰m₁ m₀≤m₁
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁)    ξ-`let-return[≤ m₀≤m₁ ⇒-] L₀⟶ `in?                  ξ-`let-return[≰ m₀≰m₁ ⇒-] M₀⟶[≤] `in?        h[≤]L′   h[≤]M′ with () ← m₀≰m₁ m₀≤m₁
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁)    ξ-`let-return[≤ m₀≤m₁ ⇒-] L₀⟶ `in?                  ξ-`let-return[≤ _ ⇒-] M₀⟶ `in?               h[≤]L′   h[≤]M′
  with hL₀′ , _ ← halt[≤]-`let-return[≤]-`in-inversion m₀≤m₁ h[≤]L′
     | hM₀′ , _ ← halt[≤]-`let-return[≤]-`in-inversion m₀≤m₁ h[≤]M′
    with _ , _ , L₀′⟶* , M₀′⟶* , L₀″≈M₀″ ← ≈-diamond (≤ₘ-trans m′≤m m≤m₁) (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) ⊢↓ L₀≈M₀ L₀⟶ M₀⟶ hL₀′ hM₀′                                                                 = -, -, ξ-of-↝*-⟶[ _ ≤]* _⟶_ (`let-return[ _ ⇒ _ ]_`in _) ξ-`let-return[≤ m₀≤m₁ ⇒-]_`in? L₀′⟶*
                                                                                                                                                                                                   , ξ-of-↝*-⟶[ _ ≤]* _⟶_ (`let-return[ _ ⇒ _ ]_`in _) ξ-`let-return[≤ m₀≤m₁ ⇒-]_`in? M₀′⟶*
                                                                                                                                                                                                   , Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀″≈M₀″ ⦂ ⊢↓ `in L₁≈M₁
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁)    ξ-`let-return[≰ m₀≰m₁ ⇒-] L₀⟶[≤] `in?               (ξ-`let-return[≰ _ ⇒-]! WM₀ `in M₁⟶[≤])     h[≤]L′   h[≤]M′
  with `↓[-⇒ m₁<m₀ ][ _ ] ⊢T ← ⊢↓
     | (_ , L₀′⟶[≤]* , WL₀″) , h[≤]L₁ ← halt[≤]-`let-return[≰]-`in-inversion m₀≰m₁ h[≤]L′
     | h[≤]M₀ , h[≤]M₁′ ← halt[≤]-`let-return[≰]-`in-inversion m₀≰m₁ h[≤]M′
    with L₀″≈M₀ ← ≈-sym (DeferredTerm≈⟶[≤]* (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) ⊢↓ (≈-sym L₀≈M₀) WM₀ (L₀⟶[≤] ◅ L₀′⟶[≤]*))
      with h[≤]L₁
...      | _ , ε , WL₁
        with L₁≈M₁′ ← DeferredTerm≈⟶[≤] ((⊢T , valid (≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m₁<m₀))) ∷ ⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢S L₁≈M₁ WL₁ M₁⟶[≤]                                                                         = -, -, ξ-of-⟶[ _ ≤]* (`let-return[ _ ⇒ _ ]_`in _) ξ-`let-return[≰ m₀≰m₁ ⇒-]_`in? L₀′⟶[≤]*
                                                                                                                                                                                                   , ε
                                                                                                                                                                                                   , Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀″≈M₀ ⦂ ⊢↓ `in L₁≈M₁′
...      | _ , L₁⟶[≤] ◅ L₁′⟶[≤]* , WL₁″
        with _ , _ , L₁′⟶[≤]*′ , M₁′⟶[≤]* , L₁″≈M₁″ ← ≈-diamond[≤] m′≤m ((⊢T , valid (≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m₁<m₀))) ∷ ⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢S L₁≈M₁ L₁⟶[≤] M₁⟶[≤] (-, L₁′⟶[≤]* , WL₁″) h[≤]M₁′         = -, -, ξ-of-⟶[ _ ≤]* (`let-return[ _ ⇒ _ ]_`in _) ξ-`let-return[≰ m₀≰m₁ ⇒-]_`in? L₀′⟶[≤]*
                                                                                                                                                                                                       ◅◅ ξ-of-⟶[ _ ≤]* `let-return[ _ ⇒ _ ] _ `in_ ξ-`let-return[≰ m₀≰m₁ ⇒-]! WL₀″ `in_ (L₁⟶[≤] ◅ L₁′⟶[≤]*′)
                                                                                                                                                                                                   , ξ-of-⟶[ _ ≤]* `let-return[ _ ⇒ _ ] _ `in_ ξ-`let-return[≰ m₀≰m₁ ⇒-]! WM₀ `in_ M₁′⟶[≤]*
                                                                                                                                                                                                   , Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀″≈M₀ ⦂ ⊢↓ `in L₁″≈M₁″
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁)    ξ-`let-return[≰ m₀≰m₁ ⇒-] L₀⟶[≤] `in?               (ξ-`let-return[≤ m₀≤m₁ ⇒-]! VM₀ `in M₁⟶[≤])     h[≤]L′   h[≤]M′ with () ← m₀≰m₁ m₀≤m₁
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁)    ξ-`let-return[≤ m₀≤m₁ ⇒-] L₀⟶ `in?               (ξ-`let-return[≰ m₀≰m₁ ⇒-]! WM₀ `in M₁⟶[≤])     h[≤]L′   h[≤]M′ with () ← m₀≰m₁ m₀≤m₁
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁)    ξ-`let-return[≤ m₀≤m₁ ⇒-] L₀⟶ `in?               (ξ-`let-return[≤ _ ⇒-]! VM₀ `in M₁⟶[≤])     h[≤]L′   h[≤]M′
  with `↓[-⇒ m₁<m₀ ][ _ ] ⊢T ← ⊢↓
     | (_ , L₀′⟶* , VL₀″) , h[≤]L₁ ← halt[≤]-`let-return[≤]-`in-inversion m₀≤m₁ h[≤]L′
     | hM₀ , h[≤]M₁′ ← halt[≤]-`let-return[≤]-`in-inversion m₀≤m₁ h[≤]M′
    with L₀″≈M₀ ← ≈-sym (WeakNorm≈⟶* (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) ⊢↓ (≈-sym L₀≈M₀) VM₀ (L₀⟶ ◅ L₀′⟶*))
      with h[≤]L₁
...      | _ , ε , WL₁
        with L₁≈M₁′ ← DeferredTerm≈⟶[≤] ((⊢T , valid (≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m₁<m₀))) ∷ ⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢S L₁≈M₁ WL₁ M₁⟶[≤]                                                                         = -, -, ξ-of-↝*-⟶[ _ ≤]* _⟶_ (`let-return[ _ ⇒ _ ]_`in _) ξ-`let-return[≤ m₀≤m₁ ⇒-]_`in? L₀′⟶*
                                                                                                                                                                                                   , ε
                                                                                                                                                                                                   , Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀″≈M₀ ⦂ ⊢↓ `in L₁≈M₁′
...      | _ , L₁⟶[≤] ◅ L₁′⟶[≤]* , WL₁″
        with _ , _ , L₁′⟶[≤]*′ , M₁′⟶[≤]* , L₁″≈M₁″ ← ≈-diamond[≤] m′≤m ((⊢T , valid (≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m₁<m₀))) ∷ ⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢S L₁≈M₁ L₁⟶[≤] M₁⟶[≤] (-, L₁′⟶[≤]* , WL₁″) h[≤]M₁′         = -, -, ξ-of-↝*-⟶[ _ ≤]* _⟶_ (`let-return[ _ ⇒ _ ]_`in _) ξ-`let-return[≤ m₀≤m₁ ⇒-]_`in? L₀′⟶*
                                                                                                                                                                                                       ◅◅ ξ-of-⟶[ _ ≤]* `let-return[ _ ⇒ _ ] _ `in_ ξ-`let-return[≤ m₀≤m₁ ⇒-]! VL₀″ `in_ (L₁⟶[≤] ◅ L₁′⟶[≤]*′)
                                                                                                                                                                                                   , ξ-of-⟶[ _ ≤]* `let-return[ _ ⇒ _ ] _ `in_ ξ-`let-return[≤ m₀≤m₁ ⇒-]! VM₀ `in_ M₁′⟶[≤]*
                                                                                                                                                                                                   , Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀″≈M₀ ⦂ ⊢↓ `in L₁″≈M₁″
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁)    (ξ-`let-return[≰ m₀≰m₁ ⇒-]! WL₀ `in L₁⟶[≤])         ξ-`let-return[≰ _ ⇒-] M₀⟶[≤] `in?           h[≤]L′   h[≤]M′
  with `↓[-⇒ m₁<m₀ ][ _ ] ⊢T ← ⊢↓
     | h[≤]L₀ , h[≤]L₁′ ← halt[≤]-`let-return[≰]-`in-inversion m₀≰m₁ h[≤]L′
     | (_ , M₀′⟶[≤]* , WM₀″) , h[≤]M₁ ← halt[≤]-`let-return[≰]-`in-inversion m₀≰m₁ h[≤]M′
    with L₀≈M₀″ ← DeferredTerm≈⟶[≤]* (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) ⊢↓ L₀≈M₀ WL₀ (M₀⟶[≤] ◅ M₀′⟶[≤]*)
      with h[≤]M₁
...      | _ , ε , WM₁
        with L₁′≈M₁ ← ≈-sym (DeferredTerm≈⟶[≤] ((⊢T , valid (≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m₁<m₀))) ∷ ⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢S (≈-sym L₁≈M₁) WM₁ L₁⟶[≤])                                                         = -, -, ε
                                                                                                                                                                                                   , ξ-of-⟶[ _ ≤]* (`let-return[ _ ⇒ _ ]_`in _) ξ-`let-return[≰ m₀≰m₁ ⇒-]_`in? M₀′⟶[≤]*
                                                                                                                                                                                                   , Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀″ ⦂ ⊢↓ `in L₁′≈M₁
...      | _ , M₁⟶[≤] ◅ M₁′⟶[≤]* , WM₁″
        with _ , _ , L₁′⟶[≤]* , M₁′⟶[≤]*′ , L₁″≈M₁″ ← ≈-diamond[≤] m′≤m ((⊢T , valid (≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m₁<m₀))) ∷ ⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢S L₁≈M₁ L₁⟶[≤] M₁⟶[≤] h[≤]L₁′ (-, M₁′⟶[≤]* , WM₁″)         = -, -, ξ-of-⟶[ _ ≤]* `let-return[ _ ⇒ _ ] _ `in_ ξ-`let-return[≰ m₀≰m₁ ⇒-]! WL₀ `in_ L₁′⟶[≤]*
                                                                                                                                                                                                   , ξ-of-⟶[ _ ≤]* (`let-return[ _ ⇒ _ ]_`in _) ξ-`let-return[≰ m₀≰m₁ ⇒-]_`in? M₀′⟶[≤]*
                                                                                                                                                                                                       ◅◅ ξ-of-⟶[ _ ≤]* `let-return[ _ ⇒ _ ] _ `in_ ξ-`let-return[≰ m₀≰m₁ ⇒-]! WM₀″ `in_ (M₁⟶[≤] ◅ M₁′⟶[≤]*′)
                                                                                                                                                                                                   , Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀″ ⦂ ⊢↓ `in L₁″≈M₁″
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁)    (ξ-`let-return[≰ m₀≰m₁ ⇒-]! WL₀ `in L₁⟶[≤])         ξ-`let-return[≤ m₀≤m₁ ⇒-] M₀⟶ `in?           h[≤]L′   h[≤]M′ with () ← m₀≰m₁ m₀≤m₁
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁)    (ξ-`let-return[≤ m₀≤m₁ ⇒-]! VL₀ `in L₁⟶[≤])         ξ-`let-return[≰ m₀≰m₁ ⇒-] M₀⟶[≤] `in?           h[≤]L′   h[≤]M′ with () ← m₀≰m₁ m₀≤m₁
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁)    (ξ-`let-return[≤ m₀≤m₁ ⇒-]! VL₀ `in L₁⟶[≤])         ξ-`let-return[≤ _ ⇒-] M₀⟶ `in?           h[≤]L′   h[≤]M′
  with `↓[-⇒ m₁<m₀ ][ _ ] ⊢T ← ⊢↓
     | hL₀ , h[≤]L₁′ ← halt[≤]-`let-return[≤]-`in-inversion m₀≤m₁ h[≤]L′
     | (_ , M₀′⟶* , VM₀″) , h[≤]M₁ ← halt[≤]-`let-return[≤]-`in-inversion m₀≤m₁ h[≤]M′
    with L₀≈M₀″ ← WeakNorm≈⟶* (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) Γ₀∤) ⊢↓ L₀≈M₀ VL₀ (M₀⟶ ◅ M₀′⟶*)
      with h[≤]M₁
...      | _ , ε , WM₁
        with L₁′≈M₁ ← ≈-sym (DeferredTerm≈⟶[≤] ((⊢T , valid (≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m₁<m₀))) ∷ ⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢S (≈-sym L₁≈M₁) WM₁ L₁⟶[≤])                                                         = -, -, ε
                                                                                                                                                                                                   , ξ-of-↝*-⟶[ _ ≤]* _⟶_ (`let-return[ _ ⇒ _ ]_`in _) ξ-`let-return[≤ m₀≤m₁ ⇒-]_`in? M₀′⟶*
                                                                                                                                                                                                   , Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀″ ⦂ ⊢↓ `in L₁′≈M₁
...      | _ , M₁⟶[≤] ◅ M₁′⟶[≤]* , WM₁″
        with _ , _ , L₁′⟶[≤]* , M₁′⟶[≤]*′ , L₁″≈M₁″ ← ≈-diamond[≤] m′≤m ((⊢T , valid (≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m₁<m₀))) ∷ ⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢S L₁≈M₁ L₁⟶[≤] M₁⟶[≤] h[≤]L₁′ (-, M₁′⟶[≤]* , WM₁″)         = -, -, ξ-of-⟶[ _ ≤]* `let-return[ _ ⇒ _ ] _ `in_ ξ-`let-return[≤ m₀≤m₁ ⇒-]! VL₀ `in_ L₁′⟶[≤]*
                                                                                                                                                                                                   , ξ-of-↝*-⟶[ _ ≤]* _⟶_ (`let-return[ _ ⇒ _ ]_`in _) ξ-`let-return[≤ m₀≤m₁ ⇒-]_`in? M₀′⟶*
                                                                                                                                                                                                       ◅◅ ξ-of-⟶[ _ ≤]* `let-return[ _ ⇒ _ ] _ `in_ ξ-`let-return[≤ m₀≤m₁ ⇒-]! VM₀″ `in_ (M₁⟶[≤] ◅ M₁′⟶[≤]*′)
                                                                                                                                                                                                   , Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀″ ⦂ ⊢↓ `in L₁″≈M₁″
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁)    (ξ-`let-return[≰ m₀≰m₁ ⇒-]! WL₀ `in L₁⟶[≤])         (ξ-`let-return[≰ _ ⇒-]! WM₀ `in M₁⟶[≤])     h[≤]L′   h[≤]M′
  with `↓[-⇒ m₁<m₀ ][ _ ] ⊢T ← ⊢↓
     | _ , h[≤]L₁′ ← halt[≤]-`let-return[≰]-`in-inversion m₀≰m₁ h[≤]L′
     | _ , h[≤]M₁′ ← halt[≤]-`let-return[≰]-`in-inversion m₀≰m₁ h[≤]M′
    with _ , _ , L₁′⟶[≤]* , M₁′⟶[≤]* , L₁″≈M₁″ ← ≈-diamond[≤] m′≤m ((⊢T , valid (≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m₁<m₀))) ∷ ⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢S L₁≈M₁ L₁⟶[≤] M₁⟶[≤] h[≤]L₁′ h[≤]M₁′                           = -, -, ξ-of-⟶[ _ ≤]* (`let-return[ _ ⇒ _ ] _ `in_) (ξ-`let-return[≰ m₀≰m₁ ⇒-]! WL₀ `in_) L₁′⟶[≤]*
                                                                                                                                                                                                   , ξ-of-⟶[ _ ≤]* (`let-return[ _ ⇒ _ ] _ `in_) (ξ-`let-return[≰ m₀≰m₁ ⇒-]! WM₀ `in_) M₁′⟶[≤]*
                                                                                                                                                                                                   , Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁″≈M₁″
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁)    (ξ-`let-return[≰ m₀≰m₁ ⇒-]! WL₀ `in L₁⟶[≤])         (ξ-`let-return[≤ m₀≤m₁ ⇒-]! VM₀ `in M₁⟶[≤])     h[≤]L′   h[≤]M′ with () ← m₀≰m₁ m₀≤m₁
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁)    (ξ-`let-return[≤ m₀≤m₁ ⇒-]! VL₀ `in L₁⟶[≤])         (ξ-`let-return[≰ m₀≰m₁ ⇒-]! WM₀ `in M₁⟶[≤])     h[≤]L′   h[≤]M′ with () ← m₀≰m₁ m₀≤m₁
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁≈M₁)    (ξ-`let-return[≤ m₀≤m₁ ⇒-]! VL₀ `in L₁⟶[≤])         (ξ-`let-return[≤ _ ⇒-]! VM₀ `in M₁⟶[≤])     h[≤]L′   h[≤]M′
  with `↓[-⇒ m₁<m₀ ][ _ ] ⊢T ← ⊢↓
     | _ , h[≤]L₁′ ← halt[≤]-`let-return[≤]-`in-inversion m₀≤m₁ h[≤]L′
     | _ , h[≤]M₁′ ← halt[≤]-`let-return[≤]-`in-inversion m₀≤m₁ h[≤]M′
    with _ , _ , L₁′⟶[≤]* , M₁′⟶[≤]* , L₁″≈M₁″ ← ≈-diamond[≤] m′≤m ((⊢T , valid (≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m₁<m₀))) ∷ ⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢S L₁≈M₁ L₁⟶[≤] M₁⟶[≤] h[≤]L₁′ h[≤]M₁′                           = -, -, ξ-of-⟶[ _ ≤]* (`let-return[ _ ⇒ _ ] _ `in_) (ξ-`let-return[≤ m₀≤m₁ ⇒-]! VL₀ `in_) L₁′⟶[≤]*
                                                                                                                                                                                                   , ξ-of-⟶[ _ ≤]* (`let-return[ _ ⇒ _ ] _ `in_) (ξ-`let-return[≤ m₀≤m₁ ⇒-]! VM₀ `in_) M₁′⟶[≤]*
                                                                                                                                                                                                   , Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] L₀≈M₀ ⦂ ⊢↓ `in L₁″≈M₁″
≈-diamond[≤] m′≤m ⊢Γ (⊢T `⊸[ _ ] ⊢S)        (`λ⦂-∘ L≈M)                                    (ξ-`λ⦂[-]-∘ L⟶[≤])                           (ξ-`λ⦂[-]-∘ M⟶[≤])                       h[≤]λL′  h[≤]λM′
  with h[≤]L′ ← halt[≤]-`λ⦂-∘-inversion h[≤]λL′
     | h[≤]M′ ← halt[≤]-`λ⦂-∘-inversion h[≤]λM′
    with _ , _ , L′⟶[≤]* , M′⟶[≤]* , L″≈M″ ← ≈-diamond[≤] m′≤m ((⊢T , valid ≤ₘ-refl) ∷ ⊢Γ) ⊢S L≈M L⟶[≤] M⟶[≤] h[≤]L′ h[≤]M′                                                                        = -, -, ξ-of-⟶[ _ ≤]* `λ⦂[ _ ] _ ∘_ ξ-`λ⦂[-]-∘_ L′⟶[≤]*
                                                                                                                                                                                                   , ξ-of-⟶[ _ ≤]* `λ⦂[ _ ] _ ∘_ ξ-`λ⦂[-]-∘_ M′⟶[≤]*
                                                                                                                                                                                                   , `λ⦂-∘ L″≈M″
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ ⊢ L₀≈M₀ ⦂ ⊢⊸ `$ L₁≈M₁)                     ξ- L₀⟶[≤] `$?                                ξ- M₀⟶[≤] `$?                            h[≤]L′   h[≤]M′
  with h[≤]L₀′ , _ ← halt[≤]-`$-inversion h[≤]L′
     | h[≤]M₀′ , _ ← halt[≤]-`$-inversion h[≤]M′
    with _ , _ , L₀′⟶[≤]* , M₀′⟶[≤]* , L₀″≈M₀″ ← ≈-diamond[≤] m′≤m (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) ⊢⊸ L₀≈M₀ L₀⟶[≤] M₀⟶[≤] h[≤]L₀′ h[≤]M₀′                                                                        = -, -, ξ-of-⟶[ _ ≤]* (_`$ _) ξ-_`$? L₀′⟶[≤]*
                                                                                                                                                                                                   , ξ-of-⟶[ _ ≤]* (_`$ _) ξ-_`$? M₀′⟶[≤]*
                                                                                                                                                                                                   , Γ~ ⊢ L₀″≈M₀″ ⦂ ⊢⊸ `$ L₁≈M₁
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ ⊢ L₀≈M₀ ⦂ ⊢⊸ `$ L₁≈M₁)                     ξ- L₀⟶[≤] `$?                                (ξ-! WM₀ `$ M₁⟶[≤])                      h[≤]L′   h[≤]M′
  with ⊢T `⊸[ _ ] _ ← ⊢⊸
     | (_ , L₀′⟶[≤]* , WL₀″) , h[≤]L₁ ← halt[≤]-`$-inversion h[≤]L′
     | h[≤]M₀ , h[≤]M₁′ ← halt[≤]-`$-inversion h[≤]M′
    with L₀″≈M₀ ← ≈-sym (DeferredTerm≈⟶[≤]* (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) ⊢⊸ (≈-sym L₀≈M₀) WM₀ (L₀⟶[≤] ◅ L₀′⟶[≤]*))
      with h[≤]L₁
...      | _ , ε , WL₁
        with L₁≈M₁′ ← DeferredTerm≈⟶[≤] (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢T L₁≈M₁ WL₁ M₁⟶[≤]                                                                                                                      = -, -, ξ-of-⟶[ _ ≤]* (_`$ _) ξ-_`$? L₀′⟶[≤]*
                                                                                                                                                                                                   , ε
                                                                                                                                                                                                   , Γ~ ⊢ L₀″≈M₀ ⦂ ⊢⊸ `$ L₁≈M₁′
...      | _ , L₁⟶[≤] ◅ L₁′⟶[≤]* , WL₁″
        with _ , _ , L₁′⟶[≤]*′ , M₁′⟶[≤]* , L₁″≈M₁″ ← ≈-diamond[≤] m′≤m (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢T L₁≈M₁ L₁⟶[≤] M₁⟶[≤] (-, L₁′⟶[≤]* , WL₁″) h[≤]M₁′                                                      = -, -, ξ-of-⟶[ _ ≤]* (_`$ _) ξ-_`$? L₀′⟶[≤]*
                                                                                                                                                                                                       ◅◅ ξ-of-⟶[ _ ≤]* (_ `$_) ξ-! WL₀″ `$_ (L₁⟶[≤] ◅ L₁′⟶[≤]*′)
                                                                                                                                                                                                   , ξ-of-⟶[ _ ≤]* (_ `$_) ξ-! WM₀ `$_ M₁′⟶[≤]*
                                                                                                                                                                                                   , Γ~ ⊢ L₀″≈M₀ ⦂ ⊢⊸ `$ L₁″≈M₁″
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ ⊢ L₀≈M₀ ⦂ ⊢⊸ `$ L₁≈M₁)                     (ξ-! WL₀ `$ L₁⟶[≤])                          ξ- M₀⟶[≤] `$?                            h[≤]L′   h[≤]M′
  with ⊢T `⊸[ _ ] _ ← ⊢⊸
     | h[≤]L₀ , h[≤]L₁′ ← halt[≤]-`$-inversion h[≤]L′
     | (_ , M₀′⟶[≤]* , WM₀″) , h[≤]M₁ ← halt[≤]-`$-inversion h[≤]M′
    with L₀≈M₀″ ← DeferredTerm≈⟶[≤]* (⊢∧-~⊞-⇒⊢ˡ ⊢Γ Γ~) ⊢⊸ L₀≈M₀ WL₀ (M₀⟶[≤] ◅ M₀′⟶[≤]*)
      with h[≤]M₁
...      | _ , ε , WM₁
        with L₁′≈M₁ ← ≈-sym (DeferredTerm≈⟶[≤] (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢T (≈-sym L₁≈M₁) WM₁ L₁⟶[≤])                                                                                                      = -, -, ε
                                                                                                                                                                                                   , ξ-of-⟶[ _ ≤]* (_`$ _) ξ-_`$? M₀′⟶[≤]*
                                                                                                                                                                                                   , Γ~ ⊢ L₀≈M₀″ ⦂ ⊢⊸ `$ L₁′≈M₁
...      | _ , M₁⟶[≤] ◅ M₁′⟶[≤]* , WM₁″
        with _ , _ , L₁′⟶[≤]* , M₁′⟶[≤]*′ , L₁″≈M₁″ ← ≈-diamond[≤] m′≤m (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢T L₁≈M₁ L₁⟶[≤] M₁⟶[≤] h[≤]L₁′ (-, M₁′⟶[≤]* , WM₁″)                                                      = -, -, ξ-of-⟶[ _ ≤]* (_ `$_) ξ-! WL₀ `$_ L₁′⟶[≤]*
                                                                                                                                                                                                   , ξ-of-⟶[ _ ≤]* (_`$ _) ξ-_`$? M₀′⟶[≤]*
                                                                                                                                                                                                       ◅◅ ξ-of-⟶[ _ ≤]* (_ `$_) ξ-! WM₀″ `$_ (M₁⟶[≤] ◅ M₁′⟶[≤]*′)
                                                                                                                                                                                                   , Γ~ ⊢ L₀≈M₀″ ⦂ ⊢⊸ `$ L₁″≈M₁″
≈-diamond[≤] m′≤m ⊢Γ ⊢S                     (Γ~ ⊢ L₀≈M₀ ⦂ ⊢⊸ `$ L₁≈M₁)                     (ξ-! WL₀ `$ L₁⟶[≤])                          (ξ-! WM₀ `$ M₁⟶[≤])                      h[≤]L′   h[≤]M′
  with ⊢T `⊸[ _ ] _ ← ⊢⊸
     | _ , h[≤]L₁′ ← halt[≤]-`$-inversion h[≤]L′
     | _ , h[≤]M₁′ ← halt[≤]-`$-inversion h[≤]M′
    with _ , _ , L₁′⟶[≤]* , M₁′⟶[≤]* , L₁″≈M₁″ ← ≈-diamond[≤] m′≤m (⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~) ⊢T L₁≈M₁ L₁⟶[≤] M₁⟶[≤] h[≤]L₁′ h[≤]M₁′                                                                        = -, -, ξ-of-⟶[ _ ≤]* (_ `$_) ξ-! WL₀ `$_ L₁′⟶[≤]*
                                                                                                                                                                                                   , ξ-of-⟶[ _ ≤]* (_ `$_) ξ-! WM₀ `$_ M₁′⟶[≤]*
                                                                                                                                                                                                   , Γ~ ⊢ L₀≈M₀ ⦂ ⊢⊸ `$ L₁″≈M₁″
≈-diamond[≤] m′≤m ⊢Γ (`↑[-⇒ m₀<m ][ _ ] ⊢S) (`lift[≤ m′≤m₀ ⇒-] L≈M)                        (ξ-`lift[-⇒-] L⟶[≤])                         (ξ-`lift[-⇒-] M⟶[≤])                     h[≤]lL′  h[≤]lM′
  with h[≤]L′ ← halt[≤]-`lift-inversion h[≤]lL′
     | h[≤]M′ ← halt[≤]-`lift-inversion h[≤]lM′
    with _ , _ , L′⟶[≤]* , M′⟶[≤]* , L″≈M″ ← ≈-diamond[≤] m′≤m₀ (⊢∧<ₘ⇒⊢ ⊢Γ m₀<m) ⊢S L≈M L⟶[≤] M⟶[≤] h[≤]L′ h[≤]M′                                                                                  = -, -, ξ-of-⟶[ _ ≤]* `lift[ _ ⇒ _ ] ξ-`lift[-⇒-] L′⟶[≤]*
                                                                                                                                                                                                   , ξ-of-⟶[ _ ≤]* `lift[ _ ⇒ _ ] ξ-`lift[-⇒-] M′⟶[≤]*
                                                                                                                                                                                                   , `lift[≤ m′≤m₀ ⇒-] L″≈M″
≈-diamond[≤] m′≤m ⊢Γ (`↑[-⇒ m₀<m ][ _ ] ⊢S) (`lift[≰ m′≰m₀ ⇒-] ⊢L ⊢M)                      (ξ-`lift[-⇒-] L⟶[≤])                         (ξ-`lift[-⇒-] M⟶[≤])                     h[≤]lL′  h[≤]lM′  = -, -, ε
                                                                                                                                                                                                   , ε
                                                                                                                                                                                                   , `lift[≰ m′≰m₀ ⇒-]
                                                                                                                                                                                                       (preservation[≤] (⊢∧<ₘ⇒⊢ ⊢Γ m₀<m) ⊢S ⊢L L⟶[≤])
                                                                                                                                                                                                       (preservation[≤] (⊢∧<ₘ⇒⊢ ⊢Γ m₀<m) ⊢S ⊢M M⟶[≤])

-- Mode safety
--
-- Note that they are almost immediate corollary of the diamond lemmas
--
mode-safety-helper : m′ ≤ₘ m →
                     ⊢[ m ] Γ →
                     ⊢[ m ] S ⦂⋆ →
                     Γ ⊢[ m ] L ≈[≥ m′ ] M ⦂ S →
                     (L⟶* : L ⟶* L′) →
                     WeakNorm L′ →
                     M ⟶* M′ →
                     WeakNorm M′ →
                     Acc ℕ._<_ (⟶*length L⟶*) →
                     ----------------------------
                     Γ ⊢[ m ] L′ ≈[≥ m′ ] M′ ⦂ S
mode-safety-helper m′≤m ⊢Γ ⊢S L≈M ε           VL′ M⟶*         VM′ rec            = WeakNorm≈⟶* ⊢Γ ⊢S L≈M VL′ M⟶*
mode-safety-helper m′≤m ⊢Γ ⊢S L≈M (L⟶ ◅ L′⟶*) VL″ ε           VM′ rec            = ≈-sym (WeakNorm≈⟶* ⊢Γ ⊢S (≈-sym L≈M) VM′ (L⟶ ◅ L′⟶*))
mode-safety-helper m′≤m ⊢Γ ⊢S L≈M (L⟶ ◅ L′⟶*) VL‴ (M⟶ ◅ M′⟶*) VM‴ (acc r)
  with _ , _ , L′⟶*′ , M′⟶*′ , L″≈M″ ← ≈-diamond m′≤m ⊢Γ ⊢S L≈M L⟶ M⟶ (-, L′⟶* , VL‴) (-, M′⟶* , VM‴)
    with L″⟶* , L″⟶*≤L′⟶* ← ⟶*-factor L′⟶*′ L′⟶* (⟶*length≤⟶*length-halt L′⟶*′ L′⟶* VL‴)
       | M″⟶* , _ ← ⟶*-factor M′⟶*′ M′⟶* (⟶*length≤⟶*length-halt M′⟶*′ M′⟶* VM‴) = mode-safety-helper m′≤m ⊢Γ ⊢S L″≈M″ L″⟶* VL‴ M″⟶* VM‴ (r _ (s≤s L″⟶*≤L′⟶*))

mode-safety[≤]-helper : m′ ≤ₘ m →
                        ⊢[ m ] Γ →
                        ⊢[ m ] S ⦂⋆ →
                        Γ ⊢[ m ] L ≈[≥ m′ ] M ⦂ S →
                        (L⟶[≤]* : L ⟶[ m″ ≤]* L′) →
                        DeferredTerm[ m″ ≤] L′ →
                        M ⟶[ m″ ≤]* M′ →
                        DeferredTerm[ m″ ≤] M′ →
                        Acc ℕ._<_ (⟶[≤]*length L⟶[≤]*) →
                        ---------------------------------
                        Γ ⊢[ m ] L′ ≈[≥ m′ ] M′ ⦂ S
mode-safety[≤]-helper m′≤m ⊢Γ ⊢S L≈M ε                 WL′ M⟶[≤]*            WM′ rec                     = DeferredTerm≈⟶[≤]* ⊢Γ ⊢S L≈M WL′ M⟶[≤]*
mode-safety[≤]-helper m′≤m ⊢Γ ⊢S L≈M (L⟶[≤] ◅ L′⟶[≤]*) WL″ ε                 WM′ rec                     = ≈-sym (DeferredTerm≈⟶[≤]* ⊢Γ ⊢S (≈-sym L≈M) WM′ (L⟶[≤] ◅ L′⟶[≤]*))
mode-safety[≤]-helper m′≤m ⊢Γ ⊢S L≈M (L⟶[≤] ◅ L′⟶[≤]*) WL‴ (M⟶[≤] ◅ M′⟶[≤]*) WM‴ (acc r)
  with _ , _ , L′⟶[≤]*′ , M′⟶[≤]*′ , L″≈M″ ← ≈-diamond[≤] m′≤m ⊢Γ ⊢S L≈M L⟶[≤] M⟶[≤] (-, L′⟶[≤]* , WL‴) (-, M′⟶[≤]* , WM‴)
    with L″⟶[≤]* , L″⟶[≤]*≤L′⟶[≤]* ← ⟶[≤]*-factor L′⟶[≤]*′ L′⟶[≤]* (⟶[≤]*length≤⟶[≤]*length-halt L′⟶[≤]*′ L′⟶[≤]* WL‴)
       | M″⟶[≤]* , _ ← ⟶[≤]*-factor M′⟶[≤]*′ M′⟶[≤]* (⟶[≤]*length≤⟶[≤]*length-halt M′⟶[≤]*′ M′⟶[≤]* WM‴) = mode-safety[≤]-helper m′≤m ⊢Γ ⊢S L″≈M″ L″⟶[≤]* WL‴ M″⟶[≤]* WM‴ (r _ (s≤s L″⟶[≤]*≤L′⟶[≤]*))

mode-safety : m′ ≤ₘ m →
              ⊢[ m ] Γ →
              ⊢[ m ] S ⦂⋆ →
              Γ ⊢[ m ] L ≈[≥ m′ ] M ⦂ S →
              L ⟶* L′ →
              WeakNorm L′ →
              M ⟶* M′ →
              WeakNorm M′ →
              ----------------------------
              Γ ⊢[ m ] L′ ≈[≥ m′ ] M′ ⦂ S
mode-safety m′≤m ⊢Γ ⊢S L≈M L⟶* VL′ M⟶* VM′ = mode-safety-helper m′≤m ⊢Γ ⊢S L≈M L⟶* VL′ M⟶* VM′ (ℕ.<-wellFounded _)

mode-safety[≤] : m′ ≤ₘ m →
                 ⊢[ m ] Γ →
                 ⊢[ m ] S ⦂⋆ →
                 Γ ⊢[ m ] L ≈[≥ m′ ] M ⦂ S →
                 (L⟶[≤]* : L ⟶[ m″ ≤]* L′) →
                 DeferredTerm[ m″ ≤] L′ →
                 M ⟶[ m″ ≤]* M′ →
                 DeferredTerm[ m″ ≤] M′ →
                 ---------------------------------
                 Γ ⊢[ m ] L′ ≈[≥ m′ ] M′ ⦂ S
mode-safety[≤] m′≤m ⊢Γ ⊢S L≈M L⟶[≤]* WL′ M⟶[≤]* WM′ = mode-safety[≤]-helper m′≤m ⊢Γ ⊢S L≈M L⟶[≤]* WL′ M⟶[≤]* WM′ (ℕ.<-wellFounded _)
