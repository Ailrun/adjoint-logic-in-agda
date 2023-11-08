------------------------------------------------------------
-- Adjoint Sequent Calculus
------------------------------------------------------------

{-# OPTIONS --safe #-}
open import Calculus.Elevator.ModeSpec

module Calculus.Adjoint.Sequent {ℓ₁ ℓ₂} (ℳ : ModeSpec ℓ₁ ℓ₂) where
open ModeSpec ℳ

open import Agda.Primitive
open import Data.Bool as Bool using (true; false)
open import Data.List as List using ([]; _∷_)
open import Data.List.Relation.Unary.All as All using (All; _∷_)
open import Data.Nat as ℕ using (ℕ; suc)
open import Data.Product as × using (∃; _×_; _,_; -,_)
open import Relation.Nullary using (¬_)

import Calculus.Elevator.Syntax as S
import Calculus.Elevator.Typing as T
import Calculus.Elevator.Typing.Properties as TP
import Calculus.Elevator.Properties as P
open S ℳ
open T ℳ
open TP ℳ
open P ℳ

infix   4 _⇛_/_

data _⇛_/_ : Context → Type → Mode → Set (ℓ₁ ⊔ ℓ₂) where
  init : x ⦂[ m ] S ∈ Γ →
         -----------------
         Γ ⇛ S / m

  `⊤R : Γ is-all-del →
        ---------------
        Γ ⇛ `⊤ / m

  ‵⊸R : (S , m , true) ∷ Γ ⇛ T / m →
        -----------------------------
        Γ ⇛ S `⊸ T / m

  ‵⊸L : Γ ~ Γ₀ ⊞ Γ₁ →
        Γ₀ ~ Γ₂ ⊞ Γ₃ →
        x ⦂[ m ] S `⊸ T ∈ Γ₂ →
        ⊢[ m ] Γ₃ →
        Γ₃ ⇛ S / m →
        (T , m , true) ∷ Γ₁ ⇛ T′ / m′ →
        --------------------------------
        Γ ⇛ T′ / m′

  `↓R : Γ ~ Γ₀ ⊞ Γ₁ →
        ⊢[ m ] Γ₀ →
        Γ₁ is-all-del →
        Γ₀ ⇛ S / m →
        ------------------------
        Γ ⇛ `↓[ m ⇒ m₀ ] S / m₀

  `↓L : Γ ~ Γ₀ ⊞ Γ₁ →
        x ⦂[ m₀ ] `↓[ m₁ ⇒ m₀ ] S ∈ Γ₀ →
        (S , m₁ , true) ∷ Γ₁ ⇛ T / m →
        ---------------------------------
        Γ ⇛ T / m

  `↑R : Γ ⇛ S / m →
        ------------------------
        Γ ⇛ `↑[ m ⇒ m₀ ] S / m₀

  `↑L : Γ ~ Γ₀ ⊞ Γ₁ →
        x ⦂[ m₀ ] `↑[ m₁ ⇒ m₀ ] S ∈ Γ₀ →
        m ≤ₘ m₁ →
        (S , m₁ , true) ∷ Γ₁ ⇛ T / m →
        ---------------------------------
        Γ ⇛ T / m

completeness : ⊢[ m ] Γ →
               ⊢[ m ] T ⦂⋆ →
               Γ ⇛ T / m →
               -----------------------
               ∃ λ t → Γ ⊢[ m ] t ⦂ T
completeness ⊢Γ ⊢T (init x∈Γ) = -, `# x∈Γ
completeness ⊢Γ ⊢T (`⊤R ΓDel) = -, `unit ΓDel
completeness ⊢Γ (⊢S `⊸[ _ ] ⊢T) (‵⊸R SΓ⇛T)
  with _ , ⊢L ← completeness ((⊢S , valid ≤ₘ-refl) ∷ ⊢Γ) ⊢T SΓ⇛T = -, `λ⦂-∘ ⊢L
completeness ⊢Γ ⊢T (‵⊸L Γ~ Γ₀~ x∈Γ₂ ⊢Γ₃ Γ₃⇛S′ T′Γ₁⇛T)
  with ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~
    with ⊢Γ₂ , _ ← ⊢∧-~⊞-⇒⊢ ⊢Γ₀ Γ₀~
      with ⊢S′⊸T′@(⊢S′ `⊸[ _ ] ⊢T′) , m≤m₁ ← ⊢∧∈⇒⊢∧≤ₘ ⊢Γ₂ x∈Γ₂
         | _ , _ , ⊢Γ₅ , x∈Γ₅ , Γ₂~ , Γ₄Del ← ⊢∧∈⇒⊢∧∈∧~⊞∧is-all-delʳ ⊢Γ₂ x∈Γ₂
        with _ , Γ₀′~ , Γ₀~′ ← ~⊞-assocˡ Γ₀~ Γ₂~
          with _ , Γ′~ , Γ~′ ← ~⊞-assocˡ Γ~ (~⊞-commute Γ₀~′)
             | _ , ⊢L ← completeness ((⊢T′ , valid m≤m₁) ∷ ⊢Γ₁) ⊢T T′Γ₁⇛T
             | _ , ⊢M ← completeness ⊢Γ₃ ⊢S′ Γ₃⇛S′ = -, true⊢[/]ˡ [] Γ~′ (⊢∧⊢∧-~⊞-⇒⊢ ⊢Γ₅ ⊢Γ₃ Γ₀′~) (Γ₀′~ ⊢ `# x∈Γ₅ ⦂ ⊢S′⊸T′ `$ ⊢M) ⊢T (~⊞-is-all-del∧⊢⇒⊢ʳ (to-right ∷ Γ′~) (unusable ∷ Γ₄Del) ⊢L)
completeness ⊢Γ (`↓[-⇒ _ ][ _ ] ⊢T) (`↓R Γ~ ⊢Γ₀ Γ₁Del Γ₀⇛T)
  with _ , ⊢L ← completeness ⊢Γ₀ ⊢T Γ₀⇛T = -, ~⊞-is-all-del∧⊢⇒⊢ˡ Γ~ Γ₁Del (⊢∧≤⇒∤ ⊢Γ₀ ≤ₘ-refl ⊢`return[-⇒-] ⊢L)
completeness ⊢Γ ⊢T (`↓L Γ~ x∈Γ₀ SΓ₁⇛T)
  with ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~
    with ⊢↓S@(`↓[-⇒ m₁<m₀ ][ _ ] ⊢S) , m≤m₁ ← ⊢∧∈⇒⊢∧≤ₘ ⊢Γ₀ x∈Γ₀
       | _ , ⊢Γ₀′ , x∈Γ₀′ , Γ₀∤ ← ⊢∧∈⇒⊢∧∈∧∤ ⊢Γ₀ x∈Γ₀
      with _ , ⊢L ← completeness ((⊢S , valid (≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m₁<m₀))) ∷ ⊢Γ₁) ⊢T SΓ₁⇛T = -, Γ~ & Γ₀∤ ⊢`let-return[ m≤m₁ ⇒-] `# x∈Γ₀′ ⦂ ⊢↓S `in ⊢L
completeness ⊢Γ (`↑[-⇒ m₀<m ][ _ ] ⊢T) (`↑R Γ⇛T)
  with _ , ⊢L ← completeness (⊢∧<ₘ⇒⊢ ⊢Γ m₀<m) ⊢T Γ⇛T = -, `lift[-⇒-] ⊢L
completeness ⊢Γ ⊢T (`↑L Γ~ x∈Γ₀ m≤m₀ SΓ⇛T)
  with ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~
    with ⊢↑S@(`↑[-⇒ m₀<m₁ ][ _ ] ⊢S) , m≤m₁ ← ⊢∧∈⇒⊢∧≤ₘ ⊢Γ₀ x∈Γ₀
       | _ , ⊢Γ₀′ , x∈Γ₀′ , Γ₀∤ ← ⊢∧∈⇒⊢∧∈∧∤ ⊢Γ₀ x∈Γ₀
      with _ , Γ₀~ , Γ₀″Del ← ∤⇒~⊞-is-all-delʳ Γ₀∤
        with _ , Γ′~ , Γ~′ ← ~⊞-assocˡ Γ~ Γ₀~
          with _ , ⊢L ← completeness ((⊢S , valid m≤m₀) ∷ ⊢Γ₁) ⊢T SΓ⇛T = -, true⊢[/]ˡ [] Γ~′ (⊢∧<ₘ⇒⊢ ⊢Γ₀′ m₀<m₁) (⊢∧≤⇒∤ ⊢Γ₀′ ≤ₘ-refl ⊢`unlift[-⇒-] (`# x∈Γ₀′) ⦂ ⊢↑S) ⊢T (~⊞-is-all-del∧⊢⇒⊢ʳ (to-right ∷ Γ′~) (unusable ∷ Γ₀″Del) ⊢L)
