------------------------------------------------------------
-- Adjoint Sequent Calculus
------------------------------------------------------------

{-# OPTIONS --safe #-}
open import Calculus.Elevator.ModeSpec

module Calculus.Adjoint.Sequent {ℓ₁ ℓ₂} (ℳ : ModeSpec ℓ₁ ℓ₂) where
open ModeSpec ℳ

open import Agda.Primitive
open import Data.Bool as Bool using (true; false)
open import Data.List as List using ([]; _∷_; _++_; length)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Nat as ℕ using (ℕ; suc)
import Data.Nat.Properties as ℕ
open import Data.Product as × using (∃; _×_; _,_; -,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)

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

  cut  : Γ ~ Γ₀ ⊞ Δ₁ ++ Δ₁′ →
         m ≤ₘ m′ →
         ⊢[ m′ ] Γ₀ →
         ⊢[ m′ ] S ⦂⋆ →
         Γ₀ ⇛ S / m′ →
         Δ₁ ++ (S , m′ , true) ∷ Δ₁′ ⇛ T / m →
         --------------------------------------
         Γ ⇛ T / m

  `⊤R  : Γ is-all-del →
         ---------------
         Γ ⇛ `⊤ / m

  `⊸R  : (S , m , true) ∷ Γ ⇛ T / m →
         -----------------------------
         Γ ⇛ S `⊸ T / m

  `⊸L  : Γ ~ Γ₀ ⊞ Γ₁ →
         Γ₀ ~ Γ₂ ⊞ Γ₃ →
         x ⦂[ m ] S `⊸ T ∈ Γ₂ →
         ⊢[ m ] Γ₃ →
         Γ₃ ⇛ S / m →
         (T , m , true) ∷ Γ₁ ⇛ T′ / m′ →
         --------------------------------
         Γ ⇛ T′ / m′

  `↓R  : Γ ~ Γ₀ ⊞ Γ₁ →
         ⊢[ m ] Γ₀ →
         Γ₁ is-all-del →
         Γ₀ ⇛ S / m →
         ------------------------
         Γ ⇛ `↓[ m ⇒ m₀ ] S / m₀

  `↓L  : Γ ~ Γ₀ ⊞ Γ₁ →
         x ⦂[ m₀ ] `↓[ m₁ ⇒ m₀ ] S ∈ Γ₀ →
         (S , m₁ , true) ∷ Γ₁ ⇛ T / m →
         ---------------------------------
         Γ ⇛ T / m

  `↑R  : Γ ⇛ S / m →
         ------------------------
         Γ ⇛ `↑[ m ⇒ m₀ ] S / m₀

  `↑L  : Γ ~ Γ₀ ⊞ Γ₁ →
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
completeness ⊢Γ ⊢T (cut {Δ₁ = Δ₁} Γ~ m≤m′ ⊢Γ₀ ⊢S Γ₀⇛S Δ₁SΔ₁′⇛T)
  with _ , ⊢Δ₁Δ₁′ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~
    with ⊢Δ₁ , ⊢Δ₁′ ← ++⊢⇒⊢ Δ₁ ⊢Δ₁Δ₁′
    with _ , ⊢L ← completeness ⊢Γ₀ ⊢S Γ₀⇛S
       | _ , ⊢M ← completeness (⊢⇒++⊢ ⊢Δ₁ ((⊢S , valid m≤m′) ∷ ⊢Δ₁′)) ⊢T Δ₁SΔ₁′⇛T = -, true⊢[/]ˡ Δ₁ Γ~ ⊢Γ₀ ⊢L ⊢T ⊢M
completeness ⊢Γ ⊢T (`⊤R ΓDel) = -, `unit ΓDel
completeness ⊢Γ (⊢S `⊸[ _ ] ⊢T) (`⊸R SΓ⇛T)
  with _ , ⊢L ← completeness ((⊢S , valid ≤ₘ-refl) ∷ ⊢Γ) ⊢T SΓ⇛T = -, `λ⦂-∘ ⊢L
completeness ⊢Γ ⊢T (`⊸L Γ~ Γ₀~ x∈Γ₂ ⊢Γ₃ Γ₃⇛S′ T′Γ₁⇛T)
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

⇛weakening : ∀ Γ₀ →
             Γ′ is-all-del →
             Γ₀ ++ Γ₁ ⇛ T / m →
             -----------------------
             Γ₀ ++ Γ′ ++ Γ₁ ⇛ T / m
⇛weakening Γ₀ Γ′Del (init {x = x} x∈)
  with x ℕ.≥? length Γ₀
...  | no  x≱Γ₀ = init (<∧∈-++⇒∈-++-++ Γ₀ Γ′Del x∈ (ℕ.≰⇒> x≱Γ₀))
...  | yes x≥Γ₀ = init (≥∧∈-++⇒+-∈-++-++ Γ₀ Γ′Del x∈ x≥Γ₀)
⇛weakening Γ₀ Γ′Del (cut x x₁ x₂ x₃ Γ₀Γ₁⇛T Γ₀Γ₁⇛T₁) = {!!}
⇛weakening Γ₀ Γ′Del (`⊤R x) = {!!}
⇛weakening Γ₀ Γ′Del (`⊸R Γ₀Γ₁⇛T) = {!!}
⇛weakening Γ₀ Γ′Del (`⊸L x x₁ x₂ x₃ Γ₀Γ₁⇛T Γ₀Γ₁⇛T₁) = {!!}
⇛weakening Γ₀ Γ′Del (`↓R x x₁ x₂ Γ₀Γ₁⇛T) = {!!}
⇛weakening Γ₀ Γ′Del (`↓L x x₁ Γ₀Γ₁⇛T) = {!!}
⇛weakening Γ₀ Γ′Del (`↑R Γ₀Γ₁⇛T) = {!!}
⇛weakening Γ₀ Γ′Del (`↑L x x₁ x₂ Γ₀Γ₁⇛T) = {!!}

soundness : ⊢[ m ] Γ →
            ⊢[ m ] T ⦂⋆ →
            Γ ⊢[ m ] L ⦂ T →
            -----------------
            Γ ⇛ T / m
soundness ⊢Γ ⊢T (`unit ΓDel) = `⊤R ΓDel
soundness ⊢Γ (`↑[-⇒ m₀<m ][ _ ] ⊢T) (`lift[-⇒-] ⊢L) = `↑R (soundness (⊢∧<ₘ⇒⊢ ⊢Γ m₀<m) ⊢T ⊢L)
soundness ⊢Γ ⊢T (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑@(`↑[-⇒ m₀<m ][ _ ] _))
  with Γ₁ , Γ~ , Γ₁Del ← ∤⇒~⊞-is-all-delʳ Γ∤
     | ⊢Γ′ ← ⊢∧∤⇒⊢ ⊢Γ Γ∤ = cut {Δ₁ = []} Γ~ (<ₘ⇒≤ₘ m₀<m) ⊢Γ′  ⊢↑ (soundness ⊢Γ′ ⊢↑ ⊢L) (`↑L (to-left ∷ proj₂ (left-bias-~⊞ _)) (here Γ₁Del) ≤ₘ-refl (init (here (unusable ∷ left-bias-~⊞-is-all-del Γ₁))))
soundness ⊢Γ (`↓[-⇒ m₁<m₀ ][ _ ] ⊢T) (Γ∤ ⊢`return[-⇒-] ⊢L)
  with Γ₁ , Γ~ , Γ₁Del ← ∤⇒~⊞-is-all-delʳ Γ∤
     | ⊢Γ′ ← ⊢∧∤⇒⊢ ⊢Γ Γ∤ = `↓R Γ~ ⊢Γ′ Γ₁Del (soundness ⊢Γ′ ⊢T ⊢L)
soundness ⊢Γ ⊢T (_&_⊢`let-return[_⇒-]_⦂_`in_ {Γ₀′ = Γ₀′} Γ~ Γ₀∤ m≤m₁ ⊢L ⊢↓@(`↓[-⇒ m₁<m₀ ][ _ ] ⊢S) ⊢M)
  with m≤m₀ ← ≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m₁<m₀)
     | ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~
    with Γ₂ , Γ₀~ , Γ₂Del ← ∤⇒~⊞-is-all-delʳ Γ₀∤
       | ⊢Γ₀′ ← ⊢∧∤⇒⊢ ⊢Γ₀ Γ₀∤
      with Γ′ , Γ′~ , Γ~′ ← ~⊞-assocˡ Γ~ Γ₀~
        with _ , ⊢Γ′ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~′ = cut {Δ₁ = []} Γ~′ m≤m₁ ⊢Γ₀′ ⊢↓ (soundness ⊢Γ₀′ ⊢↓ ⊢L) (`↓L (to-left ∷ ~⊞-commute (proj₂ (left-bias-~⊞ _))) (here (left-bias-~⊞-is-all-del Γ′)) (⇛weakening (_ ∷ []) (unusable ∷ []) (soundness ((⊢S , valid m≤m₀) ∷ ⊢Γ′) ⊢T (~⊞-is-all-del∧⊢⇒⊢ʳ (to-right ∷ Γ′~) (unusable ∷ Γ₂Del) ⊢M))))
soundness ⊢Γ (⊢S `⊸[ _ ] ⊢T) (`λ⦂-∘ ⊢L) = `⊸R (soundness ((⊢S , valid ≤ₘ-refl) ∷ ⊢Γ) ⊢T ⊢L)
soundness ⊢Γ ⊢T (_⊢_⦂_`$_ {Γ₁ = Γ₁} Γ~ ⊢L ⊢⊸@(⊢S′ `⊸[ _ ] ⊢T′) ⊢M)
  with ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~ = cut {Δ₁ = []} Γ~ ≤ₘ-refl ⊢Γ₀ ⊢⊸ (soundness ⊢Γ₀ ⊢⊸ ⊢L) (`⊸L (to-left ∷ proj₂ (left-bias-~⊞ _)) (to-left ∷ ~⊞-commute (proj₂ (left-bias-~⊞ _))) (here (left-bias-~⊞-is-all-del Γ₁)) ((⊢⊸ , unusable) ∷ ⊢Γ₁) (⇛weakening [] (unusable ∷ []) (soundness ⊢Γ₁ ⊢S′ ⊢M)) (init (here (unusable ∷ left-bias-~⊞-is-all-del Γ₁))))
soundness ⊢Γ ⊢T (`# x∈Γ) = init x∈Γ
