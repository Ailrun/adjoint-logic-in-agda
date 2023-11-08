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
import Data.List.Properties as List
import Data.List.Relation.Unary.All.Properties as All
open import Data.Nat as ℕ using (ℕ; suc)
import Data.Nat.Properties as ℕ
open import Data.Product as × using (∃; _×_; _,_; -,_; proj₁; proj₂)
open import Data.Sum as ⊎ using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

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
    with ⊢Δ₁ , ⊢Δ₁′ ← All.++⁻ Δ₁ ⊢Δ₁Δ₁′
      with _ , ⊢L ← completeness ⊢Γ₀ ⊢S Γ₀⇛S
         | _ , ⊢M ← completeness (All.++⁺ ⊢Δ₁ ((⊢S , valid m≤m′) ∷ ⊢Δ₁′)) ⊢T Δ₁SΔ₁′⇛T = -, true⊢[/]ˡ Δ₁ Γ~ ⊢Γ₀ ⊢L ⊢T ⊢M
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
completeness ⊢Γ ⊢T (`↑L Γ~ x∈Γ₀ m≤m₀ SΓ₁⇛T)
  with ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~
    with ⊢↑S@(`↑[-⇒ m₀<m₁ ][ _ ] ⊢S) , m≤m₁ ← ⊢∧∈⇒⊢∧≤ₘ ⊢Γ₀ x∈Γ₀
       | _ , ⊢Γ₀′ , x∈Γ₀′ , Γ₀∤ ← ⊢∧∈⇒⊢∧∈∧∤ ⊢Γ₀ x∈Γ₀
      with _ , Γ₀~ , Γ₀″Del ← ∤⇒~⊞-is-all-delʳ Γ₀∤
        with _ , Γ′~ , Γ~′ ← ~⊞-assocˡ Γ~ Γ₀~
          with _ , ⊢L ← completeness ((⊢S , valid m≤m₀) ∷ ⊢Γ₁) ⊢T SΓ₁⇛T = -, true⊢[/]ˡ [] Γ~′ (⊢∧<ₘ⇒⊢ ⊢Γ₀′ m₀<m₁) (⊢∧≤⇒∤ ⊢Γ₀′ ≤ₘ-refl ⊢`unlift[-⇒-] (`# x∈Γ₀′) ⦂ ⊢↑S) ⊢T (~⊞-is-all-del∧⊢⇒⊢ʳ (to-right ∷ Γ′~) (unusable ∷ Γ₀″Del) ⊢L)

++-eq-decompose : ∀ Γ₀ Δ₀ →
                  Γ₀ ++ Γ₁ ≡ Δ₀ ++ Δ₁ →
                  ∃ (λ Γ₁₀ → Δ₀ ≡ Γ₀ ++ Γ₁₀ × Γ₁ ≡ Γ₁₀ ++ Δ₁) ⊎ ∃ (λ Δ₁₀ → Γ₀ ≡ Δ₀ ++ Δ₁₀ × Δ₁ ≡ Δ₁₀ ++ Γ₁)
++-eq-decompose []       Δ₀ refl = inj₁ (-, refl , refl)
++-eq-decompose (x ∷ Γ₀) [] refl = inj₂ (-, refl , refl)
++-eq-decompose (x ∷ Γ₀) (x₁ ∷ Δ₀) eq
  with refl , eq′ ← List.∷-injective eq
    with ++-eq-decompose Γ₀ Δ₀ eq′
...    | inj₁ (_ , refl , refl) = inj₁ (-, refl , refl)
...    | inj₂ (_ , refl , refl) = inj₂ (-, refl , refl)

⇛weakening : ∀ Γ →
             ⊢[ m ] Γ ++ Γ′ ++ Γ″ →
             Γ′ is-all-del →
             ⊢[ m ] T ⦂⋆ →
             Γ ++ Γ″ ⇛ T / m →
             ----------------------
             Γ ++ Γ′ ++ Γ″ ⇛ T / m
⇛weakening Γ ⊢ΓΓ′Γ″ Γ′Del ⊢T (init {x = x} x∈ΓΓ″) = init (proj₂ ∈ΓΓ′Γ″)
  where
    ∈ΓΓ′Γ″ : ∃ λ x → x ⦂[ _ ] _ ∈ _
    ∈ΓΓ′Γ″
      with x ℕ.≥? length Γ
    ...  | no  x≱Γ = -, <∧∈-++⇒∈-++-++ Γ Γ′Del x∈ΓΓ″ (ℕ.≰⇒> x≱Γ)
    ...  | yes x≥Γ = -, ≥∧∈-++⇒+-∈-++-++ Γ Γ′Del x∈ΓΓ″ x≥Γ
⇛weakening {Γ′ = Γ′} Γ ⊢ΓΓ′Γ″ Γ′Del ⊢T (cut {Δ₁ = Δ₁} {Δ₁′ = Δ₁′} {m′ = m′} {S = S} ΓΓ″~ m≤m′ ⊢Γ₀ ⊢S Γ₀⇛S Δ₁SΔ₁′⇛T)
  with ⊢Γ , ⊢Γ′Γ″ ← All.++⁻ Γ ⊢ΓΓ′Γ″
    with ⊢Γ′ , ⊢Γ″ ← All.++⁻ Γ′ ⊢Γ′Γ″
       | Γ₀₀ , Γ₁₀ , Γ₀₁ , Γ₁₁ , refl , eq , Γ~ , Γ″~ ← ~⊞-preserves-++ Γ ΓΓ″~
      with ⊢Γ₀₀ , ⊢Γ₀₁ ← All.++⁻ Γ₀₀ ⊢Γ₀
         | ⊢Γ₁₀ ← ⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~
         | ⊢Γ₁₁ ← ⊢∧-~⊞-⇒⊢ʳ ⊢Γ″ Γ″~
         | ΓΓ′Γ″~ ← ~⊞-++⁺ Γ~ (~⊞-++⁺ (~⊞-commute (proj₂ (left-bias-~⊞ Γ′))) Γ″~)
        with ⊢Γ₀₀Γ′Γ₀₁ ← All.++⁺ (All.++⁻ˡ Γ₀₀ ⊢Γ₀) (All.++⁺ (left-bias-~⊞-⊢ _ ⊢Γ′) (All.++⁻ʳ Γ₀₀ ⊢Γ₀))
        with ++-eq-decompose Δ₁ Γ₁₀ eq
...        | inj₁ (Δ₁′₀ , refl , refl)
          rewrite sym (List.++-assoc Δ₁ ((S , m′ , true) ∷ Δ₁′₀) Γ₁₁)
                | List.++-assoc Δ₁ Δ₁′₀ (Γ′ ++ Γ₁₁) = cut ΓΓ′Γ″~ m≤m′ ⊢Γ₀₀Γ′Γ₀₁ ⊢S (⇛weakening Γ₀₀ ⊢Γ₀₀Γ′Γ₀₁ (left-bias-~⊞-is-all-del Γ′) ⊢S Γ₀⇛S) (subst (_⇛ _ / _) (List.++-assoc Δ₁ ((S , m′ , true) ∷ Δ₁′₀) (Γ′ ++ Γ₁₁)) (⇛weakening (Δ₁ ++ _ ∷ Δ₁′₀) (All.++⁺ (All.++⁺ (All.++⁻ˡ Δ₁ ⊢Γ₁₀) ((⊢S , valid m≤m′) ∷ (All.++⁻ʳ Δ₁ ⊢Γ₁₀))) (All.++⁺ ⊢Γ′ ⊢Γ₁₁)) Γ′Del ⊢T Δ₁SΔ₁′⇛T))
...        | inj₂ (Γ₁₁₀ , refl , refl)
          rewrite List.++-assoc Γ₁₀ Γ₁₁₀ ((S , m′ , true) ∷ Δ₁′)
                | sym (List.++-assoc Γ₁₀ Γ′ (Γ₁₁₀  ++ Δ₁′))
                | sym (List.++-assoc (Γ₁₀ ++ Γ′) Γ₁₁₀ Δ₁′) = cut ΓΓ′Γ″~ m≤m′ ⊢Γ₀₀Γ′Γ₀₁ ⊢S (⇛weakening Γ₀₀ ⊢Γ₀₀Γ′Γ₀₁ (left-bias-~⊞-is-all-del Γ′) ⊢S Γ₀⇛S) (subst (_⇛ _ / _) (trans (sym (List.++-assoc Γ₁₀ Γ′ (Γ₁₁₀ ++ _ ∷ Δ₁′))) (sym (List.++-assoc (Γ₁₀ ++ Γ′) Γ₁₁₀ (_ ∷ Δ₁′)))) (⇛weakening Γ₁₀ (All.++⁺ ⊢Γ₁₀ (All.++⁺ ⊢Γ′ (All.++⁺ (All.++⁻ˡ Γ₁₁₀ ⊢Γ₁₁) ((⊢S , valid m≤m′) ∷ All.++⁻ʳ Γ₁₁₀ ⊢Γ₁₁)))) Γ′Del ⊢T Δ₁SΔ₁′⇛T))
⇛weakening Γ ⊢ΓΓ′Γ″ Γ′Del ⊢T (`⊤R ΓΓ″Del) = `⊤R (All.++⁺ (All.++⁻ˡ Γ ΓΓ″Del) (All.++⁺ Γ′Del (All.++⁻ʳ Γ ΓΓ″Del)))
⇛weakening Γ ⊢ΓΓ′Γ″ Γ′Del (⊢S `⊸[ _ ] ⊢T) (`⊸R ΓΓ″⇛T) = `⊸R (⇛weakening (_ ∷ Γ) ((⊢S , valid ≤ₘ-refl) ∷ ⊢ΓΓ′Γ″) Γ′Del ⊢T ΓΓ″⇛T)
⇛weakening {Γ′ = Γ′} Γ ⊢ΓΓ′Γ″ Γ′Del ⊢T (`⊸L {x = x} ΓΓ″~ Γ₀~ x∈Γ₂ ⊢Γ₃ Γ₃⇛S′ T′Γ₁⇛T)
  with ⊢Γ , ⊢Γ′Γ″ ← All.++⁻ Γ ⊢ΓΓ′Γ″
    with ⊢Γ′ , ⊢Γ″ ← All.++⁻ Γ′ ⊢Γ′Γ″
       | Γ₀₀ , Γ₁₀ , _ , _ , refl , refl , Γ~ , Γ″~ ← ~⊞-preserves-++ Γ ΓΓ″~
      with Γ₂₀ , Γ₃₀ , _ , _ , refl , refl , Γ₀₀~ , Γ₀₁~ ← ~⊞-preserves-++ Γ₀₀ Γ₀~
         | ⊢Γ₁₀ ← ⊢∧-~⊞-⇒⊢ʳ ⊢Γ Γ~
         | ⊢Γ₁₁ ← ⊢∧-~⊞-⇒⊢ʳ ⊢Γ″ Γ″~
         | ⊢Γ₂ ← ⊢∧-~⊞-⇒⊢ˡ (⊢∧-~⊞-⇒⊢ˡ (All.++⁺ ⊢Γ ⊢Γ″) ΓΓ″~) Γ₀~
        with ⊢Γ₂₀ , ⊢Γ₂₁ ← All.++⁻ Γ₂₀ ⊢Γ₂
           | ⊢Γ₃₀ , ⊢Γ₃₁ ← All.++⁻ Γ₃₀ ⊢Γ₃
          with ⊢Γ₃₀Γ′₁Γ₃₁ ← All.++⁺ ⊢Γ₃₀ (All.++⁺ (left-bias-~⊞-⊢ _ ⊢Γ′) ⊢Γ₃₁)
            with ⊢S′ `⊸[ _ ] ⊢T′ , m≤m₁ ← ⊢∧∈⇒⊢∧≤ₘ (All.++⁺ ⊢Γ₂₀ ⊢Γ₂₁) x∈Γ₂ = `⊸L
                                                                                       (~⊞-++⁺ Γ~ (~⊞-++⁺ (~⊞-commute (proj₂ (left-bias-~⊞ _))) Γ″~))
                                                                                       (~⊞-++⁺ Γ₀₀~ (~⊞-++⁺ (~⊞-commute (proj₂ (left-bias-~⊞ _))) Γ₀₁~))
                                                                                       (proj₂ ∈ΓΓ′Γ″)
                                                                                       ⊢Γ₃₀Γ′₁Γ₃₁
                                                                                       (⇛weakening Γ₃₀ ⊢Γ₃₀Γ′₁Γ₃₁ (left-bias-~⊞-is-all-del Γ′) ⊢S′ Γ₃⇛S′)
                                                                                       (⇛weakening (_ ∷ Γ₁₀) ((⊢T′ , valid m≤m₁) ∷ All.++⁺ ⊢Γ₁₀ (All.++⁺ ⊢Γ′ ⊢Γ₁₁)) Γ′Del ⊢T T′Γ₁⇛T)
  where
    ∈ΓΓ′Γ″ : ∃ λ x → x ⦂[ _ ] _ ∈ _
    ∈ΓΓ′Γ″
      with x ℕ.≥? length Γ₂₀
    ...    | no  x≱Γ₂₀ = -, <∧∈-++⇒∈-++-++ Γ₂₀ (left-bias-~⊞-is-all-del (proj₁ (left-bias-~⊞ Γ′))) x∈Γ₂ (ℕ.≰⇒> x≱Γ₂₀)
    ...    | yes x≥Γ₂₀ = -, ≥∧∈-++⇒+-∈-++-++ Γ₂₀ (left-bias-~⊞-is-all-del (proj₁ (left-bias-~⊞ Γ′))) x∈Γ₂ x≥Γ₂₀
⇛weakening {Γ′ = Γ′} Γ ⊢ΓΓ′Γ″ Γ′Del (`↓[-⇒ m₁<m ][ _ ] ⊢T) (`↓R {m = m} ΓΓ″~ ⊢Γ₀ Γ₁Del Γ₀⇛T)
  with ⊢Γ , ⊢Γ′Γ″ ← All.++⁻ Γ ⊢ΓΓ′Γ″
    with ⊢Γ′ , ⊢Γ″ ← All.++⁻ Γ′ ⊢Γ′Γ″
       | Γ₀₀ , Γ₁₀ , _ , _ , refl , refl , Γ~ , Γ″~ ← ~⊞-preserves-++ Γ ΓΓ″~
       | _ , Γ′∤ , Γ′′Del ← is-all-del⇒∤ m Γ′Del
      with _ , Γ′~ , Γ′₁Del ← ∤⇒~⊞-is-all-delʳ Γ′∤
         | ⊢Γ′′ ← ⊢∧∤⇒⊢ ⊢Γ′ Γ′∤
        with ⊢Γ₀₀Γ′′Γ₀₁ ← All.++⁺ (All.++⁻ˡ Γ₀₀ ⊢Γ₀) (All.++⁺ ⊢Γ′′ (All.++⁻ʳ Γ₀₀ ⊢Γ₀)) = `↓R (~⊞-++⁺ Γ~ (~⊞-++⁺ Γ′~ Γ″~)) ⊢Γ₀₀Γ′′Γ₀₁ (All.++⁺ (All.++⁻ˡ Γ₁₀ Γ₁Del) (All.++⁺ Γ′₁Del (All.++⁻ʳ Γ₁₀ Γ₁Del))) (⇛weakening Γ₀₀ ⊢Γ₀₀Γ′′Γ₀₁ Γ′′Del ⊢T Γ₀⇛T)
⇛weakening {Γ′ = Γ′} Γ ⊢ΓΓ′Γ″ Γ′Del ⊢T (`↓L {x = x} {m = m} ΓΓ″~ x∈Γ₀ SΓ₁⇛T)
  with ⊢Γ , ⊢Γ′Γ″ ← All.++⁻ Γ ⊢ΓΓ′Γ″
    with ⊢Γ′ , ⊢Γ″ ← All.++⁻ Γ′ ⊢Γ′Γ″
       | Γ₀₀ , Γ₁₀ , _ , _ , refl , refl , Γ~ , Γ″~ ← ~⊞-preserves-++ Γ ΓΓ″~
      with ⊢Γ₀₀ , ⊢Γ₁₀ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~
         | ⊢Γ₀₁ , ⊢Γ₁₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ″ Γ″~
        with `↓[-⇒ m₁<m₀ ][ _ ] ⊢S , m≤m₁ ← ⊢∧∈⇒⊢∧≤ₘ (All.++⁺ ⊢Γ₀₀ ⊢Γ₀₁) x∈Γ₀ = `↓L (~⊞-++⁺ Γ~ (~⊞-++⁺ (~⊞-commute (proj₂ (left-bias-~⊞ _))) Γ″~)) (proj₂ ∈ΓΓ′Γ″) (⇛weakening (_ ∷ Γ₁₀) ((⊢S , valid (≤ₘ-trans m≤m₁ (<ₘ⇒≤ₘ m₁<m₀))) ∷ All.++⁺ ⊢Γ₁₀ (All.++⁺ ⊢Γ′ ⊢Γ₁₁)) Γ′Del ⊢T SΓ₁⇛T)
  where
    ∈ΓΓ′Γ″ : ∃ λ x → x ⦂[ _ ] _ ∈ _
    ∈ΓΓ′Γ″
      with x ℕ.≥? length Γ₀₀
    ...    | no  x≱Γ₀₀ = -, <∧∈-++⇒∈-++-++ Γ₀₀ (left-bias-~⊞-is-all-del Γ′) x∈Γ₀ (ℕ.≰⇒> x≱Γ₀₀)
    ...    | yes x≥Γ₀₀ = -, ≥∧∈-++⇒+-∈-++-++ Γ₀₀ (left-bias-~⊞-is-all-del Γ′) x∈Γ₀ x≥Γ₀₀
⇛weakening Γ ⊢ΓΓ′Γ″ Γ′Del (`↑[-⇒ m₀<m ][ _ ] ⊢T) (`↑R ΓΓ″⇛T) = `↑R (⇛weakening Γ (⊢∧<ₘ⇒⊢ ⊢ΓΓ′Γ″ m₀<m) Γ′Del ⊢T ΓΓ″⇛T)
⇛weakening {Γ′ = Γ′} Γ ⊢ΓΓ′Γ″ Γ′Del ⊢T (`↑L {x = x} ΓΓ″~ x∈Γ₀ m≤m₀ SΓ₁⇛T)
  with ⊢Γ , ⊢Γ′Γ″ ← All.++⁻ Γ ⊢ΓΓ′Γ″
    with ⊢Γ′ , ⊢Γ″ ← All.++⁻ Γ′ ⊢Γ′Γ″
       | Γ₀₀ , Γ₁₀ , _ , _ , refl , refl , Γ~ , Γ″~ ← ~⊞-preserves-++ Γ ΓΓ″~
      with ⊢Γ₀₀ , ⊢Γ₁₀ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~
         | ⊢Γ₀₁ , ⊢Γ₁₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ″ Γ″~
        with `↑[-⇒ m₁<m₀ ][ _ ] ⊢S , m≤m₁ ← ⊢∧∈⇒⊢∧≤ₘ (All.++⁺ ⊢Γ₀₀ ⊢Γ₀₁) x∈Γ₀ = `↑L (~⊞-++⁺ Γ~ (~⊞-++⁺ (~⊞-commute (proj₂ (left-bias-~⊞ _))) Γ″~)) (proj₂ ∈ΓΓ′Γ″) m≤m₀ (⇛weakening (_ ∷ Γ₁₀) ((⊢S , valid m≤m₀) ∷ All.++⁺ ⊢Γ₁₀ (All.++⁺ ⊢Γ′ ⊢Γ₁₁)) Γ′Del ⊢T SΓ₁⇛T)
  where
    ∈ΓΓ′Γ″ : ∃ λ x → x ⦂[ _ ] _ ∈ _
    ∈ΓΓ′Γ″
      with x ℕ.≥? length Γ₀₀
    ...    | no  x≱Γ₀₀ = -, <∧∈-++⇒∈-++-++ Γ₀₀ (left-bias-~⊞-is-all-del Γ′) x∈Γ₀ (ℕ.≰⇒> x≱Γ₀₀)
    ...    | yes x≥Γ₀₀ = -, ≥∧∈-++⇒+-∈-++-++ Γ₀₀ (left-bias-~⊞-is-all-del Γ′) x∈Γ₀ x≥Γ₀₀

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
        with _ , ⊢Γ′ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~′ = cut {Δ₁ = []} Γ~′ m≤m₁ ⊢Γ₀′ ⊢↓ (soundness ⊢Γ₀′ ⊢↓ ⊢L) (`↓L (to-left ∷ ~⊞-commute (proj₂ (left-bias-~⊞ _))) (here (left-bias-~⊞-is-all-del Γ′)) (⇛weakening (_ ∷ []) (((⊢S , valid m≤m₀)) ∷ (⊢↓ , unusable) ∷ ⊢Γ′) (unusable ∷ []) ⊢T (soundness ((⊢S , valid m≤m₀) ∷ ⊢Γ′) ⊢T (~⊞-is-all-del∧⊢⇒⊢ʳ (to-right ∷ Γ′~) (unusable ∷ Γ₂Del) ⊢M))))
soundness ⊢Γ (⊢S `⊸[ _ ] ⊢T) (`λ⦂-∘ ⊢L) = `⊸R (soundness ((⊢S , valid ≤ₘ-refl) ∷ ⊢Γ) ⊢T ⊢L)
soundness ⊢Γ ⊢T (_⊢_⦂_`$_ {Γ₁ = Γ₁} Γ~ ⊢L ⊢⊸@(⊢S′ `⊸[ _ ] ⊢T′) ⊢M)
  with ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~ = cut {Δ₁ = []} Γ~ ≤ₘ-refl ⊢Γ₀ ⊢⊸ (soundness ⊢Γ₀ ⊢⊸ ⊢L) (`⊸L (to-left ∷ proj₂ (left-bias-~⊞ _)) (to-left ∷ ~⊞-commute (proj₂ (left-bias-~⊞ _))) (here (left-bias-~⊞-is-all-del Γ₁)) ((⊢⊸ , unusable) ∷ ⊢Γ₁) (⇛weakening [] ((⊢⊸ , unusable) ∷ ⊢Γ₁) (unusable ∷ []) ⊢S′ (soundness ⊢Γ₁ ⊢S′ ⊢M)) (init (here (unusable ∷ left-bias-~⊞-is-all-del Γ₁))))
soundness ⊢Γ ⊢T (`# x∈Γ) = init x∈Γ
