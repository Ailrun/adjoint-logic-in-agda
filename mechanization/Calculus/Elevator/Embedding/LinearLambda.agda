------------------------------------------------------------
-- Translation of Original DILL [Barber & Plotkin 1996] into Adjoint DILL
------------------------------------------------------------
--
-- This module provides an translation relation between Original DILL
-- and Adjoint DILL, the proofs of completeness and soundness of the
-- relation regarding their typings, and bisimulation of the relation
-- regarding their operational semantics.
--

{-# OPTIONS --safe #-}
module Calculus.Elevator.Embedding.LinearLambda where

open import Agda.Primitive
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using ([]; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n; s≤s; _+_; _∸_)
import Data.Nat.Properties as ℕ
import Data.Nat.Induction as ℕ
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃; ∃₂; -,_)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary using (Rel; Antisymmetric; IsPartialOrder; IsDecPartialOrder)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; _≢_; ≢-sym)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (dec-yes; dec-no)

open import Calculus.GeneralOpSem using (wkidx[_↑_]_; idx[_/_]_along_)
open import Calculus.GeneralOpSem.Properties
open import Calculus.Elevator.Embedding.LinearLambda.ModeSpec
import Calculus.Elevator.Syntax as S
import Calculus.Elevator.Typing as T
import Calculus.Elevator.Typing.Properties as TP
import Calculus.Elevator.OpSem as O
open S ℳᴸ
open T ℳᴸ
open TP ℳᴸ
open O ℳᴸ
import Calculus.LinearLambda.Syntax as BP
import Calculus.LinearLambda.OpSem as BP
import Calculus.LinearLambda.Typing as BP
import Calculus.LinearLambda.Typing.Properties as BP
open BP.Variables

open ⟶* using (_◅◅_)

infix   4 _~ᵀ_
infix   4 _⍮_~ˣ_
infix   4 _⍮_~ˣ⁻
infix   4 _~ᵛ_∈ᵘ_
infix   4 _~ᵛ_∈ˡ_
infix   4 _~FVof_
infix   4 _⊢_~ᴹ_
infixr  5 _!∷ᵘ_
infixr  5 !∷ᵘ_
infixr  5 _?∷ˡ_
infixr  5 ?∷ˡ_
infixr  5 _!∷ˡ_
infixr  5 to-left!∷ˡ_
infixr  5 to-right!∷ˡ_
infixr  5 _++ˣ⁻_
infix   4 _is-all-dis⁰~ˣ⁻
infix   4 _~~ˣ⁻_⊞_

-- Pattern Synonyms for Syntax
--
pattern `↓ S = `↓[ uMode ⇒ lMode ] S
pattern `↑ S = `↑[ lMode ⇒ uMode ] S

pattern `lift L              = `lift[ lMode ⇒ uMode ] L
pattern `unlift L            = `unlift[ uMode ⇒ lMode ] L
pattern `return L            = `return[ uMode ⇒ lMode ] L
pattern `let-return_`in_ L M = `let-return[ lMode ⇒ uMode ] L `in M
pattern `λ⦂ˡ_∘_ S L          = `λ⦂[ lMode ] S ∘ L
pattern `unlift`lift L       = `unlift (`lift L)
pattern `unlift`#_ x         = `unlift (`# x)
pattern `return`lift L       = `return (`lift L)

-- Pattern Synonyms for Typing
--
pattern ⊢`⊤         = `⊤[ _ ]
pattern ⊢`↓ neq ⊢S  = `↓[-⇒ l≤u , neq ][ _ ] ⊢S
pattern ⊢`↑ neq ⊢S  = `↑[-⇒ l≤u , neq ][ _ ] ⊢S
pattern ⊢_`⊸_ ⊢S ⊢T = ⊢S `⊸[ _ ] ⊢T

pattern ⊢`lift ⊢L                        = `lift[-⇒-] ⊢L
pattern _⊢`unlift_⦂_ Γ∤ ⊢L ⊢S            = Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢S
pattern _⊢`return_ Γ∤ ⊢L                 = Γ∤ ⊢`return[-⇒-] ⊢L
pattern _⊢`let-return_⦂_`in_ Γ~ ⊢L ⊢S ⊢M = Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢S `in ⊢M
pattern _⊢`unlift`lift_⦂_ Γ∤ ⊢L ⊢S       = Γ∤ ⊢`unlift ⊢`lift ⊢L ⦂ ⊢S
pattern _⊢`unlift`#_⦂_ Γ∤ x∈ ⊢S          = Γ∤ ⊢`unlift `# x∈ ⦂ ⊢S
pattern _⊢`return`lift_ Γ∤ ⊢L            = Γ∤ ⊢`return ⊢`lift ⊢L

-- Pattern Synonyms for OpSem
--
pattern `unlift≤ VL = `unlift[≤ refl ⇒ lMode ] VL
pattern `return≤ VL = `return[≤ refl ⇒ lMode ] VL

pattern ξ-`lift L⟶                = ξ-`lift[-⇒-] L⟶
pattern ξ-`unlift L⟶              = ξ-`unlift[-⇒-] L⟶
pattern ξ-`unlift≤ L⟶             = ξ-`unlift[≤ refl ⇒-] L⟶
pattern ξ-`return L⟶              = ξ-`return[-⇒-] L⟶
pattern ξ-`return≤ L⟶             = ξ-`return[≤ refl ⇒-] L⟶
pattern ξ-`let-return_`in- L⟶     = ξ-`let-return[-⇒-] L⟶ `in-
pattern ξ-`let-return_`in? L⟶     = ξ-`let-return[-⇒-] L⟶ `in?
pattern ξ-`let-return!_`in_ WL M⟶ = ξ-`let-return[-⇒-]! WL `in M⟶
pattern ξ-`unlift`lift L⟶         = ξ-`unlift (ξ-`lift L⟶)
pattern ξ-`unlift≤`lift L⟶        = ξ-`unlift≤ (ξ-`lift L⟶)
pattern ξ-`return`lift L⟶         = ξ-`return (ξ-`lift L⟶)
pattern ξ-`return≤`lift L⟶        = ξ-`return≤ (ξ-`lift L⟶)

------------------------------------------------------------
-- Bisimilar Embedding Relation
------------------------------------------------------------

-- Embedding Relation for Types
--
data _~ᵀ_ : BP.Type → Type → Set where
  `⊤   : ------------
         BP.`⊤ ~ᵀ `⊤

  `!   : P ~ᵀ S →
         ---------------------
         BP.`! P ~ᵀ `↓ (`↑ S)

  _`⊸_ : P ~ᵀ S →
         Q ~ᵀ T →
         --------------------
         P BP.`⊸ Q ~ᵀ S `⊸ T

-- Embedding Relation for Contexts
--
data _⍮_~ˣ_ : BP.Context¹ → BP.Context⁰ → Context → Set where
  []    : --------------
          [] ⍮ [] ~ˣ []

  _!∷ᵘ_ : P ~ᵀ S →
          ψ₁ ⍮ ψ₀ ~ˣ Γ →
          -----------------------------------------
          P ∷ ψ₁ ⍮ ψ₀ ~ˣ (`↑ S , uMode , true) ∷ Γ

  _?∷ˡ_ : P ~ᵀ S →
          ψ₁ ⍮ ψ₀ ~ˣ Γ →
          -------------------------------------------------
          ψ₁ ⍮ (P , false) ∷ ψ₀ ~ˣ (S , lMode , false) ∷ Γ

  _!∷ˡ_ : P ~ᵀ S →
          ψ₁ ⍮ ψ₀ ~ˣ Γ →
          -----------------------------------------------
          ψ₁ ⍮ (P , true) ∷ ψ₀ ~ˣ (S , lMode , true) ∷ Γ

-- Embedding Relation for Context Skeleton
--
-- To track de Bruijn indices in the embedding relation,
-- We need to track the structure of the context embedding.
data _⍮_~ˣ⁻ : ℕ → ℕ → Set where
  []   : ----------
         0 ⍮ 0 ~ˣ⁻

  !∷ᵘ_ : k ⍮ k′ ~ˣ⁻ →
         ---------------
         suc k ⍮ k′ ~ˣ⁻

  ?∷ˡ_ : k ⍮ k′ ~ˣ⁻ →
         ---------------
         k ⍮ suc k′ ~ˣ⁻

  !∷ˡ_ : k ⍮ k′ ~ˣ⁻ →
         ---------------
         k ⍮ suc k′ ~ˣ⁻

-- Operations for The Context Embeddings
variable
  kk′~ kk′~′ kk′~″ kk′~‴ kk′~₀ kk′~₁ kk′~₂ kk′~₃ : k ⍮ k′ ~ˣ⁻

eraseˣ : ψ₁ ⍮ ψ₀ ~ˣ Γ → length ψ₁ ⍮ length ψ₀ ~ˣ⁻
eraseˣ []          = []
eraseˣ (_ !∷ᵘ ΔΓ~) = !∷ᵘ eraseˣ ΔΓ~
eraseˣ (_ ?∷ˡ ΔΓ~) = ?∷ˡ eraseˣ ΔΓ~
eraseˣ (_ !∷ˡ ΔΓ~) = !∷ˡ eraseˣ ΔΓ~

_++ˣ⁻_ : k ⍮ k′ ~ˣ⁻ → k″ ⍮ k‴ ~ˣ⁻ → k + k″ ⍮ k′ + k‴ ~ˣ⁻
[]         ++ˣ⁻ k″k‴~ = k″k‴~
(!∷ᵘ kk′~) ++ˣ⁻ k″k‴~ = !∷ᵘ (kk′~ ++ˣ⁻ k″k‴~)
(?∷ˡ kk′~) ++ˣ⁻ k″k‴~ = ?∷ˡ (kk′~ ++ˣ⁻ k″k‴~)
(!∷ˡ kk′~) ++ˣ⁻ k″k‴~ = !∷ˡ (kk′~ ++ˣ⁻ k″k‴~)

lengthˣ⁻ : k ⍮ k′ ~ˣ⁻ → ℕ
lengthˣ⁻ []         = 0
lengthˣ⁻ (!∷ᵘ kk′~) = suc (lengthˣ⁻ kk′~)
lengthˣ⁻ (?∷ˡ kk′~) = suc (lengthˣ⁻ kk′~)
lengthˣ⁻ (!∷ˡ kk′~) = suc (lengthˣ⁻ kk′~)

data _is-all-dis⁰~ˣ⁻ : k ⍮ k′ ~ˣ⁻ → Set where
  []   : ------------------
         [] is-all-dis⁰~ˣ⁻

  !∷ᵘ_ : kk′~ is-all-dis⁰~ˣ⁻ →
         ------------------------
         !∷ᵘ kk′~ is-all-dis⁰~ˣ⁻

  ?∷ˡ_ : kk′~ is-all-dis⁰~ˣ⁻ →
         ------------------------
         ?∷ˡ kk′~ is-all-dis⁰~ˣ⁻

data _~~ˣ⁻_⊞_ : k ⍮ k′ ~ˣ⁻ → k₀ ⍮ k₁ ~ˣ⁻ → k₂ ⍮ k₃ ~ˣ⁻ → Set where
  []           : ------------------------------
                 [] ~~ˣ⁻ [] ⊞ []

  !∷ᵘ_         : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                 ------------------------------------
                 !∷ᵘ kk′~ ~~ˣ⁻ !∷ᵘ kk′~₀ ⊞ !∷ᵘ kk′~₁

  ?∷ˡ_         : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                 ------------------------------------
                 ?∷ˡ kk′~ ~~ˣ⁻ ?∷ˡ kk′~₀ ⊞ ?∷ˡ kk′~₁

  to-left!∷ˡ_  : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                 ------------------------------------
                 !∷ˡ kk′~ ~~ˣ⁻ !∷ˡ kk′~₀ ⊞ ?∷ˡ kk′~₁

  to-right!∷ˡ_ : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                 ------------------------------------
                 !∷ˡ kk′~ ~~ˣ⁻ ?∷ˡ kk′~₀ ⊞ !∷ˡ kk′~₁

-- Embedding Relation for Terms
--
data _~ᵛ_∈ᵘ_ : ℕ → ℕ → k ⍮ k′ ~ˣ⁻ → Set where
  here     : kk′~ is-all-dis⁰~ˣ⁻ →
             ----------------------
             0 ~ᵛ 0 ∈ᵘ !∷ᵘ kk′~

  there!∷ᵘ : BP.u ~ᵛ u ∈ᵘ kk′~ →
             ------------------------------
             suc BP.u ~ᵛ suc u ∈ᵘ !∷ᵘ kk′~

  there?∷ˡ : BP.u ~ᵛ u ∈ᵘ kk′~ →
             --------------------------
             BP.u ~ᵛ suc u ∈ᵘ ?∷ˡ kk′~

data _~ᵛ_∈ˡ_ : ℕ → ℕ → k ⍮ k′ ~ˣ⁻ → Set where
  here     : kk′~ is-all-dis⁰~ˣ⁻ →
             ----------------------
             0 ~ᵛ 0 ∈ˡ !∷ˡ kk′~

  there!∷ᵘ : BP.x ~ᵛ x ∈ˡ kk′~ →
             --------------------------
             BP.x ~ᵛ suc x ∈ˡ !∷ᵘ kk′~

  there?∷ˡ : BP.x ~ᵛ x ∈ˡ kk′~ →
             ------------------------------
             suc BP.x ~ᵛ suc x ∈ˡ ?∷ˡ kk′~

data _⊢_~ᴹ_ : k ⍮ k′ ~ˣ⁻ → BP.Term → Term → Set where
  `unit            : kk′~ is-all-dis⁰~ˣ⁻ →
                     -------------------------
                     kk′~ ⊢ BP.`unit ~ᴹ `unit

  `bang            : kk′~ is-all-dis⁰~ˣ⁻ →
                     kk′~ ⊢ I ~ᴹ L →
                     ------------------------------------
                     kk′~ ⊢ BP.`bang I ~ᴹ `return`lift L

  _⊢`let-bang_`in_ : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                     kk′~₀ ⊢ I ~ᴹ L →
                     !∷ᵘ kk′~₁ ⊢ J ~ᴹ M →
                     ---------------------------------------------------
                     kk′~ ⊢ BP.`let-bang I `in J ~ᴹ `let-return L `in M

  `#¹_             : BP.u ~ᵛ u ∈ᵘ kk′~ →
                     ----------------------------------
                     kk′~ ⊢ BP.`#¹ BP.u ~ᴹ `unlift`# u

  `λ⦂_∘_           : P ~ᵀ S →
                     !∷ˡ kk′~ ⊢ I ~ᴹ L →
                     ----------------------------------
                     kk′~ ⊢ BP.`λ⦂ P ∘ I ~ᴹ `λ⦂ˡ S ∘ L

  _⊢_`$_           : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                     kk′~₀ ⊢ I ~ᴹ L →
                     kk′~₁ ⊢ J ~ᴹ M →
                     ---------------------------
                     kk′~ ⊢ I BP.`$ J ~ᴹ L `$ M

  `#⁰_             : BP.x ~ᵛ x ∈ˡ kk′~ →
                     ---------------------------
                     kk′~ ⊢ BP.`#⁰ BP.x ~ᴹ `# x

  `unlift-`lift    : kk′~ is-all-dis⁰~ˣ⁻ →
                     kk′~ ⊢ I ~ᴹ L →
                     ---------------------------
                     kk′~ ⊢ I ~ᴹ `unlift`lift L

-- A termination measure for _⊢_~ᴹ_
depth~ᴹ : kk′~ ⊢ I ~ᴹ L → ℕ
depth~ᴹ (`unit _)                = 0
depth~ᴹ (`bang _ ~L)             = suc (depth~ᴹ ~L)
depth~ᴹ (_ ⊢`let-bang ~L `in ~M) = suc (depth~ᴹ ~L ℕ.⊔ depth~ᴹ ~M)
depth~ᴹ (`#¹ u)                  = 0
depth~ᴹ (`λ⦂ ~S ∘ ~L)            = suc (depth~ᴹ ~L)
depth~ᴹ (_ ⊢ ~L `$ ~M)           = suc (depth~ᴹ ~L ℕ.⊔ depth~ᴹ ~M)
depth~ᴹ (`#⁰ x)                  = 0
depth~ᴹ (`unlift-`lift _ ~L)     = suc (depth~ᴹ ~L)

-- Free variables of Term represented in _⍮_~ˣ⁻
--
data _~FVof_ : k ⍮ k′ ~ˣ⁻ → Term → Set where
  FV`unit              : kk′~ is-all-dis⁰~ˣ⁻ →
                         ----------------------
                         kk′~ ~FVof `unit

  FV`lift              : kk′~ ~FVof L →
                         -------------------
                         kk′~ ~FVof `lift L

  FV`unlift            : kk′~ ~FVof L →
                         ---------------------
                         kk′~ ~FVof `unlift L

  FV`return            : kk′~ ~FVof L →
                         ---------------------
                         kk′~ ~FVof `return L

  FV_⊢`let-return_`in_ : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                         kk′~₀ ~FVof L →
                         !∷ᵘ kk′~₁ ~FVof M →
                         -------------------------------
                         kk′~ ~FVof `let-return L `in M

  FV`#¹_               : BP.u ~ᵛ u ∈ᵘ kk′~ →
                         --------------------
                         kk′~ ~FVof `# u

  FV`λ⦂-∘_             : !∷ˡ kk′~ ~FVof L →
                         ----------------------
                         kk′~ ~FVof `λ⦂ˡ S ∘ L

  FV_⊢_`$_             : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                         kk′~₀ ~FVof L →
                         kk′~₁ ~FVof M →
                         --------------------------
                         kk′~ ~FVof L `$ M

  FV`#⁰_               : BP.x ~ᵛ x ∈ˡ kk′~ →
                         --------------------
                         kk′~ ~FVof `# x

-- Properties of _~ᵀ_
--
-- In fact, _~ᵀ_ can be replaced by an injective function.
~ᵀ-det : P ~ᵀ S →
         P ~ᵀ S′ →
         ----------
         S ≡ S′
~ᵀ-det `⊤         `⊤           = refl
~ᵀ-det (`! ~S)    (`! ~S′)
  rewrite ~ᵀ-det ~S ~S′        = refl
~ᵀ-det (~S `⊸ ~T) (~S′ `⊸ ~T′)
  rewrite ~ᵀ-det ~S ~S′
        | ~ᵀ-det ~T ~T′        = refl

~ᵀ-inj : P ~ᵀ S →
         P′ ~ᵀ S →
         ----------
         P ≡ P′
~ᵀ-inj `⊤         `⊤           = refl
~ᵀ-inj (`! ~S)    (`! ~S′)
  rewrite ~ᵀ-inj ~S ~S′        = refl
~ᵀ-inj (~S `⊸ ~T) (~S′ `⊸ ~T′)
  rewrite ~ᵀ-inj ~S ~S′
        | ~ᵀ-inj ~T ~T′        = refl

~ᵀ-total : ∀ P →
           -----------------
           ∃ (λ S → P ~ᵀ S)
~ᵀ-total BP.`⊤       = -, `⊤
~ᵀ-total (A BP.`⊸ B) = -, proj₂ (~ᵀ-total A) `⊸ proj₂ (~ᵀ-total B)
~ᵀ-total (BP.`! A)   = -, `! (proj₂ (~ᵀ-total A))

~ᵀ⇒⊢ : P ~ᵀ S →
       ----------------
       ⊢[ lMode ] S ⦂⋆
~ᵀ⇒⊢ `⊤         = ⊢`⊤
~ᵀ⇒⊢ (`! ~S)    = ⊢`↓ (λ ()) (⊢`↑ (λ ()) (~ᵀ⇒⊢ ~S))
~ᵀ⇒⊢ (~S `⊸ ~T) = ⊢ ~ᵀ⇒⊢ ~S `⊸ ~ᵀ⇒⊢ ~T

∈ˡ⇒~ᵀ : ψ₁ ⍮ ψ₀ ~ˣ Γ →
        x ⦂[ lMode ] S ∈ Γ →
        ---------------------
        ∃ (λ A → A ~ᵀ S)
∈ˡ⇒~ᵀ (_  !∷ᵘ ~Γ) (there _ x∈) = ∈ˡ⇒~ᵀ ~Γ x∈
∈ˡ⇒~ᵀ (_  ?∷ˡ ~Γ) (there _ x∈) = ∈ˡ⇒~ᵀ ~Γ x∈
∈ˡ⇒~ᵀ (~S !∷ˡ ~Γ) (here _)     = -, ~S
∈ˡ⇒~ᵀ (_  !∷ˡ ~Γ) (there _ x∈) = ∈ˡ⇒~ᵀ ~Γ x∈

∈ᵘ⇒~ᵀ : ψ₁ ⍮ ψ₀ ~ˣ Γ →
        x ⦂[ uMode ] `↑ S ∈ Γ →
        ------------------------
        ∃ (λ A → A ~ᵀ S)
∈ᵘ⇒~ᵀ (~S !∷ᵘ ~Γ) (here _)     = -, ~S
∈ᵘ⇒~ᵀ (_  !∷ᵘ ~Γ) (there _ x∈) = ∈ᵘ⇒~ᵀ ~Γ x∈
∈ᵘ⇒~ᵀ (_  ?∷ˡ ~Γ) (there _ x∈) = ∈ᵘ⇒~ᵀ ~Γ x∈
∈ᵘ⇒~ᵀ (_  !∷ˡ ~Γ) (there _ x∈) = ∈ᵘ⇒~ᵀ ~Γ x∈

-- Properties of the Operations for the Context Embeddings
--
!∷ˡ-inj : !∷ˡ kk′~ ≡ !∷ˡ kk′~₀ →
          -----------------------
          kk′~ ≡ kk′~₀
!∷ˡ-inj refl = refl

!∷ᵘ-inj : ∀ {kk′~ kk′~₀ : k ⍮ k′ ~ˣ⁻} →
          _≡_ {A = suc k ⍮ k′ ~ˣ⁻} (!∷ᵘ kk′~) (!∷ᵘ kk′~₀) →
          --------------------------------------------------
          kk′~ ≡ kk′~₀
!∷ᵘ-inj refl = refl

lengthˣ⁻-respects-~~ˣ⁻⊞ : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                          ----------------------------------------------------------------
                          lengthˣ⁻ kk′~₀ ≡ lengthˣ⁻ kk′~ × lengthˣ⁻ kk′~₁ ≡ lengthˣ⁻ kk′~
lengthˣ⁻-respects-~~ˣ⁻⊞ []                       = refl , refl
lengthˣ⁻-respects-~~ˣ⁻⊞ (!∷ᵘ         kk′~~)
  with eq₀ , eq₁ ← lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~ = cong suc eq₀ , cong suc eq₁
lengthˣ⁻-respects-~~ˣ⁻⊞ (?∷ˡ         kk′~~)
  with eq₀ , eq₁ ← lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~ = cong suc eq₀ , cong suc eq₁
lengthˣ⁻-respects-~~ˣ⁻⊞ (to-left!∷ˡ  kk′~~)
  with eq₀ , eq₁ ← lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~ = cong suc eq₀ , cong suc eq₁
lengthˣ⁻-respects-~~ˣ⁻⊞ (to-right!∷ˡ kk′~~)
  with eq₀ , eq₁ ← lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~ = cong suc eq₀ , cong suc eq₁

~~ˣ⁻⊞-commute : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                --------------------------
                kk′~ ~~ˣ⁻ kk′~₁ ⊞ kk′~₀
~~ˣ⁻⊞-commute []                  = []
~~ˣ⁻⊞-commute (!∷ᵘ         kk′~~) = !∷ᵘ ~~ˣ⁻⊞-commute kk′~~
~~ˣ⁻⊞-commute (?∷ˡ         kk′~~) = ?∷ˡ ~~ˣ⁻⊞-commute kk′~~
~~ˣ⁻⊞-commute (to-left!∷ˡ  kk′~~) = to-right!∷ˡ ~~ˣ⁻⊞-commute kk′~~
~~ˣ⁻⊞-commute (to-right!∷ˡ kk′~~) = to-left!∷ˡ ~~ˣ⁻⊞-commute kk′~~

~~ˣ⁻⊞-assocˡ : ∀ {kk′~ : k ⍮ k′ ~ˣ⁻} →
               kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
               kk′~₀ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
               ---------------------------------------------------------------------------------
               Σ (k ⍮ k′ ~ˣ⁻) (λ kk′~₁′ → kk′~₁′ ~~ˣ⁻ kk′~₃ ⊞ kk′~₁ × kk′~ ~~ˣ⁻ kk′~₂ ⊞ kk′~₁′)
~~ˣ⁻⊞-assocˡ []                  []                    = -, [] , []
~~ˣ⁻⊞-assocˡ (!∷ᵘ         kk′~~) (!∷ᵘ         kk′~₀~)
  with _ , kk′~₁~ , kk′~~′ ← ~~ˣ⁻⊞-assocˡ kk′~~ kk′~₀~ = -, !∷ᵘ kk′~₁~ , !∷ᵘ kk′~~′
~~ˣ⁻⊞-assocˡ (?∷ˡ         kk′~~) (?∷ˡ         kk′~₀~)
  with _ , kk′~₁~ , kk′~~′ ← ~~ˣ⁻⊞-assocˡ kk′~~ kk′~₀~ = -, ?∷ˡ kk′~₁~ , ?∷ˡ kk′~~′
~~ˣ⁻⊞-assocˡ (to-left!∷ˡ  kk′~~) (to-left!∷ˡ  kk′~₀~)
  with _ , kk′~₁~ , kk′~~′ ← ~~ˣ⁻⊞-assocˡ kk′~~ kk′~₀~ = -, ?∷ˡ kk′~₁~ , to-left!∷ˡ kk′~~′
~~ˣ⁻⊞-assocˡ (to-left!∷ˡ  kk′~~) (to-right!∷ˡ kk′~₀~)
  with _ , kk′~₁~ , kk′~~′ ← ~~ˣ⁻⊞-assocˡ kk′~~ kk′~₀~ = -, to-left!∷ˡ kk′~₁~ , to-right!∷ˡ kk′~~′
~~ˣ⁻⊞-assocˡ (to-right!∷ˡ kk′~~) (?∷ˡ         kk′~₀~)
  with _ , kk′~₁~ , kk′~~′ ← ~~ˣ⁻⊞-assocˡ kk′~~ kk′~₀~ = -, to-right!∷ˡ kk′~₁~ , to-right!∷ˡ kk′~~′

~~ˣ⁻⊞-assocʳ : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
               kk′~₁ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
               --------------------------------------------------------------------
               ∃ (λ kk′~₀′ → kk′~₀′ ~~ˣ⁻ kk′~₀ ⊞ kk′~₂ × kk′~ ~~ˣ⁻ kk′~₀′ ⊞ kk′~₃)
~~ˣ⁻⊞-assocʳ kk′~~ kk′~₁~
  with _ , kk′~₁~ , kk′~~′ ← ~~ˣ⁻⊞-assocˡ (~~ˣ⁻⊞-commute kk′~~) (~~ˣ⁻⊞-commute kk′~₁~) = -, ~~ˣ⁻⊞-commute kk′~₁~ , ~~ˣ⁻⊞-commute kk′~~′

k⍮0~ˣ⁻-is-all-dis⁰~ˣ⁻ : ∀ (k₀0~ : k₀ ⍮ 0 ~ˣ⁻) →
                        ------------------------
                        k₀0~ is-all-dis⁰~ˣ⁻
k⍮0~ˣ⁻-is-all-dis⁰~ˣ⁻ []         = []
k⍮0~ˣ⁻-is-all-dis⁰~ˣ⁻ (!∷ᵘ k₀0~) = !∷ᵘ (k⍮0~ˣ⁻-is-all-dis⁰~ˣ⁻ k₀0~)

is-all-dis⁰~ˣ⁻-self~~ˣ⁻⊞ : kk′~ is-all-dis⁰~ˣ⁻ →
                           ----------------------
                           kk′~ ~~ˣ⁻ kk′~ ⊞ kk′~
is-all-dis⁰~ˣ⁻-self~~ˣ⁻⊞ []            = []
is-all-dis⁰~ˣ⁻-self~~ˣ⁻⊞ (!∷ᵘ kk′~Dis) = !∷ᵘ is-all-dis⁰~ˣ⁻-self~~ˣ⁻⊞ kk′~Dis
is-all-dis⁰~ˣ⁻-self~~ˣ⁻⊞ (?∷ˡ kk′~Dis) = ?∷ˡ is-all-dis⁰~ˣ⁻-self~~ˣ⁻⊞ kk′~Dis

~ˣ∧is-all-dis⇒is-all-del : ψ₁ ⍮ ψ₀ ~ˣ Γ →
                           ψ₀ BP.is-all-dis →
                           -------------------
                           Γ is-all-del
~ˣ∧is-all-dis⇒is-all-del []         ψ₀Dis          = []
~ˣ∧is-all-dis⇒is-all-del (_ !∷ᵘ ~Γ) ψ₀Dis          = weakening _ ∷ ~ˣ∧is-all-dis⇒is-all-del ~Γ ψ₀Dis
~ˣ∧is-all-dis⇒is-all-del (_ ?∷ˡ ~Γ) (refl ∷ ψ₀Dis) = unusable ∷ ~ˣ∧is-all-dis⇒is-all-del ~Γ ψ₀Dis
~ˣ∧is-all-dis⇒is-all-del (_ !∷ˡ ~Γ) (()   ∷ ψ₀Dis)

~ˣ∧is-all-del⇒is-all-dis : ψ₁ ⍮ ψ₀ ~ˣ Γ →
                           Γ is-all-del →
                           -----------------
                           ψ₀ BP.is-all-dis
~ˣ∧is-all-del⇒is-all-dis []         ΓDel                  = []
~ˣ∧is-all-del⇒is-all-dis (_ !∷ᵘ ~Γ) (_            ∷ ΓDel) = ~ˣ∧is-all-del⇒is-all-dis ~Γ ΓDel
~ˣ∧is-all-del⇒is-all-dis (_ ?∷ˡ ~Γ) (_            ∷ ΓDel) = refl ∷ ~ˣ∧is-all-del⇒is-all-dis ~Γ ΓDel
~ˣ∧is-all-del⇒is-all-dis (_ !∷ˡ ~Γ) (weakening () ∷ ΓDel)

~ˣ∧∤⇒is-all-dis : ψ₁ ⍮ ψ₀ ~ˣ Γ →
                  Γ ∤[ uMode ] Γ′ →
                  ------------------
                  ψ₀ BP.is-all-dis
~ˣ∧∤⇒is-all-dis []         []                             = []
~ˣ∧∤⇒is-all-dis (_ !∷ᵘ ~Γ) (d∤                      ∷ Γ∤) = ~ˣ∧∤⇒is-all-dis ~Γ Γ∤
~ˣ∧∤⇒is-all-dis (_ ?∷ˡ ~Γ) (d∤                      ∷ Γ∤) = refl ∷ ~ˣ∧∤⇒is-all-dis ~Γ Γ∤
~ˣ∧∤⇒is-all-dis (_ !∷ˡ ~Γ) (delete _ (weakening ()) ∷ Γ∤)

~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
                               ψ₀ BP.is-all-dis →
                               -------------------------
                               eraseˣ ~Γ is-all-dis⁰~ˣ⁻
~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ []         ψ₀Dis          = []
~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ (_ !∷ᵘ ~Γ) ψ₀Dis          = !∷ᵘ (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ ψ₀Dis)
~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ (_ !∷ˡ ~Γ) (()   ∷ ψ₀Dis)
~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ (_ ?∷ˡ ~Γ) (refl ∷ ψ₀Dis) = ?∷ˡ (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ ψ₀Dis)

~ˣ∧is-all-dis⁰~ˣ⁻⇒is-all-dis : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
                               eraseˣ ~Γ is-all-dis⁰~ˣ⁻ →
                               ---------------------------
                               ψ₀ BP.is-all-dis
~ˣ∧is-all-dis⁰~ˣ⁻⇒is-all-dis []         kk′~Dis       = []
~ˣ∧is-all-dis⁰~ˣ⁻⇒is-all-dis (_ !∷ᵘ ~Γ) (!∷ᵘ kk′~Dis) = ~ˣ∧is-all-dis⁰~ˣ⁻⇒is-all-dis ~Γ kk′~Dis
~ˣ∧is-all-dis⁰~ˣ⁻⇒is-all-dis (_ ?∷ˡ ~Γ) (?∷ˡ kk′~Dis) = refl ∷ (~ˣ∧is-all-dis⁰~ˣ⁻⇒is-all-dis ~Γ kk′~Dis)

eraseˣ-is-all-dis⁰~ˣ⁻⇒∤self : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
                              eraseˣ ~Γ is-all-dis⁰~ˣ⁻ →
                              ---------------------------
                              Γ ∤[ uMode ] Γ
eraseˣ-is-all-dis⁰~ˣ⁻⇒∤self []         []            = []
eraseˣ-is-all-dis⁰~ˣ⁻⇒∤self (_ !∷ᵘ ~Γ) (!∷ᵘ kk′~Dis) = keep refl ∷ eraseˣ-is-all-dis⁰~ˣ⁻⇒∤self ~Γ kk′~Dis
eraseˣ-is-all-dis⁰~ˣ⁻⇒∤self (_ ?∷ˡ ~Γ) (?∷ˡ kk′~Dis) = delete (λ ()) unusable ∷ eraseˣ-is-all-dis⁰~ˣ⁻⇒∤self ~Γ kk′~Dis

~ˣ∧∤⇒≡ : ψ₁ ⍮ ψ₀ ~ˣ Γ →
         Γ ∤[ uMode ] Γ′ →
         ------------------
         Γ′ ≡ Γ
~ˣ∧∤⇒≡ ~Γ Γ∤ = ∤-det Γ∤ (eraseˣ-is-all-dis⁰~ˣ⁻⇒∤self ~Γ (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ (~ˣ∧∤⇒is-all-dis ~Γ Γ∤)))

is-all-dis⁰~ˣ⁻-++⁺ : kk′~ is-all-dis⁰~ˣ⁻ →
                     kk′~′ is-all-dis⁰~ˣ⁻ →
                     -------------------------------
                     kk′~ ++ˣ⁻ kk′~′ is-all-dis⁰~ˣ⁻
is-all-dis⁰~ˣ⁻-++⁺ []            kk′~′Dis = kk′~′Dis
is-all-dis⁰~ˣ⁻-++⁺ (!∷ᵘ kk′~Dis) kk′~′Dis = !∷ᵘ is-all-dis⁰~ˣ⁻-++⁺ kk′~Dis kk′~′Dis
is-all-dis⁰~ˣ⁻-++⁺ (?∷ˡ kk′~Dis) kk′~′Dis = ?∷ˡ is-all-dis⁰~ˣ⁻-++⁺ kk′~Dis kk′~′Dis

is-all-dis⁰~ˣ⁻-++⁻ˡ : ∀ (kk′~ : k ⍮ k′ ~ˣ⁻) →
                      kk′~ ++ˣ⁻ kk′~′ is-all-dis⁰~ˣ⁻ →
                      ---------------------------------
                      kk′~ is-all-dis⁰~ˣ⁻
is-all-dis⁰~ˣ⁻-++⁻ˡ []         kk′~′Dis           = []
is-all-dis⁰~ˣ⁻-++⁻ˡ (!∷ᵘ kk′~) (!∷ᵘ kk′~kk′~′Dis) = !∷ᵘ is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~kk′~′Dis
is-all-dis⁰~ˣ⁻-++⁻ˡ (?∷ˡ kk′~) (?∷ˡ kk′~kk′~′Dis) = ?∷ˡ is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~kk′~′Dis

is-all-dis⁰~ˣ⁻-++⁻ʳ : ∀ (kk′~ : k ⍮ k′ ~ˣ⁻) →
                      kk′~ ++ˣ⁻ kk′~′ is-all-dis⁰~ˣ⁻ →
                      ---------------------------------
                      kk′~′ is-all-dis⁰~ˣ⁻
is-all-dis⁰~ˣ⁻-++⁻ʳ []         kk′~′Dis           = kk′~′Dis
is-all-dis⁰~ˣ⁻-++⁻ʳ (!∷ᵘ kk′~) (!∷ᵘ kk′~kk′~′Dis) = is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~kk′~′Dis
is-all-dis⁰~ˣ⁻-++⁻ʳ (?∷ˡ kk′~) (?∷ˡ kk′~kk′~′Dis) = is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~kk′~′Dis

~~ˣ⁻⊞-preserves-is-all-dis⁰~ˣ⁻ : kk′~ is-all-dis⁰~ˣ⁻ →
                                 kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                                 --------------------------------------------
                                 kk′~₀ is-all-dis⁰~ˣ⁻ × kk′~₁ is-all-dis⁰~ˣ⁻
~~ˣ⁻⊞-preserves-is-all-dis⁰~ˣ⁻ []            []                           = [] , []
~~ˣ⁻⊞-preserves-is-all-dis⁰~ˣ⁻ (!∷ᵘ kk′~Dis) (!∷ᵘ kk′~~)
  with kk′~₀Dis , kk′~₁Dis ← ~~ˣ⁻⊞-preserves-is-all-dis⁰~ˣ⁻ kk′~Dis kk′~~ = !∷ᵘ kk′~₀Dis , !∷ᵘ kk′~₁Dis
~~ˣ⁻⊞-preserves-is-all-dis⁰~ˣ⁻ (?∷ˡ kk′~Dis) (?∷ˡ kk′~~)
  with kk′~₀Dis , kk′~₁Dis ← ~~ˣ⁻⊞-preserves-is-all-dis⁰~ˣ⁻ kk′~Dis kk′~~ = ?∷ˡ kk′~₀Dis , ?∷ˡ kk′~₁Dis

~~ˣ⁻⊞⁻¹-preserves-is-all-dis⁰~ˣ⁻ : kk′~₀ is-all-dis⁰~ˣ⁻ →
                                   kk′~₁ is-all-dis⁰~ˣ⁻ →
                                   kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                                   --------------------------
                                   kk′~ is-all-dis⁰~ˣ⁻
~~ˣ⁻⊞⁻¹-preserves-is-all-dis⁰~ˣ⁻ []             []             []          = []
~~ˣ⁻⊞⁻¹-preserves-is-all-dis⁰~ˣ⁻ (!∷ᵘ kk′~₀Dis) (!∷ᵘ kk′~₁Dis) (!∷ᵘ kk′~~) = !∷ᵘ ~~ˣ⁻⊞⁻¹-preserves-is-all-dis⁰~ˣ⁻ kk′~₀Dis kk′~₁Dis kk′~~
~~ˣ⁻⊞⁻¹-preserves-is-all-dis⁰~ˣ⁻ (?∷ˡ kk′~₀Dis) (?∷ˡ kk′~₁Dis) (?∷ˡ kk′~~) = ?∷ˡ ~~ˣ⁻⊞⁻¹-preserves-is-all-dis⁰~ˣ⁻ kk′~₀Dis kk′~₁Dis kk′~~

~~ˣ⁻⊞-preserves-++ : ∀ (kk′~′ : k ⍮ k′ ~ˣ⁻) {kk′~″ : k″ ⍮ k‴ ~ˣ⁻} {kk′~₀ kk′~₁ : k + k″ ⍮ k′ + k‴ ~ˣ⁻} →
                     kk′~′ ++ˣ⁻ kk′~″ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                     ------------------------------------------------------------------------------------
                     Σ (k ⍮ k′ ~ˣ⁻) (λ kk′~′₀ →
                       Σ (k ⍮ k′ ~ˣ⁻) (λ kk′~′₁ →
                         Σ (k″ ⍮ k‴ ~ˣ⁻) (λ kk′~″₀ →
                           Σ (k″ ⍮ k‴ ~ˣ⁻) (λ kk′~″₁ → kk′~₀ ≡ kk′~′₀ ++ˣ⁻ kk′~″₀
                                                             × kk′~₁ ≡ kk′~′₁ ++ˣ⁻ kk′~″₁
                                                             × kk′~′ ~~ˣ⁻ kk′~′₀ ⊞ kk′~′₁
                                                             × kk′~″ ~~ˣ⁻ kk′~″₀ ⊞ kk′~″₁))))
~~ˣ⁻⊞-preserves-++ []         kk′~″~                                                       = -, -, -, -, refl , refl , [] , kk′~″~
~~ˣ⁻⊞-preserves-++ (!∷ᵘ kk′~) (!∷ᵘ         kk′~′kk′~″~)
  with _ , _ , _ , _ , refl , refl , kk′~′~ , kk′~″~ ← ~~ˣ⁻⊞-preserves-++ kk′~ kk′~′kk′~″~ = -, -, -, -, refl , refl , !∷ᵘ kk′~′~ , kk′~″~
~~ˣ⁻⊞-preserves-++ (?∷ˡ kk′~) (?∷ˡ         kk′~′kk′~″~)
  with _ , _ , _ , _ , refl , refl , kk′~′~ , kk′~″~ ← ~~ˣ⁻⊞-preserves-++ kk′~ kk′~′kk′~″~ = -, -, -, -, refl , refl , ?∷ˡ kk′~′~ , kk′~″~
~~ˣ⁻⊞-preserves-++ (!∷ˡ kk′~) (to-left!∷ˡ  kk′~′kk′~″~)
  with _ , _ , _ , _ , refl , refl , kk′~′~ , kk′~″~ ← ~~ˣ⁻⊞-preserves-++ kk′~ kk′~′kk′~″~ = -, -, -, -, refl , refl , to-left!∷ˡ kk′~′~ , kk′~″~
~~ˣ⁻⊞-preserves-++ (!∷ˡ kk′~) (to-right!∷ˡ kk′~′kk′~″~)
  with _ , _ , _ , _ , refl , refl , kk′~′~ , kk′~″~ ← ~~ˣ⁻⊞-preserves-++ kk′~ kk′~′kk′~″~ = -, -, -, -, refl , refl , to-right!∷ˡ kk′~′~ , kk′~″~

~~ˣ⁻⊞-++ : ∀ {kk′~ kk′~₀ kk′~₁ : k ⍮ k′ ~ˣ⁻} {kk′~′ kk′~′₀ kk′~′₁ : k″ ⍮ k‴ ~ˣ⁻} →
           kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
           kk′~′ ~~ˣ⁻ kk′~′₀ ⊞ kk′~′₁ →
           ------------------------------------------------------------------------
           kk′~ ++ˣ⁻ kk′~′ ~~ˣ⁻ kk′~₀ ++ˣ⁻ kk′~′₀ ⊞ kk′~₁ ++ˣ⁻ kk′~′₁
~~ˣ⁻⊞-++ []                  kk′~′~ = kk′~′~
~~ˣ⁻⊞-++ (!∷ᵘ         kk′~~) kk′~′~ = !∷ᵘ ~~ˣ⁻⊞-++ kk′~~ kk′~′~
~~ˣ⁻⊞-++ (?∷ˡ         kk′~~) kk′~′~ = ?∷ˡ ~~ˣ⁻⊞-++ kk′~~ kk′~′~
~~ˣ⁻⊞-++ (to-left!∷ˡ  kk′~~) kk′~′~ = to-left!∷ˡ ~~ˣ⁻⊞-++ kk′~~ kk′~′~
~~ˣ⁻⊞-++ (to-right!∷ˡ kk′~~) kk′~′~ = to-right!∷ˡ ~~ˣ⁻⊞-++ kk′~~ kk′~′~

~~ˣ⁻⊞-contraction-assocˡ : ∀ {kk′~ kk′~₀ kk′~₁ kk′~₂ kk′~₃ : k ⍮ k′ ~ˣ⁻} →
                           kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                           kk′~₀ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
                           kk′~₁ is-all-dis⁰~ˣ⁻ →
                           ---------------------------------------------------------
                           Σ (k ⍮ k′ ~ˣ⁻) (λ kk′~₂′ →
                             Σ (k ⍮ k′ ~ˣ⁻) (λ kk′~₃′ → kk′~₂′ ~~ˣ⁻ kk′~₂ ⊞ kk′~₁
                                                      × kk′~₃′ ~~ˣ⁻ kk′~₃ ⊞ kk′~₁
                                                      × kk′~ ~~ˣ⁻ kk′~₂′ ⊞ kk′~₃′))
~~ˣ⁻⊞-contraction-assocˡ []                 []                   []             = -, -, [] , [] , []
~~ˣ⁻⊞-contraction-assocˡ (!∷ᵘ        kk′~~) (!∷ᵘ         kk′~₀~) (!∷ᵘ kk′~₁Dis)
  with _ , _ , kk′~₂~ , kk′~₃~ , kk′~~′ ← ~~ˣ⁻⊞-contraction-assocˡ kk′~~ kk′~₀~ kk′~₁Dis = -, -, !∷ᵘ kk′~₂~ , !∷ᵘ kk′~₃~ , !∷ᵘ kk′~~′
~~ˣ⁻⊞-contraction-assocˡ (?∷ˡ        kk′~~) (?∷ˡ         kk′~₀~) (?∷ˡ kk′~₁Dis)
  with _ , _ , kk′~₂~ , kk′~₃~ , kk′~~′ ← ~~ˣ⁻⊞-contraction-assocˡ kk′~~ kk′~₀~ kk′~₁Dis = -, -, ?∷ˡ kk′~₂~ , ?∷ˡ kk′~₃~ , ?∷ˡ kk′~~′
~~ˣ⁻⊞-contraction-assocˡ (to-left!∷ˡ kk′~~) (to-left!∷ˡ  kk′~₀~) (?∷ˡ kk′~₁Dis)
  with _ , _ , kk′~₂~ , kk′~₃~ , kk′~~′ ← ~~ˣ⁻⊞-contraction-assocˡ kk′~~ kk′~₀~ kk′~₁Dis = -, -, to-left!∷ˡ kk′~₂~ , ?∷ˡ kk′~₃~ , to-left!∷ˡ kk′~~′
~~ˣ⁻⊞-contraction-assocˡ (to-left!∷ˡ kk′~~) (to-right!∷ˡ kk′~₀~) (?∷ˡ kk′~₁Dis)
  with _ , _ , kk′~₂~ , kk′~₃~ , kk′~~′ ← ~~ˣ⁻⊞-contraction-assocˡ kk′~~ kk′~₀~ kk′~₁Dis = -, -, ?∷ˡ kk′~₂~ , to-left!∷ˡ kk′~₃~ , to-right!∷ˡ kk′~~′

~~ˣ⁻⊞-contraction-assocʳ : ∀ {kk′~ kk′~₀ kk′~₁ kk′~₂ kk′~₃ : k ⍮ k′ ~ˣ⁻} →
                           kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                           kk′~₁ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
                           kk′~₀ is-all-dis⁰~ˣ⁻ →
                           ---------------------------------------------------------
                           Σ (k ⍮ k′ ~ˣ⁻) (λ kk′~₂′ →
                             Σ (k ⍮ k′ ~ˣ⁻) (λ kk′~₃′ → kk′~₂′ ~~ˣ⁻ kk′~₀ ⊞ kk′~₂
                                                      × kk′~₃′ ~~ˣ⁻ kk′~₀ ⊞ kk′~₃
                                                      × kk′~ ~~ˣ⁻ kk′~₂′ ⊞ kk′~₃′))
~~ˣ⁻⊞-contraction-assocʳ kk′~~ kk′~₁~ kk′~₀Dis
  with _ , _ , kk′~₂~ , kk′~₃~ , kk′~~′ ← ~~ˣ⁻⊞-contraction-assocˡ (~~ˣ⁻⊞-commute kk′~~) kk′~₁~ kk′~₀Dis = -, -, ~~ˣ⁻⊞-commute kk′~₂~ , ~~ˣ⁻⊞-commute kk′~₃~ , kk′~~′

~~ˣ⁻⊞-index : ∀ {kk′~ : k ⍮ k′ ~ˣ⁻} {kk′~₀ : k₀ ⍮ k₁ ~ˣ⁻} {kk′~₁ : k₂ ⍮ k₃ ~ˣ⁻} →
              kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
              --------------------------------------------------------------------
              k₀ ≡ k × k₂ ≡ k × k₁ ≡ k′ × k₃ ≡ k′
~~ˣ⁻⊞-index []                                       = refl , refl , refl , refl
~~ˣ⁻⊞-index (!∷ᵘ         kk′~~)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~ = refl , refl , refl , refl
~~ˣ⁻⊞-index (?∷ˡ         kk′~~)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~ = refl , refl , refl , refl
~~ˣ⁻⊞-index (to-left!∷ˡ  kk′~~)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~ = refl , refl , refl , refl
~~ˣ⁻⊞-index (to-right!∷ˡ kk′~~)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~ = refl , refl , refl , refl

!∷ᵘsubst : ∀ {k n m} (kn~ : k ⍮ n ~ˣ⁻) (eq : n ≡ m) →
           ----------------------------------------------------------------
           !∷ᵘ (subst (k ⍮_~ˣ⁻) eq kn~) ≡ subst (suc k ⍮_~ˣ⁻) eq (!∷ᵘ kn~)
!∷ᵘsubst _ refl = refl

!∷ˡsubst : ∀ {n m} (kn~ : k ⍮ n ~ˣ⁻) (eq : n ≡ m) →
           -----------------------------------------------------------------------
           !∷ˡ (subst (k ⍮_~ˣ⁻) eq kn~) ≡ subst (k ⍮_~ˣ⁻) (cong suc eq) (!∷ˡ kn~)
!∷ˡsubst _ refl = refl

?∷ˡsubst : ∀ {n m} (kn~ : k ⍮ n ~ˣ⁻) (eq : n ≡ m) →
           -----------------------------------------------------------------------
           ?∷ˡ (subst (k ⍮_~ˣ⁻) eq kn~) ≡ subst (k ⍮_~ˣ⁻) (cong suc eq) (?∷ˡ kn~)
?∷ˡsubst _ refl = refl

~~ˣ⁻subst⊞ʳ : ∀ {n m} {kk′~ : k ⍮ k′ ~ˣ⁻} {kk′~₀ : k₀ ⍮ n ~ˣ⁻} {kk′~₁ : k₂ ⍮ k₃ ~ˣ⁻} →
              (n≡m : n ≡ m) →
              kk′~ ~~ˣ⁻ subst (k₀ ⍮_~ˣ⁻) n≡m kk′~₀ ⊞ kk′~₁ →
              -------------------------------------------------------------------------
              kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁
~~ˣ⁻subst⊞ʳ refl kk′~~ = kk′~~

~~ˣ⁻subst⊞ʳ⁻¹ : ∀ {n m} {kk′~ : k ⍮ k′ ~ˣ⁻} {kk′~₀ : k₀ ⍮ n ~ˣ⁻} {kk′~₁ : k₂ ⍮ k₃ ~ˣ⁻} →
                (n≡m : n ≡ m) →
                kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                -------------------------------------------------------------------------
                kk′~ ~~ˣ⁻ subst (k₀ ⍮_~ˣ⁻) n≡m kk′~₀ ⊞ kk′~₁
~~ˣ⁻subst⊞ʳ⁻¹ refl kk′~~ = kk′~~

~~ˣ⁻⊞substʳ : ∀ {n m} {kk′~ : k ⍮ k′ ~ˣ⁻} {kk′~₀ : k₀ ⍮ k₁ ~ˣ⁻} {kk′~₁ : k₂ ⍮ n ~ˣ⁻} →
              (n≡m : n ≡ m) →
              kk′~ ~~ˣ⁻ kk′~₀ ⊞ subst (k₂ ⍮_~ˣ⁻) n≡m kk′~₁ →
              -------------------------------------------------------------------------
              kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁
~~ˣ⁻⊞substʳ refl kk′~~ = kk′~~

subst~~ˣ⁻⊞ʳ⁻¹ : ∀ {n m} {kk′~ : k ⍮ n ~ˣ⁻} {kk′~₀ : k₀ ⍮ k₁ ~ˣ⁻} {kk′~₁ : k₂ ⍮ k₃ ~ˣ⁻} →
                (n≡m : n ≡ m) →
                kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                -------------------------------------------------------------------------
                subst (k ⍮_~ˣ⁻) n≡m kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁
subst~~ˣ⁻⊞ʳ⁻¹ refl kk′~~ = kk′~~

subst~FVofʳ⁻¹ : ∀ {n m} {kk′~ : k ⍮ n ~ˣ⁻} →
                (n≡m : n ≡ m) →
                kk′~ ~FVof L →
                ---------------------------------
                subst (k ⍮_~ˣ⁻) n≡m kk′~ ~FVof L
subst~FVofʳ⁻¹ refl FVL = FVL

~ˣ-cancelˡ-~⊞ : (ψ₀~ : ψ₀ BP.~ ψ₀₀ ⊞ ψ₀₁) →
                (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
                (~Γ₀ : ψ₁ ⍮ ψ₀₀ ~ˣ Γ₀) →
                eraseˣ ~Γ ~~ˣ⁻ eraseˣ ~Γ₀ ⊞ kk′~₁ →
                ----------------------------------------------------------------------------------
                ∃ (λ Γ₁ → Γ ~ Γ₀ ⊞ Γ₁
                        × Σ (ψ₁ ⍮ ψ₀₁ ~ˣ Γ₁) (λ ~Γ₁ →
                                                let eq = proj₂ (BP.length-respects-~⊞ ψ₀~) in
                                                kk′~₁ ≡ subst (length ψ₁ ⍮_~ˣ⁻) eq (eraseˣ ~Γ₁)))
~ˣ-cancelˡ-~⊞ BP.[]                  []          []            []                  = -, [] , [] , refl
~ˣ-cancelˡ-~⊞ ψ₀~                    (~S !∷ᵘ ~Γ) (~S′ !∷ᵘ ~Γ₀) (!∷ᵘ kk′~~)
  with _ , Γ~ , ~Γ₁ , refl ← ~ˣ-cancelˡ-~⊞ ψ₀~ ~Γ ~Γ₀ kk′~~
     | refl ← ~ᵀ-det ~S ~S′                                                        = -, contraction _ ∷ Γ~ , ~S !∷ᵘ ~Γ₁ , !∷ᵘsubst (eraseˣ ~Γ₁) (proj₂ (BP.length-respects-~⊞ ψ₀~))
~ˣ-cancelˡ-~⊞ (BP.unusable BP.∷ ψ₀~) (~S ?∷ˡ ~Γ) (~S′ ?∷ˡ ~Γ₀) (?∷ˡ kk′~~)
  with _ , Γ~ , ~Γ₁ , refl ← ~ˣ-cancelˡ-~⊞ ψ₀~ ~Γ ~Γ₀ kk′~~
     | refl ← ~ᵀ-det ~S ~S′                                                        = -, unusable ∷ Γ~ , ~S ?∷ˡ ~Γ₁ , ?∷ˡsubst (eraseˣ ~Γ₁) (proj₂ (BP.length-respects-~⊞ ψ₀~))
~ˣ-cancelˡ-~⊞ (BP.to-right BP.∷ ψ₀~) (~S !∷ˡ ~Γ) (~S′ ?∷ˡ ~Γ₀) (to-right!∷ˡ kk′~~)
  with _ , Γ~ , ~Γ₁ , refl ← ~ˣ-cancelˡ-~⊞ ψ₀~ ~Γ ~Γ₀ kk′~~
     | refl ← ~ᵀ-det ~S ~S′                                                        = -, to-right ∷ Γ~ , ~S !∷ˡ ~Γ₁ , !∷ˡsubst (eraseˣ ~Γ₁) (proj₂ (BP.length-respects-~⊞ ψ₀~))
~ˣ-cancelˡ-~⊞ (BP.to-left  BP.∷ ψ₀~) (~S !∷ˡ ~Γ) (~S′ !∷ˡ ~Γ₀) (to-left!∷ˡ kk′~~)
  with _ , Γ~ , ~Γ₁ , refl ← ~ˣ-cancelˡ-~⊞ ψ₀~ ~Γ ~Γ₀ kk′~~
     | refl ← ~ᵀ-det ~S ~S′                                                        = -, to-left ∷ Γ~ , ~S ?∷ˡ ~Γ₁ , ?∷ˡsubst (eraseˣ ~Γ₁) (proj₂ (BP.length-respects-~⊞ ψ₀~))

~d⊞-contract-is-del : d [ m ]~d d₀ ⊞ d₁ →
                      d′ [ m ]~d d₀ ⊞ d₂ →
                      d″ [ m ]~d d₁ ⊞ d₃ →
                      d₂ [ m ]is-del →
                      d₃ [ m ]is-del →
                      ---------------------------------------------------------------------------
                      ∃₂ (λ d‴ dS → d‴ [ m ]~d d′ ⊞ d″ × d‴ [ m ]~d d ⊞ dS × dS [ m ]~d d₂ ⊞ d₃)
~d⊞-contract-is-del {m = uMode} (contraction _) (contraction _) (contraction _) _             d₃Del         = -, -, contraction _ , contraction _ , contraction _
~d⊞-contract-is-del {m = uMode} (contraction _) (contraction _) to-left         _             d₃Del         = -, -, contraction _ , contraction _ , to-left
~d⊞-contract-is-del {m = uMode} to-left         (contraction _) to-right        _             d₃Del         = -, -, contraction _ , contraction _ , contraction _
~d⊞-contract-is-del {m = uMode} to-left         (contraction _) unusable        _             d₃Del         = -, -, to-left , contraction _ , to-left
~d⊞-contract-is-del {m = uMode} (contraction _) to-left         (contraction _) d₂Del         d₃Del         = -, -, contraction _ , contraction _ , to-right
~d⊞-contract-is-del {m = uMode} (contraction _) to-left         to-left         d₂Del         d₃Del         = -, -, contraction _ , to-left , unusable
~d⊞-contract-is-del {m = uMode} to-left         to-left         to-right        d₂Del         (weakening _) = -, -, contraction _ , contraction _ , to-right 
~d⊞-contract-is-del {m = lMode} to-left         to-left         to-right        d₂Del         (weakening ())
~d⊞-contract-is-del             to-left         to-left         unusable        d₂Del         d₃Del         = -, -, to-left , to-left , unusable 
~d⊞-contract-is-del {m = uMode} to-right        to-right        (contraction x) (weakening _) d₃Del         = -, -, contraction _ , contraction _ , contraction _
~d⊞-contract-is-del {m = uMode} to-right        to-right        to-left         (weakening _) d₃Del         = -, -, contraction _ , contraction _ , to-left
~d⊞-contract-is-del {m = uMode} unusable        to-right        to-right        (weakening _) d₃Del         = -, -, contraction _ , to-right , contraction _
~d⊞-contract-is-del {m = uMode} unusable        to-right        unusable        (weakening _) d₃Del         = -, -, to-left , to-right , to-left
~d⊞-contract-is-del {m = lMode} d~              to-right        d″~             (weakening ())
~d⊞-contract-is-del             to-right        unusable        d″~             d₂Del         d₃Del         = -, -, ~d⊞-identityˡ _ , d″~ , ~d⊞-identityˡ _
~d⊞-contract-is-del             unusable        unusable        d″~             d₂Del         d₃Del         = -, -, ~d⊞-identityˡ _ , d″~ , ~d⊞-identityˡ _

~⊞-contract-is-all-del : Γ ~ Γ₀ ⊞ Γ₁ →
                         Γ′ ~ Γ₀ ⊞ Γ₂ →
                         Γ″ ~ Γ₁ ⊞ Γ₃ →
                         Γ₂ is-all-del →
                         Γ₃ is-all-del →
                         ------------------------------------------------------
                         ∃₂ (λ Γ‴ Δ → Γ‴ ~ Γ′ ⊞ Γ″ × Γ‴ ~ Γ ⊞ Δ × Δ ~ Γ₂ ⊞ Γ₃)
~⊞-contract-is-all-del []        []          []          []              []              = -, -, [] , [] , []
~⊞-contract-is-all-del (d~ ∷ Γ~) (d′~ ∷ Γ′~) (d″~ ∷ Γ″~) (d₂Del ∷ Γ₂Del) (d₃Del ∷ Γ₃Del)
  with _ , _ , d‴~ , d‴~′ , dS~ ← ~d⊞-contract-is-del d~ d′~ d″~ d₂Del d₃Del
     | _ , _ , Γ‴~ , Γ‴~′ , Δ~ ← ~⊞-contract-is-all-del Γ~ Γ′~ Γ″~ Γ₂Del Γ₃Del = -, -, d‴~ ∷ Γ‴~ , d‴~′ ∷ Γ‴~′ , dS~ ∷ Δ~

~⊞-preserves-~ˣ : Γ ~ Γ₀ ⊞ Γ₁ →
                  (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
                  ----------------------------------------------------------------------------------------------------
                  ∃₂ (λ Γ₀′ Γ₀″ →
                     ∃₂ (λ Γ₁′ Γ₁″ →
                        ∃₂ (λ ψ₀₀ ψ₀₁ → Γ ~ Γ₀′ ⊞ Γ₁′
                                      × Γ₀′ ~ Γ₀ ⊞ Γ₀″
                                      × Γ₀″ is-all-del
                                      × Γ₁′ ~ Γ₁ ⊞ Γ₁″
                                      × Γ₁″ is-all-del
                                      × ψ₀ BP.~ ψ₀₀ ⊞ ψ₀₁
                                      × Σ (ψ₁ ⍮ ψ₀₀ ~ˣ Γ₀′) (λ ~Γ₀′ →
                                          Σ (ψ₁ ⍮ ψ₀₁ ~ˣ Γ₁′) (λ ~Γ₁′ → eraseˣ ~Γ ~~ˣ⁻ eraseˣ ~Γ₀′ ⊞ eraseˣ ~Γ₁′)))))
~⊞-preserves-~ˣ []                   []                                                                                = -, -, -, -, -, -, []
                                                                                                                       , []
                                                                                                                       , []
                                                                                                                       , []
                                                                                                                       , []
                                                                                                                       , BP.[]
                                                                                                                       , []
                                                                                                                       , []
                                                                                                                       , []
~⊞-preserves-~ˣ (contraction _ ∷ Γ~) (~S !∷ᵘ ~Γ)
  with _ , _ , _ , _ , _ , _ , Γ~′ , Γ₀′~ , Γ₀″Del , Γ₁′~ , Γ₁″Del , ψ₀~ , ~Γ₀′ , ~Γ₁′ , kk′~~ ← ~⊞-preserves-~ˣ Γ~ ~Γ = -, -, -, -, -, -, contraction _ ∷ Γ~′
                                                                                                                       , contraction _ ∷ Γ₀′~
                                                                                                                       , weakening _ ∷ Γ₀″Del
                                                                                                                       , contraction _ ∷ Γ₁′~
                                                                                                                       , weakening _ ∷ Γ₁″Del
                                                                                                                       , ψ₀~
                                                                                                                       , ~S !∷ᵘ ~Γ₀′
                                                                                                                       , ~S !∷ᵘ ~Γ₁′
                                                                                                                       , !∷ᵘ kk′~~
~⊞-preserves-~ˣ (to-left       ∷ Γ~) (~S !∷ᵘ ~Γ)
  with _ , _ , _ , _ , _ , _ , Γ~′ , Γ₀′~ , Γ₀″Del , Γ₁′~ , Γ₁″Del , ψ₀~ , ~Γ₀′ , ~Γ₁′ , kk′~~ ← ~⊞-preserves-~ˣ Γ~ ~Γ = -, -, -, -, -, -, contraction _ ∷ Γ~′
                                                                                                                       , contraction _ ∷ Γ₀′~
                                                                                                                       , weakening _ ∷ Γ₀″Del
                                                                                                                       , to-right ∷ Γ₁′~
                                                                                                                       , weakening _ ∷ Γ₁″Del
                                                                                                                       , ψ₀~
                                                                                                                       , ~S !∷ᵘ ~Γ₀′
                                                                                                                       , ~S !∷ᵘ ~Γ₁′
                                                                                                                       , !∷ᵘ kk′~~
~⊞-preserves-~ˣ (to-right      ∷ Γ~) (~S !∷ᵘ ~Γ)
  with _ , _ , _ , _ , _ , _ , Γ~′ , Γ₀′~ , Γ₀″Del , Γ₁′~ , Γ₁″Del , ψ₀~ , ~Γ₀′ , ~Γ₁′ , kk′~~ ← ~⊞-preserves-~ˣ Γ~ ~Γ = -, -, -, -, -, -, contraction _ ∷ Γ~′
                                                                                                                       , to-right ∷ Γ₀′~
                                                                                                                       , weakening _ ∷ Γ₀″Del
                                                                                                                       , contraction _ ∷ Γ₁′~
                                                                                                                       , weakening _ ∷ Γ₁″Del
                                                                                                                       , ψ₀~
                                                                                                                       , ~S !∷ᵘ ~Γ₀′
                                                                                                                       , ~S !∷ᵘ ~Γ₁′
                                                                                                                       , !∷ᵘ kk′~~
~⊞-preserves-~ˣ (unusable      ∷ Γ~) (~S ?∷ˡ ~Γ)
  with _ , _ , _ , _ , _ , _ , Γ~′ , Γ₀′~ , Γ₀″Del , Γ₁′~ , Γ₁″Del , ψ₀~ , ~Γ₀′ , ~Γ₁′ , kk′~~ ← ~⊞-preserves-~ˣ Γ~ ~Γ = -, -, -, -, -, -, unusable ∷ Γ~′
                                                                                                                       , unusable ∷ Γ₀′~
                                                                                                                       , unusable ∷ Γ₀″Del
                                                                                                                       , unusable ∷ Γ₁′~
                                                                                                                       , unusable ∷ Γ₁″Del
                                                                                                                       , BP.unusable BP.∷ ψ₀~
                                                                                                                       , ~S ?∷ˡ ~Γ₀′
                                                                                                                       , ~S ?∷ˡ ~Γ₁′
                                                                                                                       , ?∷ˡ kk′~~
~⊞-preserves-~ˣ (to-left       ∷ Γ~) (~S !∷ˡ ~Γ)
  with _ , _ , _ , _ , _ , _ , Γ~′ , Γ₀′~ , Γ₀″Del , Γ₁′~ , Γ₁″Del , ψ₀~ , ~Γ₀′ , ~Γ₁′ , kk′~~ ← ~⊞-preserves-~ˣ Γ~ ~Γ = -, -, -, -, -, -, to-left ∷ Γ~′
                                                                                                                       , to-left ∷ Γ₀′~
                                                                                                                       , unusable ∷ Γ₀″Del
                                                                                                                       , unusable ∷ Γ₁′~
                                                                                                                       , unusable ∷ Γ₁″Del
                                                                                                                       , BP.to-left BP.∷ ψ₀~
                                                                                                                       , ~S !∷ˡ ~Γ₀′
                                                                                                                       , ~S ?∷ˡ ~Γ₁′
                                                                                                                       , to-left!∷ˡ kk′~~
~⊞-preserves-~ˣ (to-right      ∷ Γ~) (~S !∷ˡ ~Γ)
  with _ , _ , _ , _ , _ , _ , Γ~′ , Γ₀′~ , Γ₀″Del , Γ₁′~ , Γ₁″Del , ψ₀~ , ~Γ₀′ , ~Γ₁′ , kk′~~ ← ~⊞-preserves-~ˣ Γ~ ~Γ = -, -, -, -, -, -, to-right ∷ Γ~′
                                                                                                                       , unusable ∷ Γ₀′~
                                                                                                                       , unusable ∷ Γ₀″Del
                                                                                                                       , to-left ∷ Γ₁′~
                                                                                                                       , unusable ∷ Γ₁″Del
                                                                                                                       , BP.to-right BP.∷ ψ₀~
                                                                                                                       , ~S ?∷ˡ ~Γ₀′
                                                                                                                       , ~S !∷ˡ ~Γ₁′
                                                                                                                       , to-right!∷ˡ kk′~~

BP~⊞-preserves-~ˣ : ψ₀ BP.~ ψ₀₀ ⊞ ψ₀₁ →
                    (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
                    --------------------------------------------------------------------------------------
                    ∃₂ (λ Γ₀ Γ₁ → Γ ~ Γ₀ ⊞ Γ₁
                                × Σ (ψ₁ ⍮ ψ₀₀ ~ˣ Γ₀) (λ ~Γ₀ →
                                    Σ (ψ₁ ⍮ ψ₀₁ ~ˣ Γ₁) (λ ~Γ₁ → eraseˣ ~Γ ~~ˣ⁻ eraseˣ ~Γ₀ ⊞ eraseˣ ~Γ₁)))
BP~⊞-preserves-~ˣ BP.[]                  []                      = -, -, [] , [] , [] , []
BP~⊞-preserves-~ˣ ψ₀~                    (~S !∷ᵘ ~Γ)
  with _ , _ , Γ~ , ~Γ₀ , ~Γ₁ , kk′~~ ← BP~⊞-preserves-~ˣ ψ₀~ ~Γ = -, -, contraction _ ∷ Γ~ , ~S !∷ᵘ ~Γ₀ , ~S !∷ᵘ ~Γ₁ , !∷ᵘ kk′~~
BP~⊞-preserves-~ˣ (BP.unusable BP.∷ ψ₀~) (~S ?∷ˡ ~Γ)
  with _ , _ , Γ~ , ~Γ₀ , ~Γ₁ , kk′~~ ← BP~⊞-preserves-~ˣ ψ₀~ ~Γ = -, -, unusable ∷ Γ~ , ~S ?∷ˡ ~Γ₀ , ~S ?∷ˡ ~Γ₁ , ?∷ˡ kk′~~
BP~⊞-preserves-~ˣ (BP.to-left BP.∷ ψ₀~)  (~S !∷ˡ ~Γ)
  with _ , _ , Γ~ , ~Γ₀ , ~Γ₁ , kk′~~ ← BP~⊞-preserves-~ˣ ψ₀~ ~Γ = -, -, to-left ∷ Γ~ , ~S !∷ˡ ~Γ₀ , ~S ?∷ˡ ~Γ₁ , to-left!∷ˡ kk′~~
BP~⊞-preserves-~ˣ (BP.to-right BP.∷ ψ₀~) (~S !∷ˡ ~Γ)
  with _ , _ , Γ~ , ~Γ₀ , ~Γ₁ , kk′~~ ← BP~⊞-preserves-~ˣ ψ₀~ ~Γ = -, -, to-right ∷ Γ~ , ~S ?∷ˡ ~Γ₀ , ~S !∷ˡ ~Γ₁ , to-right!∷ˡ kk′~~

~~ˣ⁻⊞⁻¹-det : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
              kk′~′ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
              ---------------------------
              kk′~ ≡ kk′~′
~~ˣ⁻⊞⁻¹-det []                  []                   = refl
~~ˣ⁻⊞⁻¹-det (!∷ᵘ         kk′~~) (!∷ᵘ         kk′~′~) = cong !∷ᵘ_ (~~ˣ⁻⊞⁻¹-det kk′~~ kk′~′~)
~~ˣ⁻⊞⁻¹-det (?∷ˡ         kk′~~) (?∷ˡ         kk′~′~) = cong ?∷ˡ_ (~~ˣ⁻⊞⁻¹-det kk′~~ kk′~′~)
~~ˣ⁻⊞⁻¹-det (to-left!∷ˡ  kk′~~) (to-left!∷ˡ  kk′~′~) = cong !∷ˡ_ (~~ˣ⁻⊞⁻¹-det kk′~~ kk′~′~)
~~ˣ⁻⊞⁻¹-det (to-right!∷ˡ kk′~~) (to-right!∷ˡ kk′~′~) = cong !∷ˡ_ (~~ˣ⁻⊞⁻¹-det kk′~~ kk′~′~)

~ˣ∧∈ᵘ⇒~ᵛ∈ᵘ : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
             u ⦂[ uMode ] `↑ S ∈ Γ →
             --------------------------------
             ∃ (λ u′ → u′ ~ᵛ u ∈ᵘ eraseˣ ~Γ)
~ˣ∧∈ᵘ⇒~ᵛ∈ᵘ (~S ?∷ˡ ~Γ) (there unusable      u∈)
  with _ , ~u ← ~ˣ∧∈ᵘ⇒~ᵛ∈ᵘ ~Γ u∈                = -, there?∷ˡ ~u
~ˣ∧∈ᵘ⇒~ᵛ∈ᵘ (~S !∷ᵘ ~Γ) (here ΓDel)              = -, here (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ (~ˣ∧is-all-del⇒is-all-dis ~Γ ΓDel))
~ˣ∧∈ᵘ⇒~ᵛ∈ᵘ (~S !∷ᵘ ~Γ) (there (weakening _) u∈)
  with _ , ~u ← ~ˣ∧∈ᵘ⇒~ᵛ∈ᵘ ~Γ u∈                = -, there!∷ᵘ ~u

~ˣ∧∈ˡ⇒~ᵛ∈ˡ : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
             x ⦂[ lMode ] S ∈ Γ →
             --------------------------------
             ∃ (λ x′ → x′ ~ᵛ x ∈ˡ eraseˣ ~Γ)
~ˣ∧∈ˡ⇒~ᵛ∈ˡ (~S ?∷ˡ ~Γ) (there unusable       x∈)
  with _ , ~x ← ~ˣ∧∈ˡ⇒~ᵛ∈ˡ ~Γ x∈                 = -, there?∷ˡ ~x
~ˣ∧∈ˡ⇒~ᵛ∈ˡ (~S !∷ˡ ~Γ) (here ΓDel)               = -, here (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ (~ˣ∧is-all-del⇒is-all-dis ~Γ ΓDel))
~ˣ∧∈ˡ⇒~ᵛ∈ˡ (~S !∷ˡ ~Γ) (there (weakening ()) x∈)
~ˣ∧∈ˡ⇒~ᵛ∈ˡ (~S !∷ᵘ ~Γ) (there (weakening _)  x∈)
  with _ , ~x ← ~ˣ∧∈ˡ⇒~ᵛ∈ˡ ~Γ x∈                 = -, there!∷ᵘ ~x

~ˣ∧∈¹⇒~ᵛ∈ᵘ : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
             ψ₀ BP.is-all-dis →
             u′ BP.⦂ P ∈¹ ψ₁ →
             -------------------------------
             ∃ (λ u → u′ ~ᵛ u ∈ᵘ eraseˣ ~Γ)
~ˣ∧∈¹⇒~ᵛ∈ᵘ (~S !∷ᵘ ~Γ) ψ₀Dis          BP.here        = -, here (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ ψ₀Dis)
~ˣ∧∈¹⇒~ᵛ∈ᵘ (~S !∷ᵘ ~Γ) ψ₀Dis          (BP.there u′∈) = -, there!∷ᵘ (proj₂ (~ˣ∧∈¹⇒~ᵛ∈ᵘ ~Γ ψ₀Dis u′∈))
~ˣ∧∈¹⇒~ᵛ∈ᵘ (~S ?∷ˡ ~Γ) (refl ∷ ψ₀Dis) u′∈
  with _ , ~u ← ~ˣ∧∈¹⇒~ᵛ∈ᵘ ~Γ ψ₀Dis u′∈              = -, there?∷ˡ ~u
~ˣ∧∈¹⇒~ᵛ∈ᵘ (~S !∷ˡ ~Γ) (()   ∷ ψ₀Dis) u′∈

~ˣ∧∈⁰⇒~ᵛ∈ˡ : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
             x′ BP.⦂ P ∈⁰ ψ₀ →
             -------------------------------
             ∃ (λ x → x′ ~ᵛ x ∈ˡ eraseˣ ~Γ)
~ˣ∧∈⁰⇒~ᵛ∈ˡ (~S !∷ᵘ ~Γ) x′∈             = -, there!∷ᵘ (proj₂ (~ˣ∧∈⁰⇒~ᵛ∈ˡ ~Γ x′∈))
~ˣ∧∈⁰⇒~ᵛ∈ˡ (~S ?∷ˡ ~Γ) (BP.there x′∈)
  with _ , ~x ← ~ˣ∧∈⁰⇒~ᵛ∈ˡ ~Γ x′∈      = -, there?∷ˡ ~x
~ˣ∧∈⁰⇒~ᵛ∈ˡ (~S !∷ˡ ~Γ) (BP.here ψ₀Dis) = -, here (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ ψ₀Dis)

~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                              kk′~ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
                              kk′~₀ is-all-dis⁰~ˣ⁻ →
                              kk′~₂ is-all-dis⁰~ˣ⁻ →
                              --------------------------
                              kk′~₀ ≡ kk′~₂
~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique []                  []                   []             []             = refl
~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique (!∷ᵘ kk′~~)         (!∷ᵘ kk′~~′)         (!∷ᵘ kk′~₀Dis) (!∷ᵘ kk′~₂Dis) = cong !∷ᵘ_ (~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique kk′~~ kk′~~′ kk′~₀Dis kk′~₂Dis)
~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique (?∷ˡ kk′~~)         (?∷ˡ kk′~~′)         (?∷ˡ kk′~₀Dis) (?∷ˡ kk′~₂Dis) = cong ?∷ˡ_ (~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique kk′~~ kk′~~′ kk′~₀Dis kk′~₂Dis)
~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique (to-right!∷ˡ kk′~~) (to-right!∷ˡ kk′~~′) (?∷ˡ kk′~₀Dis) (?∷ˡ kk′~₂Dis) = cong ?∷ˡ_ (~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique kk′~~ kk′~~′ kk′~₀Dis kk′~₂Dis)

~ᵛ∈ᵘ-uniqueʳ : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
               kk′~ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
               u₀ ~ᵛ u ∈ᵘ kk′~₀ →
               u₂ ~ᵛ u ∈ᵘ kk′~₂ →
               --------------------------
               kk′~₀ ≡ kk′~₂
~ᵛ∈ᵘ-uniqueʳ (!∷ᵘ kk′~~)         (!∷ᵘ kk′~~′)         (here kk′~₀Dis) (here kk′~₂Dis) = cong !∷ᵘ_ (~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique kk′~~ kk′~~′ kk′~₀Dis kk′~₂Dis)
~ᵛ∈ᵘ-uniqueʳ (!∷ᵘ kk′~~)         (!∷ᵘ kk′~~′)         (there!∷ᵘ ~u)   (there!∷ᵘ ~u′)  = cong !∷ᵘ_ (~ᵛ∈ᵘ-uniqueʳ kk′~~ kk′~~′ ~u ~u′)
~ᵛ∈ᵘ-uniqueʳ (?∷ˡ kk′~~)         (?∷ˡ kk′~~′)         (there?∷ˡ ~u)   (there?∷ˡ ~u′)  = cong ?∷ˡ_ (~ᵛ∈ᵘ-uniqueʳ kk′~~ kk′~~′ ~u ~u′)
~ᵛ∈ᵘ-uniqueʳ (to-right!∷ˡ kk′~~) (to-right!∷ˡ kk′~~′) (there?∷ˡ ~u)   (there?∷ˡ ~u′)  = cong ?∷ˡ_ (~ᵛ∈ᵘ-uniqueʳ kk′~~ kk′~~′ ~u ~u′)

~ᵛ∈ᵘ-uniqueˡ : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
               kk′~ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
               u ~ᵛ u₀ ∈ᵘ kk′~₀ →
               u ~ᵛ u₂ ∈ᵘ kk′~₂ →
               --------------------------
               kk′~₀ ≡ kk′~₂
~ᵛ∈ᵘ-uniqueˡ (!∷ᵘ kk′~~)         (!∷ᵘ kk′~~′)         (here kk′~₀Dis) (here kk′~₂Dis) = cong !∷ᵘ_ (~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique kk′~~ kk′~~′ kk′~₀Dis kk′~₂Dis)
~ᵛ∈ᵘ-uniqueˡ (!∷ᵘ kk′~~)         (!∷ᵘ kk′~~′)         (there!∷ᵘ ~u)   (there!∷ᵘ ~u′)  = cong !∷ᵘ_ (~ᵛ∈ᵘ-uniqueˡ kk′~~ kk′~~′ ~u ~u′)
~ᵛ∈ᵘ-uniqueˡ (?∷ˡ kk′~~)         (?∷ˡ kk′~~′)         (there?∷ˡ ~u)   (there?∷ˡ ~u′)  = cong ?∷ˡ_ (~ᵛ∈ᵘ-uniqueˡ kk′~~ kk′~~′ ~u ~u′)
~ᵛ∈ᵘ-uniqueˡ (to-right!∷ˡ kk′~~) (to-right!∷ˡ kk′~~′) (there?∷ˡ ~u)   (there?∷ˡ ~u′)  = cong ?∷ˡ_ (~ᵛ∈ᵘ-uniqueˡ kk′~~ kk′~~′ ~u ~u′)

~ᵛ∈ˡ-uniqueʳ : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
               kk′~ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
               x₀ ~ᵛ x ∈ˡ kk′~₀ →
               x₂ ~ᵛ x ∈ˡ kk′~₂ →
               --------------------------
               kk′~₀ ≡ kk′~₂
~ᵛ∈ˡ-uniqueʳ (!∷ᵘ kk′~~)         (!∷ᵘ kk′~~′)         (there!∷ᵘ ~x)   (there!∷ᵘ ~x′)  = cong !∷ᵘ_ (~ᵛ∈ˡ-uniqueʳ kk′~~ kk′~~′ ~x ~x′)
~ᵛ∈ˡ-uniqueʳ (?∷ˡ kk′~~)         (?∷ˡ kk′~~′)         (there?∷ˡ ~x)   (there?∷ˡ ~x′)  = cong ?∷ˡ_ (~ᵛ∈ˡ-uniqueʳ kk′~~ kk′~~′ ~x ~x′)
~ᵛ∈ˡ-uniqueʳ (to-left!∷ˡ kk′~~)  (to-left!∷ˡ kk′~~′)  (here kk′~₀Dis) (here kk′~₂Dis) = cong !∷ˡ_ (~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique kk′~~ kk′~~′ kk′~₀Dis kk′~₂Dis)
~ᵛ∈ˡ-uniqueʳ (to-right!∷ˡ kk′~~) (to-right!∷ˡ kk′~~′) (there?∷ˡ ~x)   (there?∷ˡ ~x′)  = cong ?∷ˡ_ (~ᵛ∈ˡ-uniqueʳ kk′~~ kk′~~′ ~x ~x′)

~ᵛ∈ˡ-uniqueˡ : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
               kk′~ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
               x ~ᵛ x₀ ∈ˡ kk′~₀ →
               x ~ᵛ x₂ ∈ˡ kk′~₂ →
               --------------------------
               kk′~₀ ≡ kk′~₂
~ᵛ∈ˡ-uniqueˡ (!∷ᵘ kk′~~)         (!∷ᵘ kk′~~′)         (there!∷ᵘ ~x)   (there!∷ᵘ ~x′)  = cong !∷ᵘ_ (~ᵛ∈ˡ-uniqueˡ kk′~~ kk′~~′ ~x ~x′)
~ᵛ∈ˡ-uniqueˡ (?∷ˡ kk′~~)         (?∷ˡ kk′~~′)         (there?∷ˡ ~x)   (there?∷ˡ ~x′)  = cong ?∷ˡ_ (~ᵛ∈ˡ-uniqueˡ kk′~~ kk′~~′ ~x ~x′)
~ᵛ∈ˡ-uniqueˡ (to-left!∷ˡ kk′~~)  (to-left!∷ˡ kk′~~′)  (here kk′~₀Dis) (here kk′~₂Dis) = cong !∷ˡ_ (~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique kk′~~ kk′~~′ kk′~₀Dis kk′~₂Dis)
~ᵛ∈ˡ-uniqueˡ (to-right!∷ˡ kk′~~) (to-right!∷ˡ kk′~~′) (there?∷ˡ ~x)   (there?∷ˡ ~x′)  = cong ?∷ˡ_ (~ᵛ∈ˡ-uniqueˡ kk′~~ kk′~~′ ~x ~x′)

~ᵛ∈ᵘ∧~ᵛ∈ˡ⇒⊥ : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
              kk′~ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
              u₀ ~ᵛ u ∈ᵘ kk′~₀ →
              x₂ ~ᵛ u ∈ˡ kk′~₂ →
              --------------------------
              ⊥
~ᵛ∈ᵘ∧~ᵛ∈ˡ⇒⊥ (!∷ᵘ kk′~~)         (!∷ᵘ kk′~~′)         (there!∷ᵘ ~u) (there!∷ᵘ ~u′) = ~ᵛ∈ᵘ∧~ᵛ∈ˡ⇒⊥ kk′~~ kk′~~′ ~u ~u′
~ᵛ∈ᵘ∧~ᵛ∈ˡ⇒⊥ (?∷ˡ kk′~~)         (?∷ˡ kk′~~′)         (there?∷ˡ ~u) (there?∷ˡ ~u′) = ~ᵛ∈ᵘ∧~ᵛ∈ˡ⇒⊥ kk′~~ kk′~~′ ~u ~u′
~ᵛ∈ᵘ∧~ᵛ∈ˡ⇒⊥ (to-right!∷ˡ kk′~~) (to-right!∷ˡ kk′~~′) (there?∷ˡ ~u) (there?∷ˡ ~u′) = ~ᵛ∈ᵘ∧~ᵛ∈ˡ⇒⊥ kk′~~ kk′~~′ ~u ~u′

-- Properties of ~FVof
--
~FVof-unique : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
               kk′~ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
               kk′~₀ ~FVof L →
               kk′~₂ ~FVof L →
               --------------------------
               kk′~₀ ≡ kk′~₂
~FVof-unique kk′~~ kk′~~′ (FV`unit kk′~₀Dis)                   (FV`unit kk′~₂Dis)                     = ~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique kk′~~ kk′~~′ kk′~₀Dis kk′~₂Dis
~FVof-unique kk′~~ kk′~~′ (FV`lift FVL)                        (FV`lift FVL′)                         = ~FVof-unique kk′~~ kk′~~′ FVL FVL′
~FVof-unique kk′~~ kk′~~′ (FV`unlift FVL)                      (FV`unlift FVL′)                       = ~FVof-unique kk′~~ kk′~~′ FVL FVL′
~FVof-unique kk′~~ kk′~~′ (FV`return FVL)                      (FV`return FVL′)                       = ~FVof-unique kk′~~ kk′~~′ FVL FVL′
~FVof-unique kk′~~ kk′~~′ (FV kk′~₀~ ⊢`let-return FVL `in FVM) (FV kk′~₂~ ⊢`let-return FVL′ `in FVM′)
  with kk′~₄′ , kk′~₄′~ , kk′~~₄ ← ~~ˣ⁻⊞-assocˡ kk′~~ (~~ˣ⁻⊞-commute kk′~₀~)
     | kk′~₅′ , kk′~₅′~ , kk′~~₅ ← ~~ˣ⁻⊞-assocˡ kk′~~ kk′~₀~
     | kk′~₆′ , kk′~₆′~ , kk′~~₆ ← ~~ˣ⁻⊞-assocˡ kk′~~′ (~~ˣ⁻⊞-commute kk′~₂~)
     | kk′~₇′ , kk′~₇′~ , kk′~~₇ ← ~~ˣ⁻⊞-assocˡ kk′~~′ kk′~₂~
    with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~′
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~₄
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~₅
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~₆
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~₇
      with refl ← ~FVof-unique kk′~~₅ kk′~~₇ FVL FVL′
         | refl ← ~FVof-unique (!∷ᵘ kk′~~₄) (!∷ᵘ kk′~~₆) FVM FVM′                                     = ~~ˣ⁻⊞⁻¹-det kk′~₀~ kk′~₂~
~FVof-unique kk′~~ kk′~~′ (FV`#¹ ~u)                           (FV`#¹ ~u′)                            = ~ᵛ∈ᵘ-uniqueʳ kk′~~ kk′~~′ ~u ~u′
~FVof-unique kk′~~ kk′~~′ (FV`#¹ ~u)                           (FV`#⁰ ~x)                             with () ← ~ᵛ∈ᵘ∧~ᵛ∈ˡ⇒⊥ kk′~~ kk′~~′ ~u ~x
~FVof-unique kk′~~ kk′~~′ (FV`λ⦂-∘ FVL)                        (FV`λ⦂-∘ FVL′)                         = !∷ˡ-inj (~FVof-unique (to-left!∷ˡ kk′~~) (to-left!∷ˡ kk′~~′) FVL FVL′)
~FVof-unique kk′~~ kk′~~′ (FV kk′~₀~ ⊢ FVL `$ FVM)             (FV kk′~₂~ ⊢ FVL′ `$ FVM′)
  with kk′~₄′ , kk′~₄′~ , kk′~~₄ ← ~~ˣ⁻⊞-assocˡ kk′~~ (~~ˣ⁻⊞-commute kk′~₀~)
     | kk′~₅′ , kk′~₅′~ , kk′~~₅ ← ~~ˣ⁻⊞-assocˡ kk′~~ kk′~₀~
     | kk′~₆′ , kk′~₆′~ , kk′~~₆ ← ~~ˣ⁻⊞-assocˡ kk′~~′ (~~ˣ⁻⊞-commute kk′~₂~)
     | kk′~₇′ , kk′~₇′~ , kk′~~₇ ← ~~ˣ⁻⊞-assocˡ kk′~~′ kk′~₂~
    with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~′
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~₄
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~₅
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~₆
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~₇
      with refl ← ~FVof-unique kk′~~₅ kk′~~₇ FVL FVL′
         | refl ← ~FVof-unique kk′~~₄ kk′~~₆ FVM FVM′ = ~~ˣ⁻⊞⁻¹-det kk′~₀~ kk′~₂~
~FVof-unique kk′~~ kk′~~′ (FV`#⁰ ~x)                           (FV`#¹ ~u)                             with () ← ~ᵛ∈ᵘ∧~ᵛ∈ˡ⇒⊥ kk′~~′ kk′~~ ~u ~x
~FVof-unique kk′~~ kk′~~′ (FV`#⁰ ~x)                           (FV`#⁰ ~x′)                            = ~ᵛ∈ˡ-uniqueʳ kk′~~ kk′~~′ ~x ~x′

-- Properties of _~ᴹ_ and ~ᵀ
--
~ᴹ∧∈ᵘ⇒~ᵀ : ψ₁ ⍮ ψ₀ ~ˣ Γ →
           u ⦂[ uMode ] `↑ S ∈ Γ →
           ------------------------
           ∃ (λ P → P ~ᵀ S)
~ᴹ∧∈ᵘ⇒~ᵀ (~S ?∷ˡ ~Γ) (there unusable      u∈) = ~ᴹ∧∈ᵘ⇒~ᵀ ~Γ u∈
~ᴹ∧∈ᵘ⇒~ᵀ (~S !∷ᵘ ~Γ) (here ΓDel)              = -, ~S
~ᴹ∧∈ᵘ⇒~ᵀ (~S !∷ᵘ ~Γ) (there (weakening _) u∈) = ~ᴹ∧∈ᵘ⇒~ᵀ ~Γ u∈

~ᴹ∧∈ˡ⇒~ᵀ : ψ₁ ⍮ ψ₀ ~ˣ Γ →
           u ⦂[ lMode ] S ∈ Γ →
           ---------------------
           ∃ (λ P → P ~ᵀ S)
~ᴹ∧∈ˡ⇒~ᵀ (~S ?∷ˡ ~Γ) (there unusable       x∈) = ~ᴹ∧∈ˡ⇒~ᵀ ~Γ x∈
~ᴹ∧∈ˡ⇒~ᵀ (~S !∷ˡ ~Γ) (here ΓDel)               = -, ~S
~ᴹ∧∈ˡ⇒~ᵀ (~S !∷ˡ ~Γ) (there (weakening ()) x∈)
~ᴹ∧∈ˡ⇒~ᵀ (~S !∷ᵘ ~Γ) (there (weakening _)  x∈) = ~ᴹ∧∈ˡ⇒~ᵀ ~Γ x∈

~ᴹ∧⊢⇒~ᵀ : ψ₁ ⍮ ψ₀ ~ˣ Γ →
          kk′~ ⊢ I ~ᴹ L →
          Γ ⊢[ lMode ] L ⦂ S →
          ---------------------
          ∃ (λ P → P ~ᵀ S)
~ᴹ∧⊢⇒~ᵀ ~Γ (`unit _)                (`unit _)                              = -, `⊤
~ᴹ∧⊢⇒~ᵀ ~Γ (`bang _ ~L)             (Γ∤ ⊢`return`lift ⊢L)
  with refl ← ~ˣ∧∤⇒≡ ~Γ Γ∤
    with _ , ~S ← ~ᴹ∧⊢⇒~ᵀ ~Γ ~L ⊢L                                         = -, `! ~S
~ᴹ∧⊢⇒~ᵀ ~Γ (_ ⊢`let-bang ~L `in ~M) (Γ~ ⊢`let-return ⊢L ⦂ ⊢↓ `in ⊢M)
  with _ , _ , _ , _ , _ , _ , Γ~′ , Γ₀′~ , Γ₀″Del , Γ₁′~ , Γ₁″Del , ψ₀~ , ~Γ₀′ , ~Γ₁′ , kk′~~ ← ~⊞-preserves-~ˣ Γ~ ~Γ
    with _ , `! ~T ← ~ᴹ∧⊢⇒~ᵀ ~Γ₀′ ~L (~⊞-is-all-del∧⊢⇒⊢ˡ Γ₀′~ Γ₀″Del ⊢L)   = ~ᴹ∧⊢⇒~ᵀ (~T !∷ᵘ ~Γ₁′) ~M (~⊞-is-all-del∧⊢⇒⊢ˡ (contraction _ ∷ Γ₁′~) (weakening _ ∷ Γ₁″Del) ⊢M)
~ᴹ∧⊢⇒~ᵀ ~Γ (`#¹ u∈)                 (Γ∤ ⊢`unlift`# u∈′ ⦂ ⊢↑)
  with refl ← ~ˣ∧∤⇒≡ ~Γ Γ∤                                                 = ~ᴹ∧∈ᵘ⇒~ᵀ ~Γ u∈′
~ᴹ∧⊢⇒~ᵀ ~Γ (`λ⦂ ~S ∘ ~L)            (`λ⦂-∘ ⊢L)
  with _ , ~T ← ~ᴹ∧⊢⇒~ᵀ (~S !∷ˡ ~Γ) ~L ⊢L                                  = -, ~S `⊸ ~T
~ᴹ∧⊢⇒~ᵀ ~Γ (_ ⊢ ~L `$ ~M)           (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with _ , _ , _ , _ , _ , _ , Γ~′ , Γ₀′~ , Γ₀″Del , Γ₁′~ , Γ₁″Del , ψ₀~ , ~Γ₀′ , ~Γ₁′ , kk′~~ ← ~⊞-preserves-~ˣ Γ~ ~Γ
    with _ , _ `⊸ ~S ← ~ᴹ∧⊢⇒~ᵀ ~Γ₀′ ~L (~⊞-is-all-del∧⊢⇒⊢ˡ Γ₀′~ Γ₀″Del ⊢L) = -, ~S
~ᴹ∧⊢⇒~ᵀ ~Γ (`#⁰ x∈)                 (`# x∈′)                               = ~ᴹ∧∈ˡ⇒~ᵀ ~Γ x∈′
~ᴹ∧⊢⇒~ᵀ ~Γ (`unlift-`lift _ ~L)     (Γ∤ ⊢`unlift`lift ⊢L ⦂ ⊢↑)
  with refl ← ~ˣ∧∤⇒≡ ~Γ Γ∤                                                 = ~ᴹ∧⊢⇒~ᵀ ~Γ ~L ⊢L

-- Properties of _~ᴹ_ and ~FVof
--
~ᴹ∧⊢⇒~FVof : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
             kk′~ ⊢ I ~ᴹ L →
             Γ ⊢[ lMode ] L ⦂ S →
             ----------------------
             eraseˣ ~Γ ~FVof L
~ᴹ∧⊢⇒~FVof ~Γ (`unit _)                (`unit ΓDel)                                                                = FV`unit (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ (~ˣ∧is-all-del⇒is-all-dis ~Γ ΓDel))
~ᴹ∧⊢⇒~FVof ~Γ (`bang _ ~L)             (Γ∤ ⊢`return`lift ⊢L)
  with kk′~Dis ← ~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ (~ˣ∧∤⇒is-all-dis ~Γ Γ∤)
    with refl ← ~ˣ∧∤⇒≡ ~Γ Γ∤                                                                                       = FV`return (FV`lift (~ᴹ∧⊢⇒~FVof ~Γ ~L ⊢L))
~ᴹ∧⊢⇒~FVof ~Γ (_ ⊢`let-bang ~L `in ~M) (Γ~ ⊢`let-return ⊢L ⦂ ⊢↓ `in ⊢M)
  with _ , _ , _ , _ , _ , _ , Γ~′ , Γ₀′~ , Γ₀″Del , Γ₁′~ , Γ₁″Del , ψ₀~ , ~Γ₀′ , ~Γ₁′ , kk′~~ ← ~⊞-preserves-~ˣ Γ~ ~Γ
    with ⊢L′ ← ~⊞-is-all-del∧⊢⇒⊢ˡ Γ₀′~ Γ₀″Del ⊢L
      with _ , `! ~T ← ~ᴹ∧⊢⇒~ᵀ ~Γ₀′ ~L ⊢L′                                                                         = FV kk′~~ ⊢`let-return ~ᴹ∧⊢⇒~FVof ~Γ₀′ ~L ⊢L′ `in (~ᴹ∧⊢⇒~FVof (~T !∷ᵘ ~Γ₁′) ~M (~⊞-is-all-del∧⊢⇒⊢ˡ (contraction _ ∷ Γ₁′~) (weakening _ ∷ Γ₁″Del) ⊢M))
~ᴹ∧⊢⇒~FVof ~Γ (`#¹ u∈)                 (Γ∤ ⊢`unlift`# u∈′ ⦂ ⊢↑)
  with refl ← ~ˣ∧∤⇒≡ ~Γ Γ∤                                                                                         = FV`unlift (FV`#¹ proj₂ (~ˣ∧∈ᵘ⇒~ᵛ∈ᵘ ~Γ u∈′))
~ᴹ∧⊢⇒~FVof ~Γ (`λ⦂ ~S ∘ ~L)            (`λ⦂-∘ ⊢L)                                                                  = FV`λ⦂-∘ (~ᴹ∧⊢⇒~FVof (~S !∷ˡ ~Γ) ~L ⊢L)
~ᴹ∧⊢⇒~FVof ~Γ (_ ⊢ ~L `$ ~M)           (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with _ , _ , _ , _ , _ , _ , _ , Γ₀′~ , Γ₀″Del , Γ₁′~ , Γ₁″Del , _ , ~Γ₀′ , ~Γ₁′ , kk′~~ ← ~⊞-preserves-~ˣ Γ~ ~Γ = FV kk′~~ ⊢ ~ᴹ∧⊢⇒~FVof ~Γ₀′ ~L (~⊞-is-all-del∧⊢⇒⊢ˡ Γ₀′~ Γ₀″Del ⊢L) `$ ~ᴹ∧⊢⇒~FVof ~Γ₁′ ~M (~⊞-is-all-del∧⊢⇒⊢ˡ Γ₁′~ Γ₁″Del ⊢M)
~ᴹ∧⊢⇒~FVof ~Γ (`#⁰ x∈)                 (`# x∈′)                                                                    = FV`#⁰ proj₂ (~ˣ∧∈ˡ⇒~ᵛ∈ˡ ~Γ x∈′)
~ᴹ∧⊢⇒~FVof ~Γ (`unlift-`lift _ ~L)     (Γ∤ ⊢`unlift`lift ⊢L ⦂ ⊢↑)
  with kk′~Dis ← ~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ (~ˣ∧∤⇒is-all-dis ~Γ Γ∤)
    with refl ← ~ˣ∧∤⇒≡ ~Γ Γ∤                                                                                       = FV`unlift (FV`lift (~ᴹ∧⊢⇒~FVof ~Γ ~L ⊢L))

~ᴹ⇒~FVof : kk′~ ⊢ I ~ᴹ L →
           ----------------
           kk′~ ~FVof L
~ᴹ⇒~FVof (`unit kk′~Dis)              = FV`unit kk′~Dis
~ᴹ⇒~FVof (`bang kk′~Dis ~L)           = FV`return (FV`lift (~ᴹ⇒~FVof ~L))
~ᴹ⇒~FVof (kk′~~ ⊢`let-bang ~L `in ~M) = FV kk′~~ ⊢`let-return ~ᴹ⇒~FVof ~L `in ~ᴹ⇒~FVof ~M
~ᴹ⇒~FVof (`#¹ u∈)                     = FV`unlift (FV`#¹ u∈)
~ᴹ⇒~FVof (`λ⦂ ~S ∘ ~L)                = FV`λ⦂-∘ ~ᴹ⇒~FVof ~L
~ᴹ⇒~FVof (kk′~~ ⊢ ~L `$ ~M)           = FV kk′~~ ⊢ ~ᴹ⇒~FVof ~L `$ ~ᴹ⇒~FVof ~M
~ᴹ⇒~FVof (`#⁰ x∈)                     = FV`#⁰ x∈
~ᴹ⇒~FVof (`unlift-`lift kk′~Dis ~L)   = FV`unlift (FV`lift (~ᴹ⇒~FVof ~L))

~ᴹ∧BP⊢⇒~FVof : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
               kk′~ ~~ˣ⁻ eraseˣ ~Γ ⊞ kk′~₁ →
               kk′~ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
               kk′~₂ ⊢ I ~ᴹ L →
               ψ₁ BP.⍮ ψ₀ ⊢ I ⦂ P →
               ------------------------------
               eraseˣ ~Γ ~FVof L
~ᴹ∧BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ (`unit _)                     (BP.`unit ψ₀Dis)              = FV`unit (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ ψ₀Dis)
~ᴹ∧BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ (`bang _ ~L)                  (ψ₀Dis BP.⊢`bang ⊢I)          = FV`return (FV`lift (~ᴹ∧BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ ~L ⊢I))
~ᴹ∧BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ (kk′~₂~ ⊢`let-bang ~L `in ~M) (ψ₀~ BP.⊢`let-bang ⊢I `in ⊢J)
  with _ , _ , Γ~ , ~Γ₀ , ~Γ₁ , kk′~′~ ← BP~⊞-preserves-~ˣ ψ₀~ ~Γ
    with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~′
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~₂~
       | refl , refl , _ , _ ← ~~ˣ⁻⊞-index kk′~′~
      with _ , kk′~Γ₁′~ , kk′~~₀ ← ~~ˣ⁻⊞-assocˡ kk′~~ kk′~′~
         | _ , kk′~₃′~ , kk′~~₀′ ← ~~ˣ⁻⊞-assocˡ kk′~~′ kk′~₂~
         | _ , kk′~Γ₀′~ , kk′~~₁ ← ~~ˣ⁻⊞-assocˡ kk′~~ (~~ˣ⁻⊞-commute kk′~′~)
         | _ , kk′~₂′~ , kk′~~₁′ ← ~~ˣ⁻⊞-assocˡ kk′~~′ (~~ˣ⁻⊞-commute kk′~₂~)            = FV kk′~′~ ⊢`let-return ~ᴹ∧BP⊢⇒~FVof ~Γ₀ kk′~~₀ kk′~~₀′ ~L ⊢I `in ~ᴹ∧BP⊢⇒~FVof (proj₂ (~ᵀ-total _) !∷ᵘ ~Γ₁) (!∷ᵘ kk′~~₁) (!∷ᵘ kk′~~₁′) ~M ⊢J
~ᴹ∧BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ (`#¹ ~u)                      (ψ₀Dis BP.⊢`#¹ u∈)
  with _ , ~u′ ← ~ˣ∧∈¹⇒~ᵛ∈ᵘ ~Γ ψ₀Dis u∈
    with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~′
      with refl ← ~ᵛ∈ᵘ-uniqueˡ kk′~~′ kk′~~ ~u ~u′ = FV`unlift (FV`#¹ ~u)
~ᴹ∧BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ (`λ⦂ ~S ∘ ~L)                 (BP.`λ⦂-∘ ⊢I)                 = FV`λ⦂-∘ ~ᴹ∧BP⊢⇒~FVof (~S !∷ˡ ~Γ) (to-left!∷ˡ kk′~~) (to-left!∷ˡ kk′~~′) ~L ⊢I
~ᴹ∧BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ (kk′~₂~ ⊢ ~L `$ ~M)           (ψ₀~ BP.⊢ ⊢I `$ ⊢J)
  with _ , _ , Γ~ , ~Γ₀ , ~Γ₁ , kk′~′~ ← BP~⊞-preserves-~ˣ ψ₀~ ~Γ
    with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~′
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~₂~
       | refl , refl , _ , _ ← ~~ˣ⁻⊞-index kk′~′~
      with _ , kk′~Γ₁′~ , kk′~~₀ ← ~~ˣ⁻⊞-assocˡ kk′~~ kk′~′~
         | _ , kk′~₃′~ , kk′~~₀′ ← ~~ˣ⁻⊞-assocˡ kk′~~′ kk′~₂~
         | _ , kk′~Γ₀′~ , kk′~~₁ ← ~~ˣ⁻⊞-assocˡ kk′~~ (~~ˣ⁻⊞-commute kk′~′~)
         | _ , kk′~₂′~ , kk′~~₁′ ← ~~ˣ⁻⊞-assocˡ kk′~~′ (~~ˣ⁻⊞-commute kk′~₂~)            = FV kk′~′~ ⊢ ~ᴹ∧BP⊢⇒~FVof ~Γ₀ kk′~~₀ kk′~~₀′ ~L ⊢I `$ ~ᴹ∧BP⊢⇒~FVof ~Γ₁ kk′~~₁ kk′~~₁′ ~M ⊢J
~ᴹ∧BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ (`#⁰ ~x)                      (BP.`#⁰ x∈)
  with _ , ~x′ ← ~ˣ∧∈⁰⇒~ᵛ∈ˡ ~Γ x∈
    with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~′
      with refl ← ~ᵛ∈ˡ-uniqueˡ kk′~~′ kk′~~ ~x ~x′                                       = FV`#⁰ ~x
~ᴹ∧BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ (`unlift-`lift _ ~L)          ⊢I                            = FV`unlift (FV`lift (~ᴹ∧BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ ~L ⊢I))

-- Soundness and Completeness of _~ᴹ_ Regarding Typings
--
subst⊢~ᴹʳ : ∀ {n m kk′~} →
            (n≡m : n ≡ m) →
            subst (k ⍮_~ˣ⁻) n≡m kk′~ ⊢ I ~ᴹ L →
            ------------------------------------
            kk′~ ⊢ I ~ᴹ L
subst⊢~ᴹʳ refl ~L = ~L

subst⊢~ᴹʳ-depth : ∀ {n m kk′~} →
                  (n≡m : n ≡ m) →
                  (~L : subst (k ⍮_~ˣ⁻) n≡m kk′~ ⊢ I ~ᴹ L) →
                  -------------------------------------------
                  depth~ᴹ ~L ≡ depth~ᴹ (subst⊢~ᴹʳ n≡m ~L)
subst⊢~ᴹʳ-depth refl _ = refl

~ᴹ-soundness-∈ᵘ : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
                  P ~ᵀ S →
                  u′ ~ᵛ u ∈ᵘ eraseˣ ~Γ →
                  u′ BP.⦂ P ∈¹ ψ₁ →
                  -----------------------
                  u ⦂[ uMode ] `↑ S ∈ Γ
~ᴹ-soundness-∈ᵘ (~S′ !∷ᵘ ~Γ) ~S (here kk′~Dis) BP.here
  with refl ← ~ᵀ-det ~S′ ~S                                   = here (~ˣ∧is-all-dis⇒is-all-del ~Γ (~ˣ∧is-all-dis⁰~ˣ⁻⇒is-all-dis ~Γ kk′~Dis))
~ᴹ-soundness-∈ᵘ (~S′ !∷ᵘ ~Γ) ~S (there!∷ᵘ ~u)  (BP.there u′∈) = there (weakening _) (~ᴹ-soundness-∈ᵘ ~Γ ~S ~u u′∈)
~ᴹ-soundness-∈ᵘ (~S′ ?∷ˡ ~Γ) ~S (there?∷ˡ ~u)  u′∈            = there unusable (~ᴹ-soundness-∈ᵘ ~Γ ~S ~u u′∈)

~ᴹ-soundness-∈ˡ : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
                  P ~ᵀ S →
                  x′ ~ᵛ x ∈ˡ eraseˣ ~Γ →
                  x′ BP.⦂ P ∈⁰ ψ₀ →
                  -----------------------
                  x ⦂[ lMode ] S ∈ Γ
~ᴹ-soundness-∈ˡ (~S′ !∷ˡ ~Γ) ~S (here kk′~Dis) (BP.here ψ₀Dis)
  with refl ← ~ᵀ-det ~S′ ~S                                    = here (~ˣ∧is-all-dis⇒is-all-del ~Γ ψ₀Dis)
~ᴹ-soundness-∈ˡ (~S′ !∷ᵘ ~Γ) ~S (there!∷ᵘ ~x)  x′∈             = there (weakening _) (~ᴹ-soundness-∈ˡ ~Γ ~S ~x x′∈)
~ᴹ-soundness-∈ˡ (~S′ ?∷ˡ ~Γ) ~S (there?∷ˡ ~x)  (BP.there x′∈)  = there unusable (~ᴹ-soundness-∈ˡ ~Γ ~S ~x x′∈)

~ᴹ-soundness : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
               P ~ᵀ S →
               eraseˣ ~Γ ⊢ I ~ᴹ L →
               ψ₁ BP.⍮ ψ₀ ⊢ I ⦂ P →
               -----------------------
               Γ ⊢[ lMode ] L ⦂ S
~ᴹ-soundness ~Γ ~S          (kk′~~ ⊢`let-bang ~L `in ~M) (BP._⊢`let-bang_`in_ {Q = Q} ψ₀~ ⊢I ⊢J)
  with _ , ~T ← ~ᵀ-total Q
     | _ , _ , Γ~ , ~Γ₀ , ~Γ₁ , kk′~′~ ← BP~⊞-preserves-~ˣ ψ₀~ ~Γ
    with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
       | refl , refl , _ , _ ← ~~ˣ⁻⊞-index kk′~′~
       | eq₀₀ , eq₀₁ ← BP.length-respects-~⊞ ψ₀~
       | FVL ← ~ᴹ∧BP⊢⇒~FVof ~Γ₀ kk′~′~ kk′~~ ~L ⊢I
       | FVM ← ~ᴹ∧BP⊢⇒~FVof (~T !∷ᵘ ~Γ₁) (!∷ᵘ (~~ˣ⁻⊞-commute kk′~′~)) (!∷ᵘ (~~ˣ⁻⊞-commute kk′~~)) ~M ⊢J
      with refl ← ~FVof-unique kk′~~ (~~ˣ⁻subst⊞ʳ⁻¹ eq₀₀ kk′~′~) (~ᴹ⇒~FVof ~L) (subst~FVofʳ⁻¹ eq₀₀ FVL)
         | refl ← trans
                    (~FVof-unique (!∷ᵘ (~~ˣ⁻⊞-commute kk′~~)) (~~ˣ⁻subst⊞ʳ⁻¹ eq₀₁ (!∷ᵘ (~~ˣ⁻⊞-commute kk′~′~))) (~ᴹ⇒~FVof ~M) (subst~FVofʳ⁻¹ eq₀₁ FVM))
                    (sym (!∷ᵘsubst (eraseˣ ~Γ₁) eq₀₁))                                           = Γ~ ⊢`let-return ~ᴹ-soundness ~Γ₀ (`! ~T) (subst⊢~ᴹʳ eq₀₀ ~L) ⊢I ⦂ ⊢`↓ (λ ()) (⊢`↑ (λ ()) (~ᵀ⇒⊢ ~T)) `in ~ᴹ-soundness (~T !∷ᵘ ~Γ₁) ~S (subst⊢~ᴹʳ eq₀₁ (subst (_⊢ _ ~ᴹ _) (!∷ᵘsubst (eraseˣ ~Γ₁) eq₀₁) ~M)) ⊢J
~ᴹ-soundness ~Γ ~S          (`#¹ ~u)                     (ψ₀Dis BP.⊢`#¹ u∈)                      = eraseˣ-is-all-dis⁰~ˣ⁻⇒∤self ~Γ (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ ψ₀Dis) ⊢`unlift`# ~ᴹ-soundness-∈ᵘ ~Γ ~S ~u u∈ ⦂ ⊢`↑ (λ ()) (~ᵀ⇒⊢ ~S)
~ᴹ-soundness ~Γ (~S′ `⊸ ~T) (`λ⦂ ~S ∘ ~L)                (BP.`λ⦂-∘ ⊢I)
  with refl ← ~ᵀ-det ~S′ ~S                                                                      = `λ⦂-∘ ~ᴹ-soundness (~S !∷ˡ ~Γ) ~T ~L ⊢I
~ᴹ-soundness ~Γ ~S          (kk′~~ ⊢ ~L `$ ~M)           (BP._⊢_`$_ {Q = Q} ψ₀~ ⊢I ⊢J)
  with _ , ~T ← ~ᵀ-total Q
     | _ , _ , Γ~ , ~Γ₀ , ~Γ₁ , kk′~′~ ← BP~⊞-preserves-~ˣ ψ₀~ ~Γ
    with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
       | refl , refl , _ , _ ← ~~ˣ⁻⊞-index kk′~′~
       | eq₀₀ , eq₀₁ ← BP.length-respects-~⊞ ψ₀~
       | FVL ← ~ᴹ∧BP⊢⇒~FVof ~Γ₀ kk′~′~ kk′~~ ~L ⊢I
       | FVM ← ~ᴹ∧BP⊢⇒~FVof ~Γ₁ (~~ˣ⁻⊞-commute kk′~′~) (~~ˣ⁻⊞-commute kk′~~) ~M ⊢J
      with refl ← ~FVof-unique kk′~~ (~~ˣ⁻subst⊞ʳ⁻¹ eq₀₀ kk′~′~) (~ᴹ⇒~FVof ~L) (subst~FVofʳ⁻¹ eq₀₀ FVL)
         | refl ← ~FVof-unique
                    (~~ˣ⁻⊞-commute kk′~~)
                    (~~ˣ⁻subst⊞ʳ⁻¹ eq₀₁ (~~ˣ⁻⊞-commute kk′~′~))
                    (~ᴹ⇒~FVof ~M)
                    (subst~FVofʳ⁻¹ eq₀₁ FVM)                                                     = Γ~ ⊢ ~ᴹ-soundness ~Γ₀ (~T `⊸ ~S) (subst⊢~ᴹʳ eq₀₀ ~L) ⊢I ⦂ ⊢ ~ᵀ⇒⊢ ~T `⊸ ~ᵀ⇒⊢ ~S `$ ~ᴹ-soundness ~Γ₁ ~T (subst⊢~ᴹʳ eq₀₁ ~M) ⊢J
~ᴹ-soundness ~Γ ~S          (`#⁰ ~x)                     (BP.`#⁰ x∈)                             = `# ~ᴹ-soundness-∈ˡ ~Γ ~S ~x x∈
~ᴹ-soundness ~Γ ~S          (`unlift-`lift kk′~Dis ~L)   ⊢I
  with Γ∤ ← eraseˣ-is-all-dis⁰~ˣ⁻⇒∤self ~Γ kk′~Dis                                               = Γ∤ ⊢`unlift`lift ~ᴹ-soundness ~Γ ~S ~L ⊢I ⦂ ⊢`↑ (λ ()) (~ᵀ⇒⊢ ~S)
~ᴹ-soundness ~Γ `⊤          (`unit kk′~Dis)              (BP.`unit ψ₀Dis)                        = `unit (~ˣ∧is-all-dis⇒is-all-del ~Γ ψ₀Dis)
~ᴹ-soundness ~Γ (`! ~S)     (`bang kk′~Dis ~L)           (ψ₀Dis BP.⊢`bang ⊢I)
  with Γ∤ ← eraseˣ-is-all-dis⁰~ˣ⁻⇒∤self ~Γ kk′~Dis                                               = Γ∤ ⊢`return`lift ~ᴹ-soundness ~Γ ~S ~L ⊢I

~ᴹ-completeness-∈ᵘ : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
                     P ~ᵀ S →
                     u′ ~ᵛ u ∈ᵘ eraseˣ ~Γ →
                     u ⦂[ uMode ] `↑ S ∈ Γ →
                     ------------------------
                     u′ BP.⦂ P ∈¹ ψ₁
~ᴹ-completeness-∈ᵘ (~S′ !∷ᵘ ~Γ) ~S (here kk′~Dis) (here ΓDel)
  with refl ← ~ᵀ-inj ~S′ ~S                                                = BP.here
~ᴹ-completeness-∈ᵘ (~S′ !∷ᵘ ~Γ) ~S (there!∷ᵘ ~u)  (there (weakening _) u∈) = BP.there (~ᴹ-completeness-∈ᵘ ~Γ ~S ~u u∈)
~ᴹ-completeness-∈ᵘ (~S′ ?∷ˡ ~Γ) ~S (there?∷ˡ ~u)  (there unusable      u∈) = ~ᴹ-completeness-∈ᵘ ~Γ ~S ~u u∈

~ᴹ-completeness-∈ˡ : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
                     P ~ᵀ S →
                     x′ ~ᵛ x ∈ˡ eraseˣ ~Γ →
                     x ⦂[ lMode ] S ∈ Γ →
                     -----------------------
                     x′ BP.⦂ P ∈⁰ ψ₀
~ᴹ-completeness-∈ˡ (~S′ !∷ˡ ~Γ) ~S (here kk′~Dis) (here ΓDel)
  with refl ← ~ᵀ-inj ~S′ ~S                                                = BP.here (~ˣ∧is-all-del⇒is-all-dis ~Γ ΓDel)
~ᴹ-completeness-∈ˡ (~S′ !∷ᵘ ~Γ) ~S (there!∷ᵘ ~x)  (there (weakening _) x∈) = ~ᴹ-completeness-∈ˡ ~Γ ~S ~x x∈
~ᴹ-completeness-∈ˡ (~S′ ?∷ˡ ~Γ) ~S (there?∷ˡ ~x)  (there unusable      x∈) = BP.there (~ᴹ-completeness-∈ˡ ~Γ ~S ~x x∈)

~ᴹ-completeness : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
                  P ~ᵀ S →
                  eraseˣ ~Γ ⊢ I ~ᴹ L →
                  Γ ⊢[ lMode ] L ⦂ S →
                  -----------------------
                  ψ₁ BP.⍮ ψ₀ ⊢ I ⦂ P
~ᴹ-completeness ~Γ ~S          (kk′~~ ⊢`let-bang ~L `in ~M) (Γ~ ⊢`let-return ⊢L ⦂ ⊢↓ `in ⊢M)
  with _ , _ , _ , _ , _ , _ , Γ~′ , Γ₀′~ , Γ₀″Del , Γ₁′~ , Γ₁″Del , ψ₀~ , ~Γ₀′ , ~Γ₁′ , kk′~~′ ← ~⊞-preserves-~ˣ Γ~ ~Γ
    with eq₀₀ , eq₀₁ ← BP.length-respects-~⊞ ψ₀~
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
       | refl , refl , _ , _ ← ~~ˣ⁻⊞-index kk′~~′
       | ⊢L′ ← ~⊞-is-all-del∧⊢⇒⊢ˡ Γ₀′~ Γ₀″Del ⊢L
      with _ , `! ~T ← ~ᴹ∧⊢⇒~ᵀ ~Γ₀′ ~L ⊢L′
        with FVL ← subst~FVofʳ⁻¹ eq₀₀ (~ᴹ∧⊢⇒~FVof ~Γ₀′ ~L ⊢L′)
           | FVM ← subst~FVofʳ⁻¹ eq₀₁ (~ᴹ∧⊢⇒~FVof (~T !∷ᵘ ~Γ₁′) ~M (~⊞-is-all-del∧⊢⇒⊢ˡ (contraction _ ∷ Γ₁′~) (weakening _ ∷ Γ₁″Del) ⊢M))
          with refl ← ~FVof-unique kk′~~ (~~ˣ⁻subst⊞ʳ⁻¹ eq₀₀ kk′~~′) (~ᴹ⇒~FVof ~L) FVL
             | refl ← trans
                        (~FVof-unique (!∷ᵘ (~~ˣ⁻⊞-commute kk′~~)) (~~ˣ⁻subst⊞ʳ⁻¹ eq₀₁ (~~ˣ⁻⊞-commute (!∷ᵘ kk′~~′))) (~ᴹ⇒~FVof ~M) FVM)
                        (sym (!∷ᵘsubst (eraseˣ ~Γ₁′) eq₀₁))                                                            = ψ₀~ BP.⊢`let-bang ⊢I `in ⊢J
  where
    ⊢I = ~ᴹ-completeness ~Γ₀′ (`! ~T) (subst⊢~ᴹʳ eq₀₀ ~L) (~⊞-is-all-del∧⊢⇒⊢ʳ (~⊞-commute Γ₀′~) Γ₀″Del ⊢L)
    ⊢J = ~ᴹ-completeness
           (~T !∷ᵘ ~Γ₁′)
           ~S
           (subst⊢~ᴹʳ eq₀₁ (subst (_⊢ _ ~ᴹ _) (!∷ᵘsubst (eraseˣ ~Γ₁′) eq₀₁) ~M))
           (~⊞-is-all-del∧⊢⇒⊢ʳ (contraction _ ∷ ~⊞-commute Γ₁′~) (weakening _ ∷ Γ₁″Del) ⊢M)
~ᴹ-completeness ~Γ ~S          (`#¹ ~u)                     (Γ∤ ⊢`unlift`# u∈ ⦂ ⊢↑)
  with ψ₀Dis ← ~ˣ∧∤⇒is-all-dis ~Γ Γ∤
     | refl ← ~ˣ∧∤⇒≡ ~Γ Γ∤                                                                                             = ψ₀Dis BP.⊢`#¹ ~ᴹ-completeness-∈ᵘ ~Γ ~S ~u u∈
~ᴹ-completeness ~Γ (~S′ `⊸ ~T) (`λ⦂ ~S ∘ ~L)                (`λ⦂-∘ ⊢L)
  with refl ← ~ᵀ-inj ~S ~S′                                                                                            = BP.`λ⦂-∘ ~ᴹ-completeness (~S !∷ˡ ~Γ) ~T ~L ⊢L
~ᴹ-completeness ~Γ ~S          (kk′~~ ⊢ ~L `$ ~M)           (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with _ , _ , _ , _ , _ , _ , Γ~′ , Γ₀′~ , Γ₀″Del , Γ₁′~ , Γ₁″Del , ψ₀~ , ~Γ₀′ , ~Γ₁′ , kk′~~′ ← ~⊞-preserves-~ˣ Γ~ ~Γ
    with eq₀₀ , eq₀₁ ← BP.length-respects-~⊞ ψ₀~
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
       | refl , refl , _ , _ ← ~~ˣ⁻⊞-index kk′~~′
       | ⊢L′ ← ~⊞-is-all-del∧⊢⇒⊢ˡ Γ₀′~ Γ₀″Del ⊢L
      with _ , ~T `⊸ _ ← ~ᴹ∧⊢⇒~ᵀ ~Γ₀′ ~L ⊢L′
        with FVL ← subst~FVofʳ⁻¹ eq₀₀ (~ᴹ∧⊢⇒~FVof ~Γ₀′ ~L ⊢L′)
           | FVM ← subst~FVofʳ⁻¹ eq₀₁ (~ᴹ∧⊢⇒~FVof ~Γ₁′ ~M (~⊞-is-all-del∧⊢⇒⊢ˡ Γ₁′~ Γ₁″Del ⊢M))
          with refl ← ~FVof-unique kk′~~ (~~ˣ⁻subst⊞ʳ⁻¹ eq₀₀ kk′~~′) (~ᴹ⇒~FVof ~L) FVL
             | refl ← ~FVof-unique (~~ˣ⁻⊞-commute kk′~~) (~~ˣ⁻subst⊞ʳ⁻¹ eq₀₁ (~~ˣ⁻⊞-commute kk′~~′)) (~ᴹ⇒~FVof ~M) FVM = ψ₀~ BP.⊢ ⊢I `$ ⊢J
  where
    ⊢I = ~ᴹ-completeness ~Γ₀′ (~T `⊸ ~S) (subst⊢~ᴹʳ eq₀₀ ~L) (~⊞-is-all-del∧⊢⇒⊢ʳ (~⊞-commute Γ₀′~) Γ₀″Del ⊢L)
    ⊢J = ~ᴹ-completeness ~Γ₁′ ~T (subst⊢~ᴹʳ eq₀₁ ~M) (~⊞-is-all-del∧⊢⇒⊢ʳ (~⊞-commute Γ₁′~) Γ₁″Del ⊢M)
~ᴹ-completeness ~Γ ~S          (`#⁰ ~x)                     (`# x∈)                                                    = BP.`#⁰ ~ᴹ-completeness-∈ˡ ~Γ ~S ~x x∈
~ᴹ-completeness ~Γ ~S          (`unlift-`lift kk′~Dis ~L)   (Γ∤ ⊢`unlift`lift ⊢L ⦂ ⊢↑)
  with refl ← ~ˣ∧∤⇒≡ ~Γ Γ∤                                                                                             = ~ᴹ-completeness ~Γ ~S ~L ⊢L
~ᴹ-completeness ~Γ `⊤          (`unit kk′~Dis)              (`unit ΓDel)                                               = BP.`unit (~ˣ∧is-all-del⇒is-all-dis ~Γ ΓDel)
~ᴹ-completeness ~Γ (`! ~S)     (`bang kk′~Dis ~L)           (Γ∤ ⊢`return`lift ⊢L)
  with refl ← ~ˣ∧∤⇒≡ ~Γ Γ∤                                                                                             = ~ˣ∧∤⇒is-all-dis ~Γ Γ∤ BP.⊢`bang ~ᴹ-completeness ~Γ ~S ~L ⊢L


-- Properties of _~ᴹ_ Regarding OpSems
--
⟶[≤]-preserves-~ᴹ : kk′~ ⊢ I ~ᴹ L →
                    L ⟶[ uMode ≤] L′ →
                    -------------------
                    kk′~ ⊢ I ~ᴹ L′
⟶[≤]-preserves-~ᴹ (`bang kk′~Dis ~L)           (ξ-`return[≰ ≰uMode ⇒-] L⟶[≤]) with () ← ≰uMode refl
⟶[≤]-preserves-~ᴹ (`bang kk′~Dis ~L)           (ξ-`return≤`lift L⟶[≤])        = `bang kk′~Dis (⟶[≤]-preserves-~ᴹ ~L L⟶[≤])
⟶[≤]-preserves-~ᴹ (kk′~~ ⊢`let-bang ~L `in ~M) ξ-`let-return L⟶[≤] `in?       = kk′~~ ⊢`let-bang (⟶[≤]-preserves-~ᴹ ~L L⟶[≤]) `in ~M
⟶[≤]-preserves-~ᴹ (kk′~~ ⊢`let-bang ~L `in ~M) (ξ-`let-return! WL `in M⟶[≤])  = kk′~~ ⊢`let-bang ~L `in ⟶[≤]-preserves-~ᴹ ~M M⟶[≤]
⟶[≤]-preserves-~ᴹ (`λ⦂ ~S ∘ ~L    )            (ξ-`λ⦂[-]-∘ L⟶[≤])             = `λ⦂ ~S ∘ ⟶[≤]-preserves-~ᴹ ~L L⟶[≤]
⟶[≤]-preserves-~ᴹ (kk′~~ ⊢ ~L `$ ~M)           ξ- L⟶[≤] `$?                   = kk′~~ ⊢ ⟶[≤]-preserves-~ᴹ ~L L⟶[≤] `$ ~M
⟶[≤]-preserves-~ᴹ (kk′~~ ⊢ ~L `$ ~M)           (ξ-! WL `$ M⟶[≤])              = kk′~~ ⊢ ~L `$ ⟶[≤]-preserves-~ᴹ ~M M⟶[≤]
⟶[≤]-preserves-~ᴹ (`#¹ u<)                     (ξ-`unlift[≰ ≰uMode ⇒-] L⟶[≤]) with () ← ≰uMode refl
⟶[≤]-preserves-~ᴹ (`#¹ u<)                     (ξ-`unlift≤ ())
⟶[≤]-preserves-~ᴹ (`unlift-`lift kk′~Dis ~L)   (ξ-`unlift[≰ ≰uMode ⇒-] L⟶[≤]) with () ← ≰uMode refl
⟶[≤]-preserves-~ᴹ (`unlift-`lift kk′~Dis ~L)   (ξ-`unlift≤`lift L⟶[≤])        = `unlift-`lift kk′~Dis (⟶[≤]-preserves-~ᴹ ~L L⟶[≤])
⟶[≤]-preserves-~ᴹ (`unlift-`lift kk′~Dis ~L)   (β-`↑ _ WL)                    = ~L 

[]⊢~ᴹ⁻¹⇒¬Neut⁰ : [] ⊢ I ~ᴹ L →
                 ---------------
                 ¬ (WeakNeut L)
[]⊢~ᴹ⁻¹⇒¬Neut⁰ (`unlift-`lift [] ~L)     (`unlift ())
[]⊢~ᴹ⁻¹⇒¬Neut⁰ ([] ⊢`let-bang ~L `in ~M) (`let-return NL `in _) = []⊢~ᴹ⁻¹⇒¬Neut⁰ ~L NL
[]⊢~ᴹ⁻¹⇒¬Neut⁰ ([] ⊢ ~L `$ ~M)           (NL `$ VM)             = []⊢~ᴹ⁻¹⇒¬Neut⁰ ~L NL

[]⊢~ᴹ⁻¹-respects-Value : [] ⊢ I ~ᴹ L →
                         WeakNorm L →
                         --------------
                         BP.Value I
[]⊢~ᴹ⁻¹-respects-Value ~L            (`neut NL)        with () ← []⊢~ᴹ⁻¹⇒¬Neut⁰ ~L NL
[]⊢~ᴹ⁻¹-respects-Value (`unit b)     `unit             = BP.`unit
[]⊢~ᴹ⁻¹-respects-Value (`bang b ~L)  (`return`lift WL) = BP.`bang _
[]⊢~ᴹ⁻¹-respects-Value (`λ⦂ ~S ∘ ~L) (`λ⦂ˡ S ∘ L)      = BP.`λ⦂ _ ∘ _

~ᴹ-normalize[≤] : (~L : kk′~ ⊢ I ~ᴹ L) →
                  --------------------------------------------------
                  ∃ (λ L′ → L ⟶[ uMode ≤]* L′
                          × DeferredTerm[ uMode ≤] L′
                          × Σ (kk′~ ⊢ I ~ᴹ L′)
                              (λ ~L′ → depth~ᴹ ~L′ ℕ.≤ depth~ᴹ ~L))
~ᴹ-normalize[≤] (`unit kk′~Dis)                           = -, ε
                                                          , `unit
                                                          , `unit kk′~Dis
                                                          , z≤n
~ᴹ-normalize[≤] (`bang kk′~Dis ~L)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L = -, ξ-of-⟶[ uMode ≤]* `return`lift ξ-`return≤`lift ⟶*L′[≤]
                                                          , `return≤ (`lift WL′)
                                                          , `bang kk′~Dis ~L′
                                                          , s≤s L′≤
~ᴹ-normalize[≤] (kk′~~ ⊢`let-bang ~L `in ~M)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
     | _ , ⟶*M′[≤] , WM′ , ~M′ , M′≤ ← ~ᴹ-normalize[≤] ~M = -, ξ-of-⟶[ uMode ≤]* (`let-return_`in _) ξ-`let-return_`in? ⟶*L′[≤]
                                                              ◅◅ ξ-of-⟶[ uMode ≤]* (`let-return _ `in_) (ξ-`let-return! WL′ `in_) ⟶*M′[≤]
                                                          , `let-return WL′ `in WM′
                                                          , kk′~~ ⊢`let-bang ~L′ `in ~M′
                                                          , s≤s (ℕ.⊔-mono-≤ L′≤ M′≤)
~ᴹ-normalize[≤] (`#¹ u<)                                  = -, ε
                                                          , `unlift≤ (`neut (`# _))
                                                          , `#¹ u<
                                                          , z≤n
~ᴹ-normalize[≤] (`λ⦂ ~S ∘ ~L)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L = -, ξ-of-⟶[ uMode ≤]* (`λ⦂ˡ _ ∘_) ξ-`λ⦂[-]-∘_ ⟶*L′[≤]
                                                          , `λ⦂ˡ _ ∘ WL′
                                                          , `λ⦂ ~S ∘ ~L′
                                                          , s≤s L′≤
~ᴹ-normalize[≤] (kk′~~ ⊢ ~L `$ ~M)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
     | _ , ⟶*M′[≤] , WM′ , ~M′ , M′≤ ← ~ᴹ-normalize[≤] ~M = -, ξ-of-⟶[ uMode ≤]* (_`$ _) ξ-_`$? ⟶*L′[≤]
                                                              ◅◅ ξ-of-⟶[ uMode ≤]* (_ `$_) (ξ-! WL′ `$_) ⟶*M′[≤]
                                                          , WL′ `$ WM′
                                                          , kk′~~ ⊢ ~L′ `$ ~M′
                                                          , s≤s (ℕ.⊔-mono-≤ L′≤ M′≤)
~ᴹ-normalize[≤] (`#⁰ x<)                                  = -, ε
                                                          , `# _
                                                          , `#⁰ x<
                                                          , z≤n
~ᴹ-normalize[≤] (`unlift-`lift kk′~Dis ~L)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L = -, ξ-of-⟶[ uMode ≤]* `unlift`lift ξ-`unlift≤`lift ⟶*L′[≤]
                                                              ◅◅ β-`↑ refl WL′ ◅ ε
                                                          , WL′
                                                          , ~L′
                                                          , ℕ.≤-trans L′≤ (ℕ.n≤1+n _)

Value~ᴹ-normalize-helper : (~L : kk′~ ⊢ I ~ᴹ L) →
                           BP.Value I →
                           Acc ℕ._<_ (depth~ᴹ ~L) →
                           --------------------------------------------------
                           ∃ (λ L′ → L ⟶* L′ × WeakNorm L′ × kk′~ ⊢ I ~ᴹ L′)
Value~ᴹ-normalize-helper (`unit kk′~Dis)            VI rec                      = -, ε , `unit , `unit kk′~Dis
Value~ᴹ-normalize-helper (`bang kk′~Dis ~L)         VI (acc r)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , _ ← ~ᴹ-normalize[≤] ~L                         = -, ξ-of-↝*-⟶* _⟶[ _ ≤]_ `return`lift ξ-`return`lift ⟶*L′[≤]
                                                                                , `return`lift WL′
                                                                                , `bang kk′~Dis ~L′
Value~ᴹ-normalize-helper (`λ⦂ ~S ∘ ~L)              VI rec                      = -, ε , `λ⦂ˡ _ ∘ _ , `λ⦂ ~S ∘ ~L
Value~ᴹ-normalize-helper (`unlift-`lift kk′~Dis ~L) VI (acc r)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
    with _ , ⟶*L″ , VL″ , ~L″ ← Value~ᴹ-normalize-helper ~L′ VI (r _ (s≤s L′≤)) = -, ξ-of-↝*-⟶* _⟶[ uMode ≤]_ `unlift`lift ξ-`unlift`lift ⟶*L′[≤]
                                                                                    ◅◅ β-`↑ WL′ ◅ ⟶*L″
                                                                                , VL″
                                                                                , ~L″

Value~ᴹ-normalize : kk′~ ⊢ I ~ᴹ L →
                    BP.Value I →
                    --------------------------------------------------
                    ∃ (λ L′ → L ⟶* L′ × WeakNorm L′ × kk′~ ⊢ I ~ᴹ L′)
Value~ᴹ-normalize ~L VI = Value~ᴹ-normalize-helper ~L VI (ℕ.<-wellFounded _)

`bang-~ᴹ-inv-helper : (~L : kk′~ ⊢ BP.`bang I ~ᴹ L) →
                     Acc ℕ._<_ (depth~ᴹ ~L) →
                     ------------------------------------
                     ∃ (λ L′ → L ⟶* `return`lift L′
                             × DeferredTerm[ uMode ≤] L′
                             × kk′~ ⊢ I ~ᴹ L′)
`bang-~ᴹ-inv-helper (`bang kk′~Dis ~L)         rec
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L                    = -, ξ-of-↝*-⟶* _⟶[ _ ≤]_ `return`lift ξ-`return`lift ⟶*L′[≤]
                                                                             , WL′
                                                                             , ~L′
`bang-~ᴹ-inv-helper (`unlift-`lift kk′~Dis ~L) (acc r)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
    with _ , ⟶*`bangL″ , WL″ , ~L″ ← `bang-~ᴹ-inv-helper ~L′ (r _ (s≤s L′≤)) = -, ξ-of-↝*-⟶* _⟶[ uMode ≤]_ `unlift`lift ξ-`unlift`lift ⟶*L′[≤]
                                                                                 ◅◅ β-`↑ WL′ ◅ ⟶*`bangL″
                                                                             , WL″
                                                                             , ~L″

`bang-~ᴹ-inv : kk′~ ⊢ BP.`bang I ~ᴹ L →
              ------------------------------------
              ∃ (λ L′ → L ⟶* `return`lift L′
                      × DeferredTerm[ uMode ≤] L′
                      × kk′~ ⊢ I ~ᴹ L′)
`bang-~ᴹ-inv ~L = `bang-~ᴹ-inv-helper ~L (ℕ.<-wellFounded _)

`λ⦂-∙-~ᴹ-inv-helper : (~L : kk′~ ⊢ BP.`λ⦂ P ∘ I ~ᴹ L) →
                      Acc ℕ._<_ (depth~ᴹ ~L) →
                      ----------------------------------
                      ∃₂ (λ S′ L′ → L ⟶* `λ⦂ˡ S′ ∘ L′
                                  × !∷ˡ kk′~ ⊢ I ~ᴹ L′
                                  × P ~ᵀ S′)
`λ⦂-∙-~ᴹ-inv-helper (`λ⦂ ~S ∘ ~L)              rec                                 = -, -, ε
                                                                                   , ~L
                                                                                   , ~S
`λ⦂-∙-~ᴹ-inv-helper (`unlift-`lift kk′~Dis ~L) (acc r)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
    with _ , _ , ⟶*`λ⦂ˡS″∘L″ , ~L″ , ~S″ ← `λ⦂-∙-~ᴹ-inv-helper ~L′ (r _ (s≤s L′≤)) = -, -, ξ-of-↝*-⟶* _⟶[ uMode ≤]_ `unlift`lift ξ-`unlift`lift ⟶*L′[≤]
                                                                                       ◅◅ β-`↑ WL′ ◅ ⟶*`λ⦂ˡS″∘L″
                                                                                   , ~L″
                                                                                   , ~S″

`λ⦂-∙-~ᴹ-inv : kk′~ ⊢ BP.`λ⦂ P ∘ I ~ᴹ L →
               ---------------------------------
               ∃₂ (λ S′ L′ → L ⟶* `λ⦂ˡ S′ ∘ L′
                           × !∷ˡ kk′~ ⊢ I ~ᴹ L′
                           × P ~ᵀ S′)
`λ⦂-∙-~ᴹ-inv ~L = `λ⦂-∙-~ᴹ-inv-helper ~L (ℕ.<-wellFounded _)

~ᵛ⇒¬is-all-dis : BP.x ~ᵛ x ∈ˡ kk′~ →
                 ------------------------
                 ¬ (kk′~ is-all-dis⁰~ˣ⁻)
~ᵛ⇒¬is-all-dis (there!∷ᵘ ~x) (!∷ᵘ kk′~) = ~ᵛ⇒¬is-all-dis ~x kk′~
~ᵛ⇒¬is-all-dis (there?∷ˡ ~x) (?∷ˡ kk′~) = ~ᵛ⇒¬is-all-dis ~x kk′~

~ᵛ∧is-all-dis⇒< : (kk′~ : k ⍮ k′ ~ˣ⁻) →
                  {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                  BP.x ~ᵛ x ∈ˡ kk′~ ++ˣ⁻ k″k‴~ →
                  k″k‴~ is-all-dis⁰~ˣ⁻ →
                  -------------------------------
                  BP.x ℕ.< k′
~ᵛ∧is-all-dis⇒< []         ~x            k″k‴~Dis with () ← ~ᵛ⇒¬is-all-dis ~x k″k‴~Dis
~ᵛ∧is-all-dis⇒< (!∷ᵘ kk′~) (there!∷ᵘ ~x) k″k‴~Dis = ~ᵛ∧is-all-dis⇒< kk′~ ~x k″k‴~Dis
~ᵛ∧is-all-dis⇒< (?∷ˡ kk′~) (there?∷ˡ ~x) k″k‴~Dis = s≤s (~ᵛ∧is-all-dis⇒< kk′~ ~x k″k‴~Dis)
~ᵛ∧is-all-dis⇒< (!∷ˡ kk′~) (here _)      k″k‴~Dis = s≤s z≤n

~ᴹ∧≥⇒wk[↑⁰]≡ : ∀ k₀ →
               (kk′~ : k ⍮ k′ ~ˣ⁻) →
               {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
               kk′~ ++ˣ⁻ k″k‴~ ⊢ I ~ᴹ L →
               k″k‴~ is-all-dis⁰~ˣ⁻ →
               x ℕ.≥ k′ →
               ---------------------------
               BP.wk[ k₀ ↑⁰ x ] I ≡ I
~ᴹ∧≥⇒wk[↑⁰]≡ _ kk′~ (`unit kk′~k″k‴~Dis)              k″k‴~Dis x≥                      = refl
~ᴹ∧≥⇒wk[↑⁰]≡ _ kk′~ (`bang kk′~k″k‴~Dis ~M)           k″k‴~Dis x≥                      = refl
~ᴹ∧≥⇒wk[↑⁰]≡ _ kk′~ (kk′~k″k‴~~ ⊢`let-bang ~M `in ~N) k″k‴~Dis x≥
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~k″k‴~~
    with kk′~₀~ , kk′~₁~ , _ , _ , refl , refl , kk′~~ , k″k‴~~ ← ~~ˣ⁻⊞-preserves-++ kk′~ kk′~k″k‴~~
      with k″k‴~₀Dis , k″k‴~₁Dis ← ~~ˣ⁻⊞-preserves-is-all-dis⁰~ˣ⁻ k″k‴~Dis k″k‴~~      = cong₂ BP.`let-bang_`in_ (~ᴹ∧≥⇒wk[↑⁰]≡ _ kk′~₀~ ~M k″k‴~₀Dis x≥) (~ᴹ∧≥⇒wk[↑⁰]≡ _ (!∷ᵘ kk′~₁~) ~N k″k‴~₁Dis x≥)
~ᴹ∧≥⇒wk[↑⁰]≡ _ kk′~ (`#¹ ~u)                          k″k‴~Dis x≥                      = refl
~ᴹ∧≥⇒wk[↑⁰]≡ _ kk′~ (`λ⦂ ~S ∘ ~M)                     k″k‴~Dis x≥                      = cong (BP.`λ⦂ _ ∘_) (~ᴹ∧≥⇒wk[↑⁰]≡ _ (!∷ˡ kk′~) ~M k″k‴~Dis (s≤s x≥))
~ᴹ∧≥⇒wk[↑⁰]≡ _ kk′~ (kk′~k″k‴~~ ⊢ ~M `$ ~N)           k″k‴~Dis x≥
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~k″k‴~~
    with kk′~₀~ , kk′~₁~ , _ , _ , refl , refl , kk′~~ , k″k‴~~ ← ~~ˣ⁻⊞-preserves-++ kk′~ kk′~k″k‴~~
      with k″k‴~₀Dis , k″k‴~₁Dis ← ~~ˣ⁻⊞-preserves-is-all-dis⁰~ˣ⁻ k″k‴~Dis k″k‴~~      = cong₂ BP._`$_ (~ᴹ∧≥⇒wk[↑⁰]≡ _ kk′~₀~ ~M k″k‴~₀Dis x≥) (~ᴹ∧≥⇒wk[↑⁰]≡ _ kk′~₁~ ~N k″k‴~₁Dis x≥)
~ᴹ∧≥⇒wk[↑⁰]≡ _ kk′~ (`#⁰ ~y)                          k″k‴~Dis x≥
  rewrite dec-no (_ ℕ.≤? _) (ℕ.<⇒≱ (ℕ.<-transˡ (~ᵛ∧is-all-dis⇒< kk′~ ~y k″k‴~Dis) x≥)) = refl
~ᴹ∧≥⇒wk[↑⁰]≡ _ kk′~ (`unlift-`lift kk′~k″k‴~Dis ~M)   k″k‴~Dis x≥                      = ~ᴹ∧≥⇒wk[↑⁰]≡ _ kk′~ ~M k″k‴~Dis x≥

subst-~ᴹwk[↑-] : x ≡ x′ →
                 ∀ M →
                 kk′~ ⊢ I ~ᴹ wk[ y ↑ x ] M →
                 ----------------------------
                 kk′~ ⊢ I ~ᴹ wk[ y ↑ x′ ] M
subst-~ᴹwk[↑-] {kk′~ = kk′~} {I} {y} eq M = subst (λ x → kk′~ ⊢ I ~ᴹ wk[ y ↑ x ] M) eq

wk[↑¹]~ᴹwk[↑] : (kk′~ : k ⍮ k′ ~ˣ⁻) (k₀0~ : k₀ ⍮ 0 ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                 kk′~ ++ˣ⁻ k″k‴~ ⊢ I ~ᴹ L →
                 ----------------------------------------------------------------------------------------
                 kk′~ ++ˣ⁻ k₀0~ ++ˣ⁻ k″k‴~ ⊢ BP.wk[ k₀ ↑¹ k ] I ~ᴹ wk[ lengthˣ⁻ k₀0~ ↑ lengthˣ⁻ kk′~ ] L
wk[↑¹]~ᴹwk[↑] {_} {_}  kk′~ k₀0~ (`unlift-`lift kk′~k″k‴~Dis ~L)                     = `unlift-`lift kk′~k₀0~k″k‴~Dis (wk[↑¹]~ᴹwk[↑] kk′~ k₀0~ ~L)
  where
    kk′~k₀0~k″k‴~Dis = is-all-dis⁰~ˣ⁻-++⁺
                         (is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~k″k‴~Dis)
                         (is-all-dis⁰~ˣ⁻-++⁺
                           (k⍮0~ˣ⁻-is-all-dis⁰~ˣ⁻ k₀0~)
                           (is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~k″k‴~Dis))
wk[↑¹]~ᴹwk[↑] {_} {_}  kk′~ k₀0~ (`bang kk′~k″k‴~Dis ~L)                             = `bang kk′~k₀0~k″k‴~Dis (wk[↑¹]~ᴹwk[↑] kk′~ k₀0~ ~L)
  where
    kk′~k₀0~k″k‴~Dis = is-all-dis⁰~ˣ⁻-++⁺
                         (is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~k″k‴~Dis)
                         (is-all-dis⁰~ˣ⁻-++⁺
                           (k⍮0~ˣ⁻-is-all-dis⁰~ˣ⁻ k₀0~)
                           (is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~k″k‴~Dis))
wk[↑¹]~ᴹwk[↑]          kk′~ k₀0~ (`unit kk′~k″k‴~Dis)                                = `unit kk′~k₀0~k″k‴~Dis
  where
    kk′~k₀0~k″k‴~Dis = is-all-dis⁰~ˣ⁻-++⁺
                         (is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~k″k‴~Dis)
                         (is-all-dis⁰~ˣ⁻-++⁺
                           (k⍮0~ˣ⁻-is-all-dis⁰~ˣ⁻ k₀0~)
                           (is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~k″k‴~Dis))
wk[↑¹]~ᴹwk[↑]          kk′~ k₀0~ (_⊢`let-bang_`in_ {L = L} {M = M} kk′~k″k‴~~ ~L ~M)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~k″k‴~~
    with kk′~₀ , kk′~₁ , _ , _ , refl , refl , kk′~~ , k″k‴~~ ← ~~ˣ⁻⊞-preserves-++ kk′~ kk′~k″k‴~~
      with eq₀ , eq₁ ← lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~                                  = kk′~k₀0~k″k‴~~ ⊢`let-bang subst-~ᴹwk[↑-] eq₀ L (wk[↑¹]~ᴹwk[↑] kk′~₀ k₀0~ ~L) `in subst-~ᴹwk[↑-] (cong suc eq₁) M (wk[↑¹]~ᴹwk[↑] (!∷ᵘ kk′~₁) k₀0~ ~M)
  where
    kk′~k₀0~k″k‴~~ = ~~ˣ⁻⊞-++ kk′~~ (~~ˣ⁻⊞-++ (is-all-dis⁰~ˣ⁻-self~~ˣ⁻⊞ (k⍮0~ˣ⁻-is-all-dis⁰~ˣ⁻ k₀0~)) k″k‴~~)
wk[↑¹]~ᴹwk[↑]          kk′~ k₀0~ (`#¹ ~u)                                             = `#¹ lemma kk′~ k₀0~ ~u
  where
    lemma : (kk′~ : k ⍮ k′ ~ˣ⁻) (k₀0~ : k₀ ⍮ 0 ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
            BP.u ~ᵛ u ∈ᵘ kk′~ ++ˣ⁻ k″k‴~ →
            wkidx[ k₀ ↑ k ] BP.u ~ᵛ wkidx[ lengthˣ⁻ k₀0~ ↑ lengthˣ⁻ kk′~ ] u ∈ᵘ kk′~ ++ˣ⁻ k₀0~ ++ˣ⁻ k″k‴~
    lemma {k}     {_} {_}      {_} {_} {BPu}     {u}     kk′~       []         ~u
      rewrite wkidx[0↑]≡ k BPu
            | wkidx[0↑]≡ (lengthˣ⁻ kk′~) u                                                         = ~u
    lemma                                                []         (!∷ᵘ k₀0~) ~u                  = there!∷ᵘ (lemma [] k₀0~ ~u)
    lemma                                                (!∷ᵘ kk′~) (!∷ᵘ k₀0~) (here kk′~k″k‴~Dis) = here (is-all-dis⁰~ˣ⁻-++⁺ (is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~k″k‴~Dis) (!∷ᵘ (is-all-dis⁰~ˣ⁻-++⁺ (k⍮0~ˣ⁻-is-all-dis⁰~ˣ⁻ k₀0~) (is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~k″k‴~Dis))))
    lemma {suc k} {_} {suc k₀} {_} {_} {suc BPu} {suc u} (!∷ᵘ kk′~) (!∷ᵘ k₀0~) (there!∷ᵘ ~u)
      rewrite wkidx[↑suc]suc≡sucwkidx[↑] (suc k₀) k BPu
            | wkidx[↑suc]suc≡sucwkidx[↑] (suc (lengthˣ⁻ k₀0~)) (lengthˣ⁻ kk′~) u                   = there!∷ᵘ (lemma kk′~ (!∷ᵘ k₀0~) ~u)
    lemma {k}     {_} {suc k₀} {_} {_} {BPu}     {suc u} (?∷ˡ kk′~) (!∷ᵘ k₀0~) (there?∷ˡ ~u)
      rewrite wkidx[↑suc]suc≡sucwkidx[↑] (suc k₀) k BPu
            | wkidx[↑suc]suc≡sucwkidx[↑] (suc (lengthˣ⁻ k₀0~)) (lengthˣ⁻ kk′~) u                   = there?∷ˡ (lemma kk′~ (!∷ᵘ k₀0~) ~u)
wk[↑¹]~ᴹwk[↑] {k} {k′} kk′~ k₀0~ (`λ⦂ ~S ∘ ~L)
  with ~L′ ← wk[↑¹]~ᴹwk[↑] (!∷ˡ kk′~) k₀0~ ~L
    rewrite ℕ.+-suc k k′                                                              = `λ⦂ ~S ∘ ~L′
wk[↑¹]~ᴹwk[↑]          kk′~ k₀0~ (_⊢_`$_ {L = L} {M = M} kk′~k″k‴~~ ~L ~M)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~k″k‴~~
    with kk′~₀ , kk′~₁ , _ , _ , refl , refl , kk′~~ , k″k‴~~ ← ~~ˣ⁻⊞-preserves-++ kk′~ kk′~k″k‴~~
      with eq₀ , eq₁ ← lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~                                  = kk′~k₀0~k″k‴~~ ⊢ subst-~ᴹwk[↑-] eq₀ L (wk[↑¹]~ᴹwk[↑] kk′~₀ k₀0~ ~L) `$ subst-~ᴹwk[↑-] eq₁ M (wk[↑¹]~ᴹwk[↑] kk′~₁ k₀0~ ~M)
  where
    kk′~k₀0~k″k‴~~ = ~~ˣ⁻⊞-++ kk′~~ (~~ˣ⁻⊞-++ (is-all-dis⁰~ˣ⁻-self~~ˣ⁻⊞ (k⍮0~ˣ⁻-is-all-dis⁰~ˣ⁻ k₀0~)) k″k‴~~)
wk[↑¹]~ᴹwk[↑]          kk′~ k₀0~ (`#⁰ ~x)                                             = `#⁰ lemma kk′~ k₀0~ ~x
  where
    lemma : (kk′~ : k ⍮ k′ ~ˣ⁻) (k₀0~ : k₀ ⍮ 0 ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
            BP.x ~ᵛ x ∈ˡ kk′~ ++ˣ⁻ k″k‴~ →
            BP.x ~ᵛ wkidx[ lengthˣ⁻ k₀0~ ↑ lengthˣ⁻ kk′~ ] x ∈ˡ kk′~ ++ˣ⁻ k₀0~ ++ˣ⁻ k″k‴~
    lemma {_} {_} {_} {_} {_} {_} {x}     kk′~       []         ~x
      rewrite wkidx[0↑]≡ (lengthˣ⁻ kk′~) x                                          = ~x
    lemma                                 []         (!∷ᵘ k₀0~) ~x                  = there!∷ᵘ (lemma [] k₀0~ ~x)
    lemma {_} {_} {_} {_} {_} {_} {suc x} (!∷ᵘ kk′~) (!∷ᵘ k₀0~) (there!∷ᵘ ~x)
      rewrite wkidx[↑suc]suc≡sucwkidx[↑] (suc (lengthˣ⁻ k₀0~)) (lengthˣ⁻ kk′~) x    = there!∷ᵘ (lemma kk′~ (!∷ᵘ k₀0~) ~x)
    lemma {_} {_} {_} {_} {_} {_} {suc x} (?∷ˡ kk′~) (!∷ᵘ k₀0~) (there?∷ˡ ~x)
      rewrite wkidx[↑suc]suc≡sucwkidx[↑] (suc (lengthˣ⁻ k₀0~)) (lengthˣ⁻ kk′~) x    = there?∷ˡ (lemma kk′~ (!∷ᵘ k₀0~) ~x)
    lemma                                 (!∷ˡ kk′~) (!∷ᵘ k₀0~) (here kk′~k″k‴~Dis) = here (is-all-dis⁰~ˣ⁻-++⁺ (is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~k″k‴~Dis) (!∷ᵘ (is-all-dis⁰~ˣ⁻-++⁺ (k⍮0~ˣ⁻-is-all-dis⁰~ˣ⁻ k₀0~) (is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~k″k‴~Dis))))

wk[↑⁰]~ᴹwk[↑] : (kk′~ : k ⍮ k′ ~ˣ⁻) {0k₀~ : 0 ⍮ k₀ ~ˣ⁻} {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                 0k₀~ is-all-dis⁰~ˣ⁻ →
                 kk′~ ++ˣ⁻ k″k‴~ ⊢ I ~ᴹ L →
                 -----------------------------------------------------------------------------------------
                 kk′~ ++ˣ⁻ 0k₀~ ++ˣ⁻ k″k‴~ ⊢ BP.wk[ k₀ ↑⁰ k′ ] I ~ᴹ wk[ lengthˣ⁻ 0k₀~ ↑ lengthˣ⁻ kk′~ ] L
wk[↑⁰]~ᴹwk[↑] {_} {_}  {k₀} kk′~ 0k₀~Dis (`bang kk′~k″k‴~Dis ~L)                                          = `bang kk′~0k₀~k″k‴~Dis (subst (_ ⊢_~ᴹ _) (~ᴹ∧≥⇒wk[↑⁰]≡ k₀ kk′~ ~L (is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~k″k‴~Dis) ℕ.≤-refl) (wk[↑⁰]~ᴹwk[↑] kk′~ 0k₀~Dis ~L))
  where
    kk′~0k₀~k″k‴~Dis = is-all-dis⁰~ˣ⁻-++⁺
                         (is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~k″k‴~Dis)
                         (is-all-dis⁰~ˣ⁻-++⁺ 0k₀~Dis (is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~k″k‴~Dis))
wk[↑⁰]~ᴹwk[↑]               kk′~ 0k₀~Dis (`unlift-`lift kk′~k″k‴~Dis ~L)                                  = `unlift-`lift kk′~0k₀~k″k‴~Dis (wk[↑⁰]~ᴹwk[↑] kk′~ 0k₀~Dis ~L)
  where
    kk′~0k₀~k″k‴~Dis = is-all-dis⁰~ˣ⁻-++⁺
                         (is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~k″k‴~Dis)
                         (is-all-dis⁰~ˣ⁻-++⁺ 0k₀~Dis (is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~k″k‴~Dis))
wk[↑⁰]~ᴹwk[↑]               kk′~ 0k₀~Dis (`unit kk′~k″k‴~Dis)                                             = `unit kk′~0k₀~k″k‴~Dis
  where
    kk′~0k₀~k″k‴~Dis = is-all-dis⁰~ˣ⁻-++⁺
                         (is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~k″k‴~Dis)
                         (is-all-dis⁰~ˣ⁻-++⁺ 0k₀~Dis (is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~k″k‴~Dis))
wk[↑⁰]~ᴹwk[↑]               kk′~ 0k₀~Dis (kk′~k″k‴~~ ⊢`let-bang ~L `in ~M)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~k″k‴~~
    with kk′~₀~ , kk′~₁~ , _ , _ , refl , refl , kk′~~ , k″k‴~~ ← ~~ˣ⁻⊞-preserves-++ kk′~ kk′~k″k‴~~
      with eq₀ , eq₁ ← lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~                                                      = kk′~0k₀~k″k‴~~ ⊢`let-bang subst-~ᴹwk[↑-] eq₀ _ (wk[↑⁰]~ᴹwk[↑] kk′~₀~ 0k₀~Dis ~L) `in subst-~ᴹwk[↑-] (cong suc eq₁) _ (wk[↑⁰]~ᴹwk[↑] (!∷ᵘ kk′~₁~) 0k₀~Dis ~M)
  where
    kk′~0k₀~k″k‴~~ = ~~ˣ⁻⊞-++ kk′~~ (~~ˣ⁻⊞-++ (is-all-dis⁰~ˣ⁻-self~~ˣ⁻⊞ 0k₀~Dis) k″k‴~~)
wk[↑⁰]~ᴹwk[↑]               kk′~ 0k₀~Dis (`#¹ ~u)                                                         = `#¹ lemma kk′~ 0k₀~Dis ~u
  where
    lemma : (kk′~ : k ⍮ k′ ~ˣ⁻) {0k₀~ : 0 ⍮ k₀ ~ˣ⁻} {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
            0k₀~ is-all-dis⁰~ˣ⁻ →
            BP.u ~ᵛ u ∈ᵘ kk′~ ++ˣ⁻ k″k‴~ →
            BP.u ~ᵛ wkidx[ lengthˣ⁻ 0k₀~ ↑ lengthˣ⁻ kk′~ ] u ∈ᵘ kk′~ ++ˣ⁻ 0k₀~ ++ˣ⁻ k″k‴~
    lemma {_} {_} {_} {_} {_} {_} {u}     kk′~              []            ~u
      rewrite wkidx[0↑]≡ (lengthˣ⁻ kk′~) u                                                    = ~u
    lemma                                 []                (?∷ˡ 0k₀~Dis) ~u                  = there?∷ˡ (lemma [] 0k₀~Dis ~u)
    lemma {_} {_} {_} {_} {_} {_} {suc u} (!∷ᵘ kk′~) {0k₀~} (?∷ˡ 0k₀~Dis) (there!∷ᵘ ~u)
      rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~) u                    = there!∷ᵘ (lemma kk′~ (?∷ˡ 0k₀~Dis) ~u)
    lemma {_} {_} {_} {_} {_} {_} {suc u} (?∷ˡ kk′~) {0k₀~} (?∷ˡ 0k₀~Dis) (there?∷ˡ ~u)
      rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~) u                    = there?∷ˡ (lemma kk′~ (?∷ˡ 0k₀~Dis) ~u)
    lemma                                 (!∷ᵘ kk′~)        (?∷ˡ 0k₀~Dis) (here kk′~k″k‴~Dis) = here ((is-all-dis⁰~ˣ⁻-++⁺ (is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~k″k‴~Dis) (?∷ˡ (is-all-dis⁰~ˣ⁻-++⁺ 0k₀~Dis (is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~k″k‴~Dis)))))
    
wk[↑⁰]~ᴹwk[↑] {k} {k′}      kk′~ 0k₀~Dis (`λ⦂ ~S ∘ ~L)
  with ~L′ ← wk[↑⁰]~ᴹwk[↑] (!∷ˡ kk′~) 0k₀~Dis ~L
    rewrite ℕ.+-suc k k′                                                                                  = `λ⦂ ~S ∘ ~L′
wk[↑⁰]~ᴹwk[↑]               kk′~ 0k₀~Dis (kk′~k″k‴~~ ⊢ ~L `$ ~M)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~k″k‴~~
    with kk′~₀~ , kk′~₁~ , _ , _ , refl , refl , kk′~~ , k″k‴~~ ← ~~ˣ⁻⊞-preserves-++ kk′~ kk′~k″k‴~~
      with eq₀ , eq₁ ← lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~                                                      = kk′~0k₀~k″k‴~~ ⊢ subst-~ᴹwk[↑-] eq₀ _ (wk[↑⁰]~ᴹwk[↑] kk′~₀~ 0k₀~Dis ~L) `$ subst-~ᴹwk[↑-] eq₁ _ (wk[↑⁰]~ᴹwk[↑] kk′~₁~ 0k₀~Dis ~M)
  where
    kk′~0k₀~k″k‴~~ = ~~ˣ⁻⊞-++ kk′~~ (~~ˣ⁻⊞-++ (is-all-dis⁰~ˣ⁻-self~~ˣ⁻⊞ 0k₀~Dis) k″k‴~~)
wk[↑⁰]~ᴹwk[↑]               kk′~ 0k₀~Dis (`#⁰ ~x)                                                         = `#⁰ lemma kk′~ 0k₀~Dis ~x
  where
    lemma : (kk′~ : k ⍮ k′ ~ˣ⁻) {0k₀~ : 0 ⍮ k₀ ~ˣ⁻} {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
            0k₀~ is-all-dis⁰~ˣ⁻ →
            BP.x ~ᵛ x ∈ˡ kk′~ ++ˣ⁻ k″k‴~ →
            wkidx[ k₀ ↑ k′ ] BP.x ~ᵛ wkidx[ lengthˣ⁻ 0k₀~ ↑ lengthˣ⁻ kk′~ ] x ∈ˡ kk′~ ++ˣ⁻ 0k₀~ ++ˣ⁻ k″k‴~
    lemma {_} {k′}     {_}  {_} {_} {BPx}     {x}     kk′~              []            ~x
      rewrite wkidx[0↑]≡ k′ BPx
            | wkidx[0↑]≡ (lengthˣ⁻ kk′~) x                                                                = ~x
    lemma                                             []                (?∷ˡ 0k₀~Dis) ~x                  = there?∷ˡ (lemma [] 0k₀~Dis ~x)
    lemma {_} {_}      {_}  {_} {_} {_}       {suc x} (!∷ᵘ kk′~) {0k₀~} (?∷ˡ 0k₀~Dis) (there!∷ᵘ ~x)
      rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~) x                                = there!∷ᵘ (lemma kk′~ (?∷ˡ 0k₀~Dis) ~x)
    lemma {_} {suc k′} {k₀} {_} {_} {suc BPx} {suc x} (?∷ˡ kk′~) {0k₀~} (?∷ˡ 0k₀~Dis) (there?∷ˡ ~x)
      rewrite wkidx[↑suc]suc≡sucwkidx[↑] k₀ k′ BPx
            | wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~) x                                = there?∷ˡ (lemma kk′~ (?∷ˡ 0k₀~Dis) ~x)
    lemma                                             (!∷ˡ kk′~)        (?∷ˡ 0k₀~Dis) (here kk′~k″k‴~Dis) = here ((is-all-dis⁰~ˣ⁻-++⁺ (is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~k″k‴~Dis) (?∷ˡ (is-all-dis⁰~ˣ⁻-++⁺ 0k₀~Dis (is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~k″k‴~Dis)))))

subst-~ᴹ[/-] : x ≡ x′ →
               ∀ M →
               kk′~ ⊢ I ~ᴹ [ L /[ m₀ ] x ] M →
               --------------------------------
               kk′~ ⊢ I ~ᴹ [ L /[ m₀ ] x′ ] M
subst-~ᴹ[/-] {kk′~ = kk′~} {I} {L} {m₀} eq M = subst (λ x → kk′~ ⊢ I ~ᴹ [ L /[ m₀ ] x ] M) eq

∈ˡ!∷ᵘ⇒≢ : ∀ (kk′~ : k ⍮ k′ ~ˣ⁻) →
          BP.x ~ᵛ x ∈ˡ kk′~ ++ˣ⁻ !∷ᵘ kk′~′ →
          -----------------------------------
          x ≢ lengthˣ⁻ kk′~
∈ˡ!∷ᵘ⇒≢ []         (there!∷ᵘ ~x) ()
∈ˡ!∷ᵘ⇒≢ (!∷ᵘ kk′~) (there!∷ᵘ ~x) refl = ∈ˡ!∷ᵘ⇒≢ kk′~ ~x refl
∈ˡ!∷ᵘ⇒≢ (?∷ˡ kk′~) (there?∷ˡ ~x) refl = ∈ˡ!∷ᵘ⇒≢ kk′~ ~x refl
∈ˡ!∷ᵘ⇒≢ (!∷ˡ kk′~) (here _)      ()

∈ᵘ?∷ˡ⇒≢ : ∀ (kk′~ : k ⍮ k′ ~ˣ⁻) →
          BP.u ~ᵛ u ∈ᵘ kk′~ ++ˣ⁻ ?∷ˡ kk′~′ →
          -----------------------------------
          u ≢ lengthˣ⁻ kk′~
∈ᵘ?∷ˡ⇒≢ []         (there?∷ˡ ~x) ()
∈ᵘ?∷ˡ⇒≢ (!∷ᵘ kk′~) (here _)      ()
∈ᵘ?∷ˡ⇒≢ (!∷ᵘ kk′~) (there!∷ᵘ ~x) refl = ∈ᵘ?∷ˡ⇒≢ kk′~ ~x refl
∈ᵘ?∷ˡ⇒≢ (?∷ˡ kk′~) (there?∷ˡ ~x) refl = ∈ᵘ?∷ˡ⇒≢ kk′~ ~x refl

∈ˡ?∷ˡ⇒≢ : ∀ (kk′~ : k ⍮ k′ ~ˣ⁻) →
          BP.x ~ᵛ x ∈ˡ kk′~ ++ˣ⁻ ?∷ˡ kk′~′ →
          -----------------------------------
          BP.x ≢ k′
∈ˡ?∷ˡ⇒≢ []         (there?∷ˡ ~x) ()
∈ˡ?∷ˡ⇒≢ (!∷ᵘ kk′~) (there!∷ᵘ ~x) refl = ∈ˡ?∷ˡ⇒≢ kk′~ ~x refl
∈ˡ?∷ˡ⇒≢ (?∷ˡ kk′~) (there?∷ˡ ~x) refl = ∈ˡ?∷ˡ⇒≢ kk′~ ~x refl
∈ˡ?∷ˡ⇒≢ (!∷ˡ kk′~) (here _)      ()

∈ᵘ∧<⇒< : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
         BP.u ~ᵛ u ∈ᵘ kk′~ ++ˣ⁻ k″k‴~ →
         BP.u ℕ.< k →
         --------------------------------------------
         u ℕ.< lengthˣ⁻ kk′~
∈ᵘ∧<⇒< (!∷ᵘ kk′~) (here _)      BPu<       = s≤s z≤n
∈ᵘ∧<⇒< (!∷ᵘ kk′~) (there!∷ᵘ ~u) (s≤s BPu<) = s≤s (∈ᵘ∧<⇒< kk′~ ~u BPu<)
∈ᵘ∧<⇒< (?∷ˡ kk′~) (there?∷ˡ ~u) (s≤s BPu<) = s≤s (∈ᵘ∧<⇒< kk′~ ~u (s≤s BPu<))

∈ᵘ∧>⇒> : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
         BP.u ~ᵛ u ∈ᵘ kk′~ ++ˣ⁻ k″k‴~ →
         BP.u ℕ.> k →
         --------------------------------------------
         u ℕ.> lengthˣ⁻ kk′~
∈ᵘ∧>⇒> []         (there!∷ᵘ ~u) BPu>       = s≤s z≤n
∈ᵘ∧>⇒> []         (there?∷ˡ ~u) BPu>       = s≤s z≤n
∈ᵘ∧>⇒> (!∷ᵘ kk′~) (there!∷ᵘ ~u) (s≤s BPu>) = s≤s (∈ᵘ∧>⇒> kk′~ ~u BPu>)
∈ᵘ∧>⇒> (?∷ˡ kk′~) (there?∷ˡ ~u) (s≤s BPu>) = s≤s (∈ᵘ∧>⇒> kk′~ ~u (s≤s BPu>))

∈ᵘ!∷ᵘ∧≡⇒≡ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
            BP.u ~ᵛ u ∈ᵘ kk′~ ++ˣ⁻ !∷ᵘ k″k‴~ →
            BP.u ≡ k →
            --------------------------------------------
            u ≡ lengthˣ⁻ kk′~
∈ᵘ!∷ᵘ∧≡⇒≡ []         (here _)      refl = refl
∈ᵘ!∷ᵘ∧≡⇒≡ (!∷ᵘ kk′~) (there!∷ᵘ ~u) refl = cong suc (∈ᵘ!∷ᵘ∧≡⇒≡ kk′~ ~u refl)
∈ᵘ!∷ᵘ∧≡⇒≡ (?∷ˡ kk′~) (there?∷ˡ ~u) refl = cong suc (∈ᵘ!∷ᵘ∧≡⇒≡ kk′~ ~u refl)

∈ˡ∧<⇒< : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
         BP.x ~ᵛ x ∈ˡ kk′~ ++ˣ⁻ k″k‴~ →
         BP.x ℕ.< k′ →
         --------------------------------------------
         x ℕ.< lengthˣ⁻ kk′~
∈ˡ∧<⇒< (!∷ᵘ kk′~) (there!∷ᵘ ~x) (s≤s BPx<) = s≤s (∈ˡ∧<⇒< kk′~ ~x (s≤s BPx<))
∈ˡ∧<⇒< (?∷ˡ kk′~) (there?∷ˡ ~x) (s≤s BPx<) = s≤s (∈ˡ∧<⇒< kk′~ ~x BPx<)
∈ˡ∧<⇒< (!∷ˡ kk′~) (here _)      BPx<       = s≤s z≤n

∈ˡ∧>⇒> : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
         BP.x ~ᵛ x ∈ˡ kk′~ ++ˣ⁻ k″k‴~ →
         BP.x ℕ.> k′ →
         --------------------------------------------
         x ℕ.> lengthˣ⁻ kk′~
∈ˡ∧>⇒> []         (there!∷ᵘ ~x) BPx>       = s≤s z≤n
∈ˡ∧>⇒> []         (there?∷ˡ ~x) BPx>       = s≤s z≤n
∈ˡ∧>⇒> (!∷ᵘ kk′~) (there!∷ᵘ ~x) (s≤s BPx>) = s≤s (∈ˡ∧>⇒> kk′~ ~x (s≤s BPx>))
∈ˡ∧>⇒> (?∷ˡ kk′~) (there?∷ˡ ~x) (s≤s BPx>) = s≤s (∈ˡ∧>⇒> kk′~ ~x BPx>)
∈ˡ∧>⇒> (!∷ˡ kk′~) (here _)      ()

~ᵛ∈ᵘ!∷ᵘ∧<⇒~ᵛ∈ᵘ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                 BP.u ~ᵛ u ∈ᵘ kk′~ ++ˣ⁻ !∷ᵘ k″k‴~ →
                 BP.u ℕ.< k →
                 --------------------------------------------
                 BP.u ~ᵛ u ∈ᵘ kk′~ ++ˣ⁻ k″k‴~
~ᵛ∈ᵘ!∷ᵘ∧<⇒~ᵛ∈ᵘ (!∷ᵘ kk′~) (here kk′~!∷ᵘk″k‴~Dis) BPu<
  with !∷ᵘ k″k‴~Dis ← is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~!∷ᵘk″k‴~Dis = here (is-all-dis⁰~ˣ⁻-++⁺ (is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~!∷ᵘk″k‴~Dis) k″k‴~Dis)
~ᵛ∈ᵘ!∷ᵘ∧<⇒~ᵛ∈ᵘ (!∷ᵘ kk′~) (there!∷ᵘ ~u)          (s≤s BPu<)    = there!∷ᵘ (~ᵛ∈ᵘ!∷ᵘ∧<⇒~ᵛ∈ᵘ kk′~ ~u BPu<)
~ᵛ∈ᵘ!∷ᵘ∧<⇒~ᵛ∈ᵘ (?∷ˡ kk′~) (there?∷ˡ ~u)          (s≤s BPu<)    = there?∷ˡ (~ᵛ∈ᵘ!∷ᵘ∧<⇒~ᵛ∈ᵘ kk′~ ~u (s≤s BPu<))

~ᵛ∈ᵘ!∷ᵘ∧>⇒pred~ᵛpred∈ᵘ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                         BP.u ~ᵛ u ∈ᵘ kk′~ ++ˣ⁻ !∷ᵘ k″k‴~ →
                         BP.u ℕ.> k →
                         --------------------------------------------
                         ℕ.pred BP.u ~ᵛ ℕ.pred u ∈ᵘ kk′~ ++ˣ⁻ k″k‴~
~ᵛ∈ᵘ!∷ᵘ∧>⇒pred~ᵛpred∈ᵘ []         (there!∷ᵘ ~u) BPu>       = ~u
~ᵛ∈ᵘ!∷ᵘ∧>⇒pred~ᵛpred∈ᵘ (!∷ᵘ kk′~) (there!∷ᵘ ~u) (s≤s BPu>) = subst₂ (_~ᵛ_∈ᵘ _) (ℕ.suc-pred _ ⦃ ℕ.>-nonZero (ℕ.m<n⇒0<n BPu>) ⦄) (ℕ.suc-pred _ ⦃ ℕ.>-nonZero (ℕ.m<n⇒0<n (∈ᵘ∧>⇒> kk′~ ~u BPu>)) ⦄) (there!∷ᵘ (~ᵛ∈ᵘ!∷ᵘ∧>⇒pred~ᵛpred∈ᵘ kk′~ ~u BPu>))
~ᵛ∈ᵘ!∷ᵘ∧>⇒pred~ᵛpred∈ᵘ (?∷ˡ kk′~) (there?∷ˡ ~u) BPu>       = subst (_ ~ᵛ_∈ᵘ _) (ℕ.suc-pred _ ⦃ ℕ.>-nonZero (ℕ.m<n⇒0<n (∈ᵘ∧>⇒> kk′~ ~u BPu>)) ⦄) (there?∷ˡ (~ᵛ∈ᵘ!∷ᵘ∧>⇒pred~ᵛpred∈ᵘ kk′~ ~u BPu>))

~ᵛ∈ᵘ!∷ᵘ∧≡⇒is-all-dis⁰~ˣ⁻ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                           BP.u ~ᵛ u ∈ᵘ kk′~ ++ˣ⁻ !∷ᵘ k″k‴~ →
                           BP.u ≡ k →
                           --------------------------------------------
                           kk′~ is-all-dis⁰~ˣ⁻ × k″k‴~ is-all-dis⁰~ˣ⁻
~ᵛ∈ᵘ!∷ᵘ∧≡⇒is-all-dis⁰~ˣ⁻ []         (here k″k‴~Dis) refl          = [] , k″k‴~Dis
~ᵛ∈ᵘ!∷ᵘ∧≡⇒is-all-dis⁰~ˣ⁻ (!∷ᵘ kk′~) (there!∷ᵘ ~u)   refl
  with kk′~Dis , k″k‴~Dis ← ~ᵛ∈ᵘ!∷ᵘ∧≡⇒is-all-dis⁰~ˣ⁻ kk′~ ~u refl = !∷ᵘ kk′~Dis , k″k‴~Dis
~ᵛ∈ᵘ!∷ᵘ∧≡⇒is-all-dis⁰~ˣ⁻ (?∷ˡ kk′~) (there?∷ˡ ~u)   refl
  with kk′~Dis , k″k‴~Dis ← ~ᵛ∈ᵘ!∷ᵘ∧≡⇒is-all-dis⁰~ˣ⁻ kk′~ ~u refl = ?∷ˡ kk′~Dis , k″k‴~Dis

~ᵛ∈ˡ!∷ᵘ∧<⇒~ᵛ∈ˡ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                 BP.x ~ᵛ x ∈ˡ kk′~ ++ˣ⁻ !∷ᵘ k″k‴~ →
                 x ℕ.< lengthˣ⁻ kk′~ →
                 --------------------------------------------
                 BP.x ~ᵛ x ∈ˡ kk′~ ++ˣ⁻ k″k‴~
~ᵛ∈ˡ!∷ᵘ∧<⇒~ᵛ∈ˡ (!∷ᵘ kk′~) (there!∷ᵘ ~x)          (s≤s x<)      = there!∷ᵘ (~ᵛ∈ˡ!∷ᵘ∧<⇒~ᵛ∈ˡ kk′~ ~x x<)
~ᵛ∈ˡ!∷ᵘ∧<⇒~ᵛ∈ˡ (?∷ˡ kk′~) (there?∷ˡ ~x)          (s≤s x<)      = there?∷ˡ (~ᵛ∈ˡ!∷ᵘ∧<⇒~ᵛ∈ˡ kk′~ ~x x<)
~ᵛ∈ˡ!∷ᵘ∧<⇒~ᵛ∈ˡ (!∷ˡ kk′~) (here kk′~!∷ᵘk″k‴~Dis) x<
  with !∷ᵘ k″k‴~Dis ← is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~!∷ᵘk″k‴~Dis = here (is-all-dis⁰~ˣ⁻-++⁺ (is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~!∷ᵘk″k‴~Dis) k″k‴~Dis)

~ᵛ∈ˡ!∷ᵘ∧>⇒~ᵛpred∈ˡ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                     BP.x ~ᵛ x ∈ˡ kk′~ ++ˣ⁻ !∷ᵘ k″k‴~ →
                     x ℕ.> lengthˣ⁻ kk′~ →
                     --------------------------------------------
                     BP.x ~ᵛ ℕ.pred x ∈ˡ kk′~ ++ˣ⁻ k″k‴~
~ᵛ∈ˡ!∷ᵘ∧>⇒~ᵛpred∈ˡ []         (there!∷ᵘ ~x) x>       = ~x
~ᵛ∈ˡ!∷ᵘ∧>⇒~ᵛpred∈ˡ (!∷ᵘ kk′~) (there!∷ᵘ ~x) (s≤s x>) = subst (_ ~ᵛ_∈ˡ _) (ℕ.suc-pred _ ⦃ ℕ.>-nonZero (ℕ.m<n⇒0<n x>) ⦄) (there!∷ᵘ (~ᵛ∈ˡ!∷ᵘ∧>⇒~ᵛpred∈ˡ kk′~ ~x x>))
~ᵛ∈ˡ!∷ᵘ∧>⇒~ᵛpred∈ˡ (?∷ˡ kk′~) (there?∷ˡ ~x) (s≤s x>) = subst (_ ~ᵛ_∈ˡ _) (ℕ.suc-pred _ ⦃ ℕ.>-nonZero (ℕ.m<n⇒0<n x>) ⦄) (there?∷ˡ (~ᵛ∈ˡ!∷ᵘ∧>⇒~ᵛpred∈ˡ kk′~ ~x x>))

~ᵛ∈ˡ?∷ˡ∧>⇒pred~ᵛpred∈ˡ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                         BP.x ~ᵛ x ∈ˡ kk′~ ++ˣ⁻ ?∷ˡ k″k‴~ →
                         BP.x ℕ.> k′ →
                         --------------------------------------------
                         ℕ.pred BP.x ~ᵛ ℕ.pred x ∈ˡ kk′~ ++ˣ⁻ k″k‴~
~ᵛ∈ˡ?∷ˡ∧>⇒pred~ᵛpred∈ˡ []         (there?∷ˡ ~x) BPx>       = ~x
~ᵛ∈ˡ?∷ˡ∧>⇒pred~ᵛpred∈ˡ (!∷ᵘ kk′~) (there!∷ᵘ ~x) BPx>       = subst (_ ~ᵛ_∈ˡ _) (ℕ.suc-pred _ ⦃ ℕ.>-nonZero (ℕ.m<n⇒0<n (∈ˡ∧>⇒> kk′~ ~x BPx>)) ⦄) (there!∷ᵘ (~ᵛ∈ˡ?∷ˡ∧>⇒pred~ᵛpred∈ˡ kk′~ ~x BPx>))
~ᵛ∈ˡ?∷ˡ∧>⇒pred~ᵛpred∈ˡ (?∷ˡ kk′~) (there?∷ˡ ~x) (s≤s BPx>) = subst₂ (_~ᵛ_∈ˡ _) (ℕ.suc-pred _ ⦃ ℕ.>-nonZero (ℕ.m<n⇒0<n BPx>) ⦄) (ℕ.suc-pred _ ⦃ ℕ.>-nonZero (ℕ.m<n⇒0<n (∈ˡ∧>⇒> kk′~ ~x BPx>)) ⦄) (there?∷ˡ (~ᵛ∈ˡ?∷ˡ∧>⇒pred~ᵛpred∈ˡ kk′~ ~x BPx>))

~ᵛ∈ˡ?∷ˡ∧<⇒~ᵛ∈ˡ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                 BP.x ~ᵛ x ∈ˡ kk′~ ++ˣ⁻ ?∷ˡ k″k‴~ →
                 BP.x ℕ.< k′ →
                 --------------------------------------------
                 BP.x ~ᵛ x ∈ˡ kk′~ ++ˣ⁻ k″k‴~
~ᵛ∈ˡ?∷ˡ∧<⇒~ᵛ∈ˡ (!∷ᵘ kk′~) (there!∷ᵘ ~x)          BPx<          = there!∷ᵘ (~ᵛ∈ˡ?∷ˡ∧<⇒~ᵛ∈ˡ kk′~ ~x BPx<)
~ᵛ∈ˡ?∷ˡ∧<⇒~ᵛ∈ˡ (?∷ˡ kk′~) (there?∷ˡ ~x)          (s≤s BPx<)    = there?∷ˡ (~ᵛ∈ˡ?∷ˡ∧<⇒~ᵛ∈ˡ kk′~ ~x BPx<)
~ᵛ∈ˡ?∷ˡ∧<⇒~ᵛ∈ˡ (!∷ˡ kk′~) (here kk′~?∷ˡk″k‴~Dis) BPx<
  with ?∷ˡ k″k‴~Dis ← is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~?∷ˡk″k‴~Dis = here (is-all-dis⁰~ˣ⁻-++⁺ (is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~?∷ˡk″k‴~Dis) k″k‴~Dis)

~ᵛ∈ᵘ?∷ˡ∧<⇒~ᵛ∈ᵘ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                 BP.u ~ᵛ u ∈ᵘ kk′~ ++ˣ⁻ ?∷ˡ k″k‴~ →
                 u ℕ.< lengthˣ⁻ kk′~ →
                 --------------------------------------------
                 BP.u ~ᵛ u ∈ᵘ kk′~ ++ˣ⁻ k″k‴~
~ᵛ∈ᵘ?∷ˡ∧<⇒~ᵛ∈ᵘ (!∷ᵘ kk′~) (there!∷ᵘ ~u)          (s≤s u<)      = there!∷ᵘ (~ᵛ∈ᵘ?∷ˡ∧<⇒~ᵛ∈ᵘ kk′~ ~u u<)
~ᵛ∈ᵘ?∷ˡ∧<⇒~ᵛ∈ᵘ (!∷ᵘ kk′~) (here kk′~?∷ˡk″k‴~Dis) u<
  with ?∷ˡ k″k‴~Dis ← is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~?∷ˡk″k‴~Dis = here (is-all-dis⁰~ˣ⁻-++⁺ (is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~?∷ˡk″k‴~Dis) k″k‴~Dis)
~ᵛ∈ᵘ?∷ˡ∧<⇒~ᵛ∈ᵘ (?∷ˡ kk′~) (there?∷ˡ ~u)          (s≤s u<)      = there?∷ˡ (~ᵛ∈ᵘ?∷ˡ∧<⇒~ᵛ∈ᵘ kk′~ ~u u<)

~ᵛ∈ᵘ?∷ˡ∧>⇒~ᵛpred∈ᵘ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                     BP.u ~ᵛ u ∈ᵘ kk′~ ++ˣ⁻ ?∷ˡ k″k‴~ →
                     u ℕ.> lengthˣ⁻ kk′~ →
                     --------------------------------------------
                     BP.u ~ᵛ ℕ.pred u ∈ᵘ kk′~ ++ˣ⁻ k″k‴~
~ᵛ∈ᵘ?∷ˡ∧>⇒~ᵛpred∈ᵘ []         (there?∷ˡ ~u) u>       = ~u
~ᵛ∈ᵘ?∷ˡ∧>⇒~ᵛpred∈ᵘ (!∷ᵘ kk′~) (there!∷ᵘ ~u) (s≤s u>) = subst (_ ~ᵛ_∈ᵘ _) (ℕ.suc-pred _ ⦃ ℕ.>-nonZero (ℕ.m<n⇒0<n u>) ⦄) (there!∷ᵘ (~ᵛ∈ᵘ?∷ˡ∧>⇒~ᵛpred∈ᵘ kk′~ ~u u>))
~ᵛ∈ᵘ?∷ˡ∧>⇒~ᵛpred∈ᵘ (?∷ˡ kk′~) (there?∷ˡ ~u) (s≤s u>) = subst (_ ~ᵛ_∈ᵘ _) (ℕ.suc-pred _ ⦃ ℕ.>-nonZero (ℕ.m<n⇒0<n u>) ⦄) (there?∷ˡ (~ᵛ∈ᵘ?∷ˡ∧>⇒~ᵛpred∈ᵘ kk′~ ~u u>))

¬~ᵛ∈ᵘ!∷ˡ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
           --------------------------------------------
           ¬ (BP.u ~ᵛ u ∈ᵘ kk′~ ++ˣ⁻ !∷ˡ k″k‴~)
¬~ᵛ∈ᵘ!∷ˡ []         ()
¬~ᵛ∈ᵘ!∷ˡ (!∷ᵘ kk′~) (here kk′~!∷ˡk″k‴~Dis) with () ← is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~!∷ˡk″k‴~Dis
¬~ᵛ∈ᵘ!∷ˡ (!∷ᵘ kk′~) (there!∷ᵘ ~u)          = ¬~ᵛ∈ᵘ!∷ˡ kk′~ ~u
¬~ᵛ∈ᵘ!∷ˡ (?∷ˡ kk′~) (there?∷ˡ ~u)          = ¬~ᵛ∈ᵘ!∷ˡ kk′~ ~u

~ᵛ∈ˡ!∷ˡ⇒≡∧is-all-dis⁰~ˣ⁻ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                           BP.x ~ᵛ x ∈ˡ kk′~ ++ˣ⁻ !∷ˡ k″k‴~ →
                           ---------------------------------------------------------------------------
                           BP.x ≡ k′ × x ≡ lengthˣ⁻ kk′~ × kk′~ is-all-dis⁰~ˣ⁻ × k″k‴~ is-all-dis⁰~ˣ⁻
~ᵛ∈ˡ!∷ˡ⇒≡∧is-all-dis⁰~ˣ⁻ []         (here k″k‴~Dis)                        = refl , refl , [] , k″k‴~Dis
~ᵛ∈ˡ!∷ˡ⇒≡∧is-all-dis⁰~ˣ⁻ (!∷ᵘ kk′~) (there!∷ᵘ ~u)
  with refl , refl , kk′~Dis , k″k‴~Dis ← ~ᵛ∈ˡ!∷ˡ⇒≡∧is-all-dis⁰~ˣ⁻ kk′~ ~u = refl , refl , !∷ᵘ kk′~Dis , k″k‴~Dis
~ᵛ∈ˡ!∷ˡ⇒≡∧is-all-dis⁰~ˣ⁻ (?∷ˡ kk′~) (there?∷ˡ ~u)
  with refl , refl , kk′~Dis , k″k‴~Dis ← ~ᵛ∈ˡ!∷ˡ⇒≡∧is-all-dis⁰~ˣ⁻ kk′~ ~u = refl , refl , ?∷ˡ kk′~Dis , k″k‴~Dis
~ᵛ∈ˡ!∷ˡ⇒≡∧is-all-dis⁰~ˣ⁻ (!∷ˡ kk′~) (here kk′~!∷ˡk″k‴~Dis)                 with () ← is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~!∷ˡk″k‴~Dis

~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧∈ᵘ⇒∈ᵘ : {kk′~ kk′~₀ kk′~₁ : k ⍮ k′ ~ˣ⁻} →
                             kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                             kk′~₀ is-all-dis⁰~ˣ⁻ →
                             BP.u ~ᵛ u ∈ᵘ kk′~₁ →
                             ----------------------------------
                             BP.u ~ᵛ u ∈ᵘ kk′~
~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧∈ᵘ⇒∈ᵘ (!∷ᵘ kk′~~) (!∷ᵘ kk′~₀Dis) (here kk′~₁Dis) = here (~~ˣ⁻⊞⁻¹-preserves-is-all-dis⁰~ˣ⁻ kk′~₀Dis kk′~₁Dis kk′~~)
~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧∈ᵘ⇒∈ᵘ (!∷ᵘ kk′~~) (!∷ᵘ kk′~₀Dis) (there!∷ᵘ ~u)   = there!∷ᵘ (~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧∈ᵘ⇒∈ᵘ kk′~~ kk′~₀Dis ~u)
~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧∈ᵘ⇒∈ᵘ (?∷ˡ kk′~~) (?∷ˡ kk′~₀Dis) (there?∷ˡ ~u)   = there?∷ˡ (~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧∈ᵘ⇒∈ᵘ kk′~~ kk′~₀Dis ~u)

~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧∈ˡ⇒∈ˡ : {kk′~ kk′~₀ kk′~₁ : k ⍮ k′ ~ˣ⁻} →
                             kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                             kk′~₀ is-all-dis⁰~ˣ⁻ →
                             BP.x ~ᵛ x ∈ˡ kk′~₁ →
                             ----------------------------------
                             BP.x ~ᵛ x ∈ˡ kk′~
~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧∈ˡ⇒∈ˡ (!∷ᵘ         kk′~~) (!∷ᵘ kk′~₀Dis) (there!∷ᵘ ~u)   = there!∷ᵘ (~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧∈ˡ⇒∈ˡ kk′~~ kk′~₀Dis ~u)
~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧∈ˡ⇒∈ˡ (?∷ˡ         kk′~~) (?∷ˡ kk′~₀Dis) (there?∷ˡ ~u)   = there?∷ˡ (~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧∈ˡ⇒∈ˡ kk′~~ kk′~₀Dis ~u)
~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧∈ˡ⇒∈ˡ (to-right!∷ˡ kk′~~) (?∷ˡ kk′~₀Dis) (here kk′~₁Dis) = here (~~ˣ⁻⊞⁻¹-preserves-is-all-dis⁰~ˣ⁻ kk′~₀Dis kk′~₁Dis kk′~~)

~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒~ᴹ : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                             kk′~₀ is-all-dis⁰~ˣ⁻ →
                             kk′~₁ ⊢ I ~ᴹ L →
                             --------------------------
                             kk′~ ⊢ I ~ᴹ L
~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒~ᴹ kk′~~ kk′~₀Dis (`unit kk′~₁Dis)                                   = `unit (~~ˣ⁻⊞⁻¹-preserves-is-all-dis⁰~ˣ⁻ kk′~₀Dis kk′~₁Dis kk′~~)
~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒~ᴹ kk′~~ kk′~₀Dis (`bang kk′~₁Dis ~L)                                = `bang (~~ˣ⁻⊞⁻¹-preserves-is-all-dis⁰~ˣ⁻ kk′~₀Dis kk′~₁Dis kk′~~) (~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒~ᴹ kk′~~ kk′~₀Dis ~L)
~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒~ᴹ kk′~~ kk′~₀Dis (kk′~₁~ ⊢`let-bang ~L `in ~M)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
     | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~₁~
    with _ , _ , kk′~₂′~ , kk′~₃′~ , kk′~~′ ← ~~ˣ⁻⊞-contraction-assocʳ kk′~~ kk′~₁~ kk′~₀Dis = kk′~~′ ⊢`let-bang ~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒~ᴹ kk′~₂′~ kk′~₀Dis ~L `in ~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒~ᴹ (!∷ᵘ kk′~₃′~) (!∷ᵘ kk′~₀Dis) ~M
~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒~ᴹ kk′~~ kk′~₀Dis (`#¹ ~u)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~                                         = `#¹ ~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧∈ᵘ⇒∈ᵘ kk′~~ kk′~₀Dis ~u
~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒~ᴹ kk′~~ kk′~₀Dis (`λ⦂ ~S ∘ ~L)                                      = `λ⦂ ~S ∘ ~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒~ᴹ (to-right!∷ˡ kk′~~) (?∷ˡ kk′~₀Dis) ~L
~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒~ᴹ kk′~~ kk′~₀Dis (kk′~₁~ ⊢ ~L `$ ~M)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
     | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~₁~
    with _ , _ , kk′~₂′~ , kk′~₃′~ , kk′~~′ ← ~~ˣ⁻⊞-contraction-assocʳ kk′~~ kk′~₁~ kk′~₀Dis = kk′~~′ ⊢ ~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒~ᴹ kk′~₂′~ kk′~₀Dis ~L `$ ~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒~ᴹ kk′~₃′~ kk′~₀Dis ~M
~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒~ᴹ kk′~~ kk′~₀Dis (`#⁰ ~x)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~                                         = `#⁰ ~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧∈ˡ⇒∈ˡ kk′~~ kk′~₀Dis ~x
~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒~ᴹ kk′~~ kk′~₀Dis (`unlift-`lift kk′~₁Dis ~L)                        = `unlift-`lift (~~ˣ⁻⊞⁻¹-preserves-is-all-dis⁰~ˣ⁻ kk′~₀Dis kk′~₁Dis kk′~~) (~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒~ᴹ kk′~~ kk′~₀Dis ~L)

!∷ᵘ[/¹]~ᴹ[/]ᵘ : {kk′~ k₀k′₀~ k₁k′₁~ : k ⍮ k′ ~ˣ⁻} {k″k‴~ k″₀k‴₀~ k″₁k‴₁~ : k″ ⍮ k‴ ~ˣ⁻} →
                kk′~ ~~ˣ⁻ k₀k′₀~ ⊞ k₁k′₁~ →
                k″k‴~ ~~ˣ⁻ k″₀k‴₀~ ⊞ k″₁k‴₁~ →
                k₀k′₀~ is-all-dis⁰~ˣ⁻ →
                k″₀k‴₀~ is-all-dis⁰~ˣ⁻ →
                k₀k′₀~ ++ˣ⁻ k″₀k‴₀~ ⊢ I ~ᴹ L →
                k₁k′₁~ ++ˣ⁻ !∷ᵘ k″₁k‴₁~ ⊢ J ~ᴹ M →
                ----------------------------------------------------------------------------
                kk′~ ++ˣ⁻ k″k‴~ ⊢ BP.[ I /¹ k ] J ~ᴹ [ `lift L /[ uMode ] lengthˣ⁻ kk′~ ] M
!∷ᵘ[/¹]~ᴹ[/]ᵘ     {J = _}          {_}                   {_}    {_}      {k₁k′₁~} kk′~~ k″k‴~~ k₀k′₀~Dis k″₀k‴₀~Dis ~L (`unit k₁k′₁~!∷ᵘk″₁k‴₁~Dis)              = `unit kk′~k″k‴~Dis
  where
    kk′~k″k‴~Dis = is-all-dis⁰~ˣ⁻-++⁺ (~~ˣ⁻⊞⁻¹-preserves-is-all-dis⁰~ˣ⁻ k₀k′₀~Dis (is-all-dis⁰~ˣ⁻-++⁻ˡ k₁k′₁~ k₁k′₁~!∷ᵘk″₁k‴₁~Dis) kk′~~) (~~ˣ⁻⊞⁻¹-preserves-is-all-dis⁰~ˣ⁻ k″₀k‴₀~Dis (is-all-dis⁰~ˣ⁻-++⁻ʳ (!∷ᵘ [])  (is-all-dis⁰~ˣ⁻-++⁻ʳ k₁k′₁~ k₁k′₁~!∷ᵘk″₁k‴₁~Dis)) k″k‴~~)
!∷ᵘ[/¹]~ᴹ[/]ᵘ     {J = _}          {_}                   {_}    {_}      {k₁k′₁~} kk′~~ k″k‴~~ k₀k′₀~Dis k″₀k‴₀~Dis ~L (`bang k₁k′₁~!∷ᵘk″₁k‴₁~Dis ~M)           = `bang kk′~k″k‴~Dis (!∷ᵘ[/¹]~ᴹ[/]ᵘ kk′~~ k″k‴~~ k₀k′₀~Dis k″₀k‴₀~Dis ~L ~M)
  where
    kk′~k″k‴~Dis = is-all-dis⁰~ˣ⁻-++⁺ (~~ˣ⁻⊞⁻¹-preserves-is-all-dis⁰~ˣ⁻ k₀k′₀~Dis (is-all-dis⁰~ˣ⁻-++⁻ˡ k₁k′₁~ k₁k′₁~!∷ᵘk″₁k‴₁~Dis) kk′~~) (~~ˣ⁻⊞⁻¹-preserves-is-all-dis⁰~ˣ⁻ k″₀k‴₀~Dis (is-all-dis⁰~ˣ⁻-++⁻ʳ (!∷ᵘ [])  (is-all-dis⁰~ˣ⁻-++⁻ʳ k₁k′₁~ k₁k′₁~!∷ᵘk″₁k‴₁~Dis)) k″k‴~~)
!∷ᵘ[/¹]~ᴹ[/]ᵘ     {J = _}          {`let-return M `in N} {_}    {_}      {k₁k′₁~} kk′~~ k″k‴~~ k₀k′₀~Dis k″₀k‴₀~Dis ~L (k₁k′₁~!∷ᵘk″₁k‴₁~~ ⊢`let-bang ~M `in ~N)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index k₁k′₁~!∷ᵘk″₁k‴₁~~
    with _ , _ , _ , _ , refl , refl , k₁k′₁~~ , !∷ᵘ k″₁k‴₁~~ ← ~~ˣ⁻⊞-preserves-++ k₁k′₁~ k₁k′₁~!∷ᵘk″₁k‴₁~~
      with _ , _ , kk′~₂~ , kk′~₃~ , kk′~~′ ← ~~ˣ⁻⊞-contraction-assocʳ kk′~~ k₁k′₁~~ k₀k′₀~Dis
         | _ , _ , k″k‴~₂~ , k″k‴~₃~ , k″k‴~~′ ← ~~ˣ⁻⊞-contraction-assocʳ k″k‴~~ k″₁k‴₁~~ k″₀k‴₀~Dis
        with eq₀ , eq₁ ← lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~′                                                                                                         = ~~ˣ⁻⊞-++ kk′~~′ k″k‴~~′ ⊢`let-bang subst-~ᴹ[/-] eq₀ M (!∷ᵘ[/¹]~ᴹ[/]ᵘ kk′~₂~ k″k‴~₂~ k₀k′₀~Dis k″₀k‴₀~Dis ~L ~M) `in subst-~ᴹ[/-] (cong suc eq₁) N (!∷ᵘ[/¹]~ᴹ[/]ᵘ (!∷ᵘ kk′~₃~) k″k‴~₃~ (!∷ᵘ k₀k′₀~Dis) k″₀k‴₀~Dis (wk[↑¹]~ᴹwk[↑] [] (!∷ᵘ []) ~L) ~N)
!∷ᵘ[/¹]~ᴹ[/]ᵘ {k} {J = BP.`#¹ BPv} {`unlift`# v}         {_}    {_}      {k₁k′₁~} kk′~~ k″k‴~~ k₀k′₀~Dis k″₀k‴₀~Dis ~L (`#¹ ~v)
  with eq₀ , eq₁ ← lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~
     | k₀k′₀~k″₀k‴₀~Dis ← is-all-dis⁰~ˣ⁻-++⁺ k₀k′₀~Dis k″₀k‴₀~Dis
     | kk′~k″k‴~~ ← ~~ˣ⁻⊞-++ kk′~~ k″k‴~~
    with BPv ℕ.≥? k
...    | no  BPv≱k
      with BPv<k ← ℕ.≰⇒> BPv≱k
        with v<kk′~ ← ℕ.<-transˡ (∈ᵘ∧<⇒< k₁k′₁~ ~v BPv<k) (ℕ.≤-reflexive eq₁)
          rewrite dec-no (_ ℕ.≥? _) (ℕ.<⇒≱ v<kk′~)                                                                                                              = `#¹ ~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧∈ᵘ⇒∈ᵘ kk′~k″k‴~~ k₀k′₀~k″₀k‴₀~Dis (~ᵛ∈ᵘ!∷ᵘ∧<⇒~ᵛ∈ᵘ k₁k′₁~ ~v BPv<k)
...    | yes BPv≥k
      with BPv ℕ.≟ k
...      | no  BPv≢k
        with BPv>k ← ℕ.≤∧≢⇒< BPv≥k (≢-sym BPv≢k)
          with v>kk′~ ← ℕ.<-transʳ (ℕ.≤-reflexive (sym eq₁)) (∈ᵘ∧>⇒> k₁k′₁~ ~v BPv>k)
            rewrite proj₂ (dec-yes (_ ℕ.≥? _) (ℕ.<⇒≤ v>kk′~))
                  | dec-no (_ ℕ.≟ _) (≢-sym (ℕ.<⇒≢ v>kk′~))                                                                                                     = `#¹ ~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧∈ᵘ⇒∈ᵘ kk′~k″k‴~~ k₀k′₀~k″₀k‴₀~Dis (~ᵛ∈ᵘ!∷ᵘ∧>⇒pred~ᵛpred∈ᵘ k₁k′₁~ ~v BPv>k)
...      | yes refl
        with v≡kk′~ ← trans (∈ᵘ!∷ᵘ∧≡⇒≡ k₁k′₁~ ~v refl) eq₁
           | k₁k′₁~Dis , k″₁k‴₁~Dis ← ~ᵛ∈ᵘ!∷ᵘ∧≡⇒is-all-dis⁰~ˣ⁻ k₁k′₁~ ~v refl
          with k₁k′₁~k″₁k‴₁~Dis ← is-all-dis⁰~ˣ⁻-++⁺ k₁k′₁~Dis k″₁k‴₁~Dis
          rewrite proj₂ (dec-yes (_ ℕ.≥? _) (ℕ.≤-reflexive (sym v≡kk′~)))
                | proj₂ (dec-yes (_ ℕ.≟ _) v≡kk′~)                                                                                                              = `unlift-`lift (~~ˣ⁻⊞⁻¹-preserves-is-all-dis⁰~ˣ⁻ k₀k′₀~k″₀k‴₀~Dis k₁k′₁~k″₁k‴₁~Dis kk′~k″k‴~~) (~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒~ᴹ (~~ˣ⁻⊞-commute kk′~k″k‴~~) k₁k′₁~k″₁k‴₁~Dis ~L)
!∷ᵘ[/¹]~ᴹ[/]ᵘ                                                                     kk′~~ k″k‴~~ k₀k′₀~Dis k″₀k‴₀~Dis ~L (`λ⦂ ~S ∘ ~M)                            = `λ⦂ ~S ∘ (!∷ᵘ[/¹]~ᴹ[/]ᵘ (to-right!∷ˡ kk′~~) k″k‴~~ (?∷ˡ k₀k′₀~Dis) k″₀k‴₀~Dis (subst (_ ⊢_~ᴹ _) (~ᴹ∧≥⇒wk[↑⁰]≡ 1 [] ~L (is-all-dis⁰~ˣ⁻-++⁺ k₀k′₀~Dis k″₀k‴₀~Dis) z≤n) (wk[↑⁰]~ᴹwk[↑] [] (?∷ˡ []) ~L) ) ~M)
!∷ᵘ[/¹]~ᴹ[/]ᵘ     {J = _}          {M `$ N}              {_}    {_}      {k₁k′₁~} kk′~~ k″k‴~~ k₀k′₀~Dis k″₀k‴₀~Dis ~L (k₁k′₁~!∷ᵘk″₁k‴₁~~ ⊢ ~M `$ ~N)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index k₁k′₁~!∷ᵘk″₁k‴₁~~
    with _ , _ , _ , _ , refl , refl , k₁k′₁~~ , !∷ᵘ k″₁k‴₁~~ ← ~~ˣ⁻⊞-preserves-++ k₁k′₁~ k₁k′₁~!∷ᵘk″₁k‴₁~~
      with _ , _ , kk′~₂~ , kk′~₃~ , kk′~~′ ← ~~ˣ⁻⊞-contraction-assocʳ kk′~~ k₁k′₁~~ k₀k′₀~Dis
         | _ , _ , k″k‴~₂~ , k″k‴~₃~ , k″k‴~~′ ← ~~ˣ⁻⊞-contraction-assocʳ k″k‴~~ k″₁k‴₁~~ k″₀k‴₀~Dis
        with eq₀ , eq₁ ← lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~′                                                                                                         = ~~ˣ⁻⊞-++ kk′~~′ k″k‴~~′ ⊢ subst-~ᴹ[/-] eq₀ M (!∷ᵘ[/¹]~ᴹ[/]ᵘ kk′~₂~ k″k‴~₂~ k₀k′₀~Dis k″₀k‴₀~Dis ~L ~M) `$ subst-~ᴹ[/-] eq₁ N (!∷ᵘ[/¹]~ᴹ[/]ᵘ kk′~₃~ k″k‴~₃~ k₀k′₀~Dis k″₀k‴₀~Dis ~L ~N)
!∷ᵘ[/¹]~ᴹ[/]ᵘ     {J = BP.`#⁰ BPy} {`# y}                {kk′~} {_}      {k₁k′₁~} kk′~~ k″k‴~~ k₀k′₀~Dis k″₀k‴₀~Dis ~L (`#⁰ ~y)
  with eq₀ , eq₁ ← lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~
     | k₀k′₀~k″₀k‴₀~Dis ← is-all-dis⁰~ˣ⁻-++⁺ k₀k′₀~Dis k″₀k‴₀~Dis
     | kk′~k″k‴~~ ← ~~ˣ⁻⊞-++ kk′~~ k″k‴~~
    with y ℕ.≥? lengthˣ⁻ kk′~
...    | no  y≱kk′~
      with y<kk′~ ← ℕ.≰⇒> y≱kk′~ = `#⁰ ~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧∈ˡ⇒∈ˡ kk′~k″k‴~~ k₀k′₀~k″₀k‴₀~Dis (~ᵛ∈ˡ!∷ᵘ∧<⇒~ᵛ∈ˡ k₁k′₁~ ~y (ℕ.<-transˡ y<kk′~ (ℕ.≤-reflexive (sym eq₁))))
...    | yes y≥kk′~
      with y≢kk′~ ← subst (_ ≢_) (proj₂ (lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~)) (∈ˡ!∷ᵘ⇒≢ k₁k′₁~ ~y)
        with y>kk′~ ← ℕ.≤∧≢⇒< y≥kk′~ (≢-sym y≢kk′~)
          rewrite dec-no (_ ℕ.≟ _) y≢kk′~                                                                                                                       = `#⁰ ~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧∈ˡ⇒∈ˡ kk′~k″k‴~~ k₀k′₀~k″₀k‴₀~Dis (~ᵛ∈ˡ!∷ᵘ∧>⇒~ᵛpred∈ˡ k₁k′₁~ ~y (ℕ.<-transʳ (ℕ.≤-reflexive eq₁) y>kk′~))
!∷ᵘ[/¹]~ᴹ[/]ᵘ     {J = _}          {_}                   {_}    {_}      {k₁k′₁~} kk′~~ k″k‴~~ k₀k′₀~Dis k″₀k‴₀~Dis ~L (`unlift-`lift k₁k′₁~!∷ᵘk″₁k‴₁~Dis ~M)   = `unlift-`lift kk′~k″k‴~Dis (!∷ᵘ[/¹]~ᴹ[/]ᵘ kk′~~ k″k‴~~ k₀k′₀~Dis k″₀k‴₀~Dis ~L ~M)
  where
    kk′~k″k‴~Dis = is-all-dis⁰~ˣ⁻-++⁺ (~~ˣ⁻⊞⁻¹-preserves-is-all-dis⁰~ˣ⁻ k₀k′₀~Dis (is-all-dis⁰~ˣ⁻-++⁻ˡ k₁k′₁~ k₁k′₁~!∷ᵘk″₁k‴₁~Dis) kk′~~) (~~ˣ⁻⊞⁻¹-preserves-is-all-dis⁰~ˣ⁻ k″₀k‴₀~Dis (is-all-dis⁰~ˣ⁻-++⁻ʳ (!∷ᵘ [])  (is-all-dis⁰~ˣ⁻-++⁻ʳ k₁k′₁~ k₁k′₁~!∷ᵘk″₁k‴₁~Dis)) k″k‴~~)

≥∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒[/⁰]≡ : {kk′~ : k ⍮ k′ ~ˣ⁻} →
                            x ℕ.≥ k′ →
                            kk′~′ is-all-dis⁰~ˣ⁻ →
                            kk′~ ++ˣ⁻ kk′~′ ⊢ J ~ᴹ M →
                            ---------------------------
                            BP.[ I /⁰ x ] J ≡ J
≥∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒[/⁰]≡               x≥ kk′~′Dis (`unit _)                         = refl
≥∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒[/⁰]≡               x≥ kk′~′Dis (`bang _ ~M)                      = refl
≥∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒[/⁰]≡ {kk′~ = kk′~} x≥ kk′~′Dis (kk′~kk′~′~ ⊢`let-bang ~M `in ~N)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~kk′~′~
    with _ , _ , _ , _ , refl , refl , kk′~~ , kk′~′~ ← ~~ˣ⁻⊞-preserves-++ kk′~ kk′~kk′~′~
      with kk′~′₀Dis , kk′~′₁Dis ← ~~ˣ⁻⊞-preserves-is-all-dis⁰~ˣ⁻ kk′~′Dis kk′~′~     = cong₂ BP.`let-bang_`in_ (≥∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒[/⁰]≡ x≥ kk′~′₀Dis ~M) (≥∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒[/⁰]≡ x≥ kk′~′₁Dis ~N)
≥∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒[/⁰]≡               x≥ kk′~′Dis (`#¹ ~v)                          = refl
≥∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒[/⁰]≡               x≥ kk′~′Dis (`λ⦂ ~S ∘ ~M)                     = cong (BP.`λ⦂ _ ∘_) (≥∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒[/⁰]≡ (s≤s x≥) kk′~′Dis ~M)
≥∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒[/⁰]≡ {kk′~ = kk′~} x≥ kk′~′Dis (kk′~kk′~′~ ⊢ ~M `$ ~N)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~kk′~′~
    with _ , _ , _ , _ , refl , refl , kk′~~ , kk′~′~ ← ~~ˣ⁻⊞-preserves-++ kk′~ kk′~kk′~′~
      with kk′~′₀Dis , kk′~′₁Dis ← ~~ˣ⁻⊞-preserves-is-all-dis⁰~ˣ⁻ kk′~′Dis kk′~′~     = cong₂ BP._`$_ (≥∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒[/⁰]≡ x≥ kk′~′₀Dis ~M) (≥∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒[/⁰]≡ x≥ kk′~′₁Dis ~N)
≥∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒[/⁰]≡               x≥ kk′~′Dis (`#⁰ ~y)                          = lemma x≥ kk′~′Dis ~y
  where
    lemma⊥ : {kk′~ : k ⍮ k′ ~ˣ⁻} →
             kk′~ is-all-dis⁰~ˣ⁻ →
             ----------------------
             ¬ (BP.x ~ᵛ x ∈ˡ kk′~)
    lemma⊥ (!∷ᵘ kk′~Dis) (there!∷ᵘ ~x) = lemma⊥ kk′~Dis ~x
    lemma⊥ (?∷ˡ kk′~Dis) (there?∷ˡ ~x) = lemma⊥ kk′~Dis ~x

    lemma< : {kk′~ : k ⍮ k′ ~ˣ⁻} →
             kk′~′ is-all-dis⁰~ˣ⁻ →
             BP.y ~ᵛ y ∈ˡ kk′~ ++ˣ⁻ kk′~′ →
             -------------------------------
             BP.y ℕ.< k′
    lemma< {kk′~ = []}       kk′~′Dis ~y            with () ← lemma⊥ kk′~′Dis ~y
    lemma< {kk′~ = !∷ᵘ kk′~} kk′~′Dis (there!∷ᵘ ~y) = lemma< kk′~′Dis ~y
    lemma< {kk′~ = ?∷ˡ kk′~} kk′~′Dis (there?∷ˡ ~y) = s≤s (lemma< kk′~′Dis ~y)
    lemma< {kk′~ = !∷ˡ kk′~} kk′~′Dis (here x)      = s≤s z≤n

    lemma : {kk′~ : k ⍮ k′ ~ˣ⁻} →
            x ℕ.≥ k′ →
            kk′~′ is-all-dis⁰~ˣ⁻ →
            BP.y ~ᵛ y ∈ˡ kk′~ ++ˣ⁻ kk′~′ →
            ------------------------------------------------
            idx[ I / x ] BP.y along BP.`#⁰_ ≡ (BP.`#⁰ BP.y)
    lemma x≥ kk′~′Dis ~y
      rewrite dec-no (_ ℕ.≥? _) (ℕ.<⇒≱ (ℕ.<-transˡ (lemma< kk′~′Dis ~y) x≥)) = refl
≥∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒[/⁰]≡               x≥ kk′~′Dis (`unlift-`lift _ ~M)              = ≥∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒[/⁰]≡ x≥ kk′~′Dis ~M

?∷ˡ[/⁰]~ᴹ[/]ˡ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                kk′~ ++ˣ⁻ ?∷ˡ k″k‴~ ⊢ J ~ᴹ M →
                ----------------------------------------------------------------------------
                kk′~ ++ˣ⁻ k″k‴~ ⊢ BP.[ I /⁰ k′ ] J ~ᴹ [ L /[ lMode ] lengthˣ⁻ kk′~ ] M
?∷ˡ[/⁰]~ᴹ[/]ˡ                                             kk′~ (`unit kk′~?∷ˡk″k‴~Dis)
  with ?∷ˡ k″k‴~Dis ← is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~?∷ˡk″k‴~Dis                                                         = `unit (is-all-dis⁰~ˣ⁻-++⁺ (is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~?∷ˡk″k‴~Dis) k″k‴~Dis)
?∷ˡ[/⁰]~ᴹ[/]ˡ {_} {k′} {J = _} {_}                    {I} kk′~ (`bang kk′~?∷ˡk″k‴~Dis ~M)
  with ?∷ˡ k″k‴~Dis ← is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~?∷ˡk″k‴~Dis                                                         = `bang (is-all-dis⁰~ˣ⁻-++⁺ (is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~?∷ˡk″k‴~Dis) k″k‴~Dis) (subst (_ ⊢_~ᴹ _) (≥∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒[/⁰]≡ {I = I} {kk′~ = []} (z≤n {k′}) kk′~?∷ˡk″k‴~Dis ~M) (?∷ˡ[/⁰]~ᴹ[/]ˡ kk′~ ~M))
?∷ˡ[/⁰]~ᴹ[/]ˡ                                             kk′~ (_⊢`let-bang_`in_ {L = M} {M = N} kk′~?∷ˡk″k‴~~ ~M  ~N)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~?∷ˡk″k‴~~
    with kk′~₀ , kk′~₁ , _ , _ , refl , refl , kk′~~ , ?∷ˡ k″k‴~~ ← ~~ˣ⁻⊞-preserves-++ kk′~ kk′~?∷ˡk″k‴~~              = ~~ˣ⁻⊞-++ kk′~~ k″k‴~~ ⊢`let-bang subst-~ᴹ[/-] (proj₁ (lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~)) M (?∷ˡ[/⁰]~ᴹ[/]ˡ kk′~₀ ~M) `in subst-~ᴹ[/-] (cong suc (proj₂ (lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~))) N (?∷ˡ[/⁰]~ᴹ[/]ˡ (!∷ᵘ kk′~₁) ~N)
?∷ˡ[/⁰]~ᴹ[/]ˡ {_} {_}  {J = _}          {`unlift`# v}     kk′~ (`#¹ ~v)
  with v ℕ.≥? lengthˣ⁻ kk′~
...  | no  v≱kk′~ = `#¹ ~ᵛ∈ᵘ?∷ˡ∧<⇒~ᵛ∈ᵘ kk′~ ~v (ℕ.≰⇒> v≱kk′~)
...  | yes v≥kk′~
    with v≢kk′~ ← ∈ᵘ?∷ˡ⇒≢ kk′~ ~v
      rewrite dec-no (_ ℕ.≟ _) v≢kk′~ = `#¹ ~ᵛ∈ᵘ?∷ˡ∧>⇒~ᵛpred∈ᵘ kk′~ ~v (ℕ.≤∧≢⇒< v≥kk′~ (≢-sym v≢kk′~))
?∷ˡ[/⁰]~ᴹ[/]ˡ                                             kk′~ (`λ⦂ ~S ∘ ~M)                                           = `λ⦂ ~S ∘ ?∷ˡ[/⁰]~ᴹ[/]ˡ (!∷ˡ kk′~) ~M
?∷ˡ[/⁰]~ᴹ[/]ˡ                                             kk′~ (_⊢_`$_ {L = M} {M = N} kk′~?∷ˡk″k‴~~ ~M ~N)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~?∷ˡk″k‴~~
    with kk′~₀ , kk′~₁ , _ , _ , refl , refl , kk′~~ , ?∷ˡ k″k‴~~ ← ~~ˣ⁻⊞-preserves-++ kk′~ kk′~?∷ˡk″k‴~~              = ~~ˣ⁻⊞-++ kk′~~ k″k‴~~ ⊢ subst-~ᴹ[/-] (proj₁ (lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~)) M (?∷ˡ[/⁰]~ᴹ[/]ˡ kk′~₀ ~M) `$ subst-~ᴹ[/-] (proj₂ (lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~)) N (?∷ˡ[/⁰]~ᴹ[/]ˡ kk′~₁ ~N)
?∷ˡ[/⁰]~ᴹ[/]ˡ {_} {k′} {J = BP.`#⁰ BPy} {`# y}            kk′~ (`#⁰ ~y)
  with BPy ℕ.≥? k′
...  | no  BPy≱k
    with BPy<k ← ℕ.≰⇒> BPy≱k
      rewrite dec-no (_ ℕ.≥? _) (ℕ.<⇒≱ (∈ˡ∧<⇒< kk′~ ~y BPy<k))                                                         = `#⁰ ~ᵛ∈ˡ?∷ˡ∧<⇒~ᵛ∈ˡ kk′~ ~y BPy<k
...  | yes BPy≥k
    with BPy≢k ← ∈ˡ?∷ˡ⇒≢ kk′~ ~y
      with BPy>k ← ℕ.≤∧≢⇒< BPy≥k (≢-sym BPy≢k)
        with y>k ← ∈ˡ∧>⇒> kk′~ ~y BPy>k
          rewrite dec-no (_ ℕ.≟ _) BPy≢k
                | proj₂ (dec-yes (_ ℕ.≥? _) (ℕ.<⇒≤ y>k))
                | dec-no (_ ℕ.≟ _) (≢-sym (ℕ.<⇒≢ y>k))                                                                 = `#⁰ ~ᵛ∈ˡ?∷ˡ∧>⇒pred~ᵛpred∈ˡ kk′~ ~y BPy>k
?∷ˡ[/⁰]~ᴹ[/]ˡ                                             kk′~ (`unlift-`lift kk′~?∷ˡk″k‴~Dis ~M)
  with ?∷ˡ k″k‴~Dis ← is-all-dis⁰~ˣ⁻-++⁻ʳ kk′~ kk′~?∷ˡk″k‴~Dis                                                         = `unlift-`lift (is-all-dis⁰~ˣ⁻-++⁺ (is-all-dis⁰~ˣ⁻-++⁻ˡ kk′~ kk′~?∷ˡk″k‴~Dis) k″k‴~Dis) (?∷ˡ[/⁰]~ᴹ[/]ˡ kk′~ ~M)

!∷ˡ[/⁰]~ᴹ[/]ˡ : {kk′~ k₀k′₀~ k₁k′₁~ : k ⍮ k′ ~ˣ⁻} {k″k‴~ k″₀k‴₀~ k″₁k‴₁~ : k″ ⍮ k‴ ~ˣ⁻} →
                kk′~ ~~ˣ⁻ k₀k′₀~ ⊞ k₁k′₁~ →
                k″k‴~ ~~ˣ⁻ k″₀k‴₀~ ⊞ k″₁k‴₁~ →
                k₀k′₀~ ++ˣ⁻ k″₀k‴₀~ ⊢ I ~ᴹ L →
                k₁k′₁~ ++ˣ⁻ !∷ˡ k″₁k‴₁~ ⊢ J ~ᴹ M →
                ----------------------------------------------------------------------------
                kk′~ ++ˣ⁻ k″k‴~ ⊢ BP.[ I /⁰ k′ ] J ~ᴹ [ L /[ lMode ] lengthˣ⁻ kk′~ ] M
!∷ˡ[/⁰]~ᴹ[/]ˡ                                  {k₁k′₁~ = k₁k′₁~} kk′~~ k″k‴~~ ~L (`unit k₁k′₁~!∷ˡk″₁k‴₁~Dis)                                with () ← is-all-dis⁰~ˣ⁻-++⁻ʳ k₁k′₁~ k₁k′₁~!∷ˡk″₁k‴₁~Dis
!∷ˡ[/⁰]~ᴹ[/]ˡ                                  {k₁k′₁~ = k₁k′₁~} kk′~~ k″k‴~~ ~L (`bang k₁k′₁~!∷ˡk″₁k‴₁~Dis ~M)                             with () ← is-all-dis⁰~ˣ⁻-++⁻ʳ k₁k′₁~ k₁k′₁~!∷ˡk″₁k‴₁~Dis
!∷ˡ[/⁰]~ᴹ[/]ˡ                                  {k₁k′₁~ = k₁k′₁~} kk′~~ k″k‴~~ ~L (_⊢`let-bang_`in_ {L = M} {M = N} k₁k′₁~!∷ˡk″₁k‴₁~~ ~M ~N)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
     | refl , refl , refl , refl ← ~~ˣ⁻⊞-index k″k‴~~
     | refl , refl , refl , refl ← ~~ˣ⁻⊞-index k₁k′₁~!∷ˡk″₁k‴₁~~
    with k₂k′₂~ , k₃k′₃~ , ∷ˡk″₂k‴₂~ , ∷ˡk″₃k‴₃~ , refl , refl , k₁k′₁~~ , !∷ˡk″₁k‴₁~~ ← ~~ˣ⁻⊞-preserves-++ k₁k′₁~ k₁k′₁~!∷ˡk″₁k‴₁~~
      with ∷ˡk″₂k‴₂~   | ∷ˡk″₃k‴₃~   | !∷ˡk″₁k‴₁~~
...      | !∷ˡ k″₂k‴₂~ | ?∷ˡ k″₃k‴₃~ | to-left!∷ˡ k″₁k‴₁~~
        with _ , kk′~₀′~ , kk′~~₀ ← ~~ˣ⁻⊞-assocʳ kk′~~ k₁k′₁~~
           | _ , k″k‴~₀′~ , k″k‴~~₀ ← ~~ˣ⁻⊞-assocʳ k″k‴~~ k″₁k‴₁~~                                                                          = ~~ˣ⁻⊞-++ kk′~~₀ k″k‴~~₀ ⊢`let-bang subst-~ᴹ[/-] (proj₁ (lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~₀)) M (!∷ˡ[/⁰]~ᴹ[/]ˡ kk′~₀′~ k″k‴~₀′~ ~L ~M) `in subst-~ᴹ[/-] (cong suc (proj₂ (lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~₀))) N (?∷ˡ[/⁰]~ᴹ[/]ˡ (!∷ᵘ k₃k′₃~) ~N) 
...      | ?∷ˡ k″₂k‴₂~ | !∷ˡ k″₃k‴₃~ | to-right!∷ˡ k″₁k‴₁~~
        with _ , kk′~₀′~ , kk′~~₀ ← ~~ˣ⁻⊞-assocʳ kk′~~ (~~ˣ⁻⊞-commute k₁k′₁~~)
           | _ , k″k‴~₀′~ , k″k‴~~₀ ← ~~ˣ⁻⊞-assocʳ k″k‴~~ (~~ˣ⁻⊞-commute k″₁k‴₁~~)                                                          = ~~ˣ⁻⊞-commute (~~ˣ⁻⊞-++ kk′~~₀ k″k‴~~₀) ⊢`let-bang subst-~ᴹ[/-] (proj₂ (lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~₀)) M (?∷ˡ[/⁰]~ᴹ[/]ˡ k₂k′₂~ ~M) `in subst-~ᴹ[/-] (cong suc (proj₁ (lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~₀))) N (!∷ˡ[/⁰]~ᴹ[/]ˡ (!∷ᵘ kk′~₀′~) k″k‴~₀′~ (wk[↑¹]~ᴹwk[↑] [] (!∷ᵘ []) ~L) ~N)
!∷ˡ[/⁰]~ᴹ[/]ˡ                                  {k₁k′₁~ = k₁k′₁~} kk′~~ k″k‴~~ ~L (`#¹ ~v)                                                   with () ← ¬~ᵛ∈ᵘ!∷ˡ k₁k′₁~ ~v
!∷ˡ[/⁰]~ᴹ[/]ˡ                                                    kk′~~ k″k‴~~ ~L (`λ⦂ ~S ∘ ~M)                                              = `λ⦂ ~S ∘ (!∷ˡ[/⁰]~ᴹ[/]ˡ (to-right!∷ˡ kk′~~) k″k‴~~ (wk[↑⁰]~ᴹwk[↑] [] (?∷ˡ []) ~L) ~M)
!∷ˡ[/⁰]~ᴹ[/]ˡ                                  {k₁k′₁~ = k₁k′₁~} kk′~~ k″k‴~~ ~L (_⊢_`$_ {L = M} {M = N} k₁k′₁~!∷ˡk″₁k‴₁~~ ~M ~N)
  with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
     | refl , refl , refl , refl ← ~~ˣ⁻⊞-index k″k‴~~
     | refl , refl , refl , refl ← ~~ˣ⁻⊞-index k₁k′₁~!∷ˡk″₁k‴₁~~
    with k₂k′₂~ , k₃k′₃~ , ∷ˡk″₂k‴₂~ , ∷ˡk″₃k‴₃~ , refl , refl , k₁k′₁~~ , !∷ˡk″₁k‴₁~~ ← ~~ˣ⁻⊞-preserves-++ k₁k′₁~ k₁k′₁~!∷ˡk″₁k‴₁~~
      with ∷ˡk″₂k‴₂~   | ∷ˡk″₃k‴₃~   | !∷ˡk″₁k‴₁~~
...      | !∷ˡ k″₂k‴₂~ | ?∷ˡ k″₃k‴₃~ | to-left!∷ˡ k″₁k‴₁~~
        with _ , kk′~₀′~ , kk′~~₀ ← ~~ˣ⁻⊞-assocʳ kk′~~ k₁k′₁~~
           | _ , k″k‴~₀′~ , k″k‴~~₀ ← ~~ˣ⁻⊞-assocʳ k″k‴~~ k″₁k‴₁~~                                                                          = ~~ˣ⁻⊞-++ kk′~~₀ k″k‴~~₀ ⊢ subst-~ᴹ[/-] (proj₁ (lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~₀)) M (!∷ˡ[/⁰]~ᴹ[/]ˡ kk′~₀′~ k″k‴~₀′~ ~L ~M) `$ subst-~ᴹ[/-] (proj₂ (lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~₀)) N (?∷ˡ[/⁰]~ᴹ[/]ˡ k₃k′₃~ ~N) 
...      | ?∷ˡ k″₂k‴₂~ | !∷ˡ k″₃k‴₃~ | to-right!∷ˡ k″₁k‴₁~~
        with _ , kk′~₀′~ , kk′~~₀ ← ~~ˣ⁻⊞-assocʳ kk′~~ (~~ˣ⁻⊞-commute k₁k′₁~~)
           | _ , k″k‴~₀′~ , k″k‴~~₀ ← ~~ˣ⁻⊞-assocʳ k″k‴~~ (~~ˣ⁻⊞-commute k″₁k‴₁~~)                                                          = ~~ˣ⁻⊞-commute (~~ˣ⁻⊞-++ kk′~~₀ k″k‴~~₀) ⊢ subst-~ᴹ[/-] (proj₂ (lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~₀)) M (?∷ˡ[/⁰]~ᴹ[/]ˡ k₂k′₂~ ~M) `$ subst-~ᴹ[/-] (proj₁ (lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~₀)) N (!∷ˡ[/⁰]~ᴹ[/]ˡ kk′~₀′~ k″k‴~₀′~ ~L ~N)
!∷ˡ[/⁰]~ᴹ[/]ˡ {_} {k′} {J = BP.`#⁰ BPy} {`# y} {k₁k′₁~ = k₁k′₁~} kk′~~ k″k‴~~ ~L (`#⁰ ~y)
  with BPy≡k′ , y≡k₁k′₁~ , k₁k′₁Dis , k″₁k‴₁Dis ← ~ᵛ∈ˡ!∷ˡ⇒≡∧is-all-dis⁰~ˣ⁻ k₁k′₁~ ~y
    with y≡kk′~ ← trans y≡k₁k′₁~ (proj₂ (lengthˣ⁻-respects-~~ˣ⁻⊞ kk′~~))
      rewrite proj₂ (dec-yes (_ ℕ.≥? _) (ℕ.≤-reflexive (sym BPy≡k′)))
            | proj₂ (dec-yes (_ ℕ.≥? _) (ℕ.≤-reflexive (sym y≡kk′~)))
            | proj₂ (dec-yes (_ ℕ.≟ _) BPy≡k′)
            | proj₂ (dec-yes (_ ℕ.≟ _) y≡kk′~)                                                                                              = ~~ˣ⁻⊞∧is-all-dis⁰~ˣ⁻∧~ᴹ⇒~ᴹ (~~ˣ⁻⊞-commute (~~ˣ⁻⊞-++ kk′~~ k″k‴~~)) (is-all-dis⁰~ˣ⁻-++⁺ k₁k′₁Dis k″₁k‴₁Dis) ~L
!∷ˡ[/⁰]~ᴹ[/]ˡ                                  {k₁k′₁~ = k₁k′₁~} kk′~~ k″k‴~~ ~L (`unlift-`lift k₁k′₁~!∷ˡk″₁k‴₁~Dis ~M)                     with () ← is-all-dis⁰~ˣ⁻-++⁻ʳ k₁k′₁~ k₁k′₁~!∷ˡk″₁k‴₁~Dis

-- Bisimulation Properties of _~ᴹ_ Regarding OpSems
--
~ᴹ-simulation-helper : I BP.⟶ I′ →
                       (~L : [] ⊢ I ~ᴹ L) →
                       Acc ℕ._<_ (depth~ᴹ ~L) →
                       -----------------------------------
                       ∃ (λ L′ → L ⟶* L′ × [] ⊢ I′ ~ᴹ L′)
~ᴹ-simulation-helper I⟶                     (`unlift-`lift [] ~L)     (acc r)
  with _ , ⟶*L′[≤] , VL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
    with _ , ⟶*L″ , ~L″ ← ~ᴹ-simulation-helper I⟶ ~L′ (r _ (s≤s L′≤))         = -, ξ-of-↝*-⟶* _⟶[ uMode ≤]_ `unlift`lift ξ-`unlift`lift ⟶*L′[≤]
                                                                                  ◅◅ β-`↑ VL′ ◅ ⟶*L″
                                                                              , ~L″
~ᴹ-simulation-helper BP.ξ-`let-bang I⟶ `in- ([] ⊢`let-bang ~L `in ~M) (acc r)
  with _ , ⟶*L′ , ~L′ ← ~ᴹ-simulation-helper I⟶ ~L (r _ (s≤s (ℕ.m≤m⊔n _ _)))  = -, ξ-of-⟶* (`let-return_`in _) ξ-`let-return_`in- ⟶*L′
                                                                              , [] ⊢`let-bang ~L′ `in ~M
~ᴹ-simulation-helper BP.β-`!                ([] ⊢`let-bang ~L `in ~M) rec
  with _ , ⟶*`bangL′ , WL′ , ~L ← `bang-~ᴹ-inv ~L                             = -, ξ-of-⟶* (`let-return_`in _) ξ-`let-return_`in- ⟶*`bangL′
                                                                                  ◅◅ β-`↓ (`lift WL′) ◅ ε
                                                                              , !∷ᵘ[/¹]~ᴹ[/]ᵘ [] [] [] [] ~L ~M
~ᴹ-simulation-helper BP.ξ- I⟶ `$?           ([] ⊢ ~L `$ ~M)           (acc r)
  with _ , ⟶*L′ , ~L′ ← ~ᴹ-simulation-helper I⟶ ~L (r _ (s≤s (ℕ.m≤m⊔n _ _)))  = -, ξ-of-⟶* (_`$ _) ξ-_`$? ⟶*L′
                                                                              , [] ⊢ ~L′ `$ ~M
~ᴹ-simulation-helper (BP.ξ-! VI `$ J⟶)      ([] ⊢ ~L `$ ~M)           (acc r)
  with _ , ⟶*L′ , VL′ , ~L′ ← Value~ᴹ-normalize ~L VI
     | _ , ⟶*M′ , ~M′ ← ~ᴹ-simulation-helper J⟶ ~M (r _ (s≤s (ℕ.m≤n⊔m _ _)))  = -, ξ-of-⟶* (_`$ _) ξ-_`$? ⟶*L′
                                                                                  ◅◅ ξ-of-⟶* (_ `$_) (ξ-! VL′ `$_) ⟶*M′
                                                                              , [] ⊢ ~L′ `$ ~M′
~ᴹ-simulation-helper (BP.β-`⊸ VJ)           ([] ⊢ ~L `$ ~M)           rec
  with _ , _ , ⟶*`λ⦂ˡS′∘L′ , ~L′ , ~S′ ← `λ⦂-∙-~ᴹ-inv ~L
     | _ , ⟶*M′ , VM′ , ~M′ ← Value~ᴹ-normalize ~M VJ                         = -, ξ-of-⟶* (_`$ _) ξ-_`$? ⟶*`λ⦂ˡS′∘L′
                                                                                  ◅◅ ξ-of-⟶* (_ `$_) ξ-! `λ⦂ˡ _ ∘ _ `$_ ⟶*M′
                                                                                  ◅◅ β-`⊸ VM′ ◅ ε
                                                                              , !∷ˡ[/⁰]~ᴹ[/]ˡ [] [] ~M′ ~L′

~ᴹ-simulation : I BP.⟶ I′ →
                [] ⊢ I ~ᴹ L →
                -----------------------------------
                ∃ (λ L′ → L ⟶* L′ × [] ⊢ I′ ~ᴹ L′)
~ᴹ-simulation I⟶ ~L = ~ᴹ-simulation-helper I⟶ ~L (ℕ.<-wellFounded _)

~ᴹ⁻¹-simulation : L ⟶ L′ →
                  [] ⊢ I ~ᴹ L →
                  -----------------------------------------------
                  ∃ (λ I′ → I BP.⟶* I′ × [] ⊢ I′ ~ᴹ L′)
~ᴹ⁻¹-simulation (ξ-`unlift (ξ-`lift L⟶[≤])) (`unlift-`lift [] ~L)             = -, ε , `unlift-`lift [] (⟶[≤]-preserves-~ᴹ ~L L⟶[≤])
~ᴹ⁻¹-simulation (β-`↑ WL′)                  (`unlift-`lift [] ~L)             = -, ε , ~L
~ᴹ⁻¹-simulation (ξ-`return (ξ-`lift L⟶[≤])) (`bang [] ~L)                     = -, ε , `bang [] (⟶[≤]-preserves-~ᴹ ~L L⟶[≤])
~ᴹ⁻¹-simulation ξ-`let-return L⟶ `in-       ([] ⊢`let-bang ~L `in ~M)
  with _ , I⟶* , ~L′ ← ~ᴹ⁻¹-simulation L⟶ ~L                                  = -, BP.ξ-of-⟶* (BP.`let-bang_`in _) BP.ξ-`let-bang_`in- I⟶* , [] ⊢`let-bang ~L′ `in ~M
~ᴹ⁻¹-simulation (β-`↓ (`lift WL))           ([] ⊢`let-bang `bang b ~L `in ~M) = -, BP.β-`! ◅ ε , !∷ᵘ[/¹]~ᴹ[/]ᵘ [] [] [] [] ~L ~M
~ᴹ⁻¹-simulation ξ- L⟶ `$?                   ([] ⊢ ~L `$ ~M)
  with _ , I⟶* , ~L′ ← ~ᴹ⁻¹-simulation L⟶ ~L                                  = -, BP.ξ-of-⟶* (BP._`$ _) BP.ξ-_`$? I⟶* , [] ⊢ ~L′ `$ ~M
~ᴹ⁻¹-simulation (ξ-! VL′ `$ M⟶)             ([] ⊢ ~L `$ ~M)
  with _ , J⟶* , ~M′ ← ~ᴹ⁻¹-simulation M⟶ ~M                                  = -, BP.ξ-of-⟶* (_ BP.`$_) (BP.ξ-! []⊢~ᴹ⁻¹-respects-Value ~L VL′ `$_) J⟶* , [] ⊢ ~L `$ ~M′
~ᴹ⁻¹-simulation (β-`⊸ VM)                   ([] ⊢ (`λ⦂ ~S ∘ ~L) `$ ~M)        = -, BP.β-`⊸ ([]⊢~ᴹ⁻¹-respects-Value ~M VM) ◅ ε , !∷ˡ[/⁰]~ᴹ[/]ˡ [] [] ~M ~L
