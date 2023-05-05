------------------------------------------------------------
-- Embedding of DILL [Barber & Plotkin 1996] into LNL
------------------------------------------------------------
--
-- This module provides an embedding relation between DILL and LNL,
-- the proofs of completeness and soundness of the relation regarding
-- their typings, and bisimulation of the relation regarding their
-- operational semantics.
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
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; sym; trans; cong; cong₂; subst; ≢-sym)
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

  there!∷ᵘ : BP.u ~ᵛ u ∈ˡ kk′~ →
             --------------------------
             BP.u ~ᵛ suc u ∈ˡ !∷ᵘ kk′~

  there?∷ˡ : BP.u ~ᵛ u ∈ˡ kk′~ →
             ------------------------------
             suc BP.u ~ᵛ suc u ∈ˡ ?∷ˡ kk′~

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

-- Embedding Relation for Terms
--
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
          kk′~ ≡ kk′~₀
!∷ˡ-inj refl = refl

!∷ᵘ-inj : ∀ {kk′~ kk′~₀ : k ⍮ k′ ~ˣ⁻} →
          _≡_ {A = suc k ⍮ k′ ~ˣ⁻} (!∷ᵘ kk′~) (!∷ᵘ kk′~₀) →
          kk′~ ≡ kk′~₀
!∷ᵘ-inj refl = refl

~~ˣ⁻⊞-commute : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                kk′~ ~~ˣ⁻ kk′~₁ ⊞ kk′~₀
~~ˣ⁻⊞-commute []                  = []
~~ˣ⁻⊞-commute (!∷ᵘ         kk′~~) = !∷ᵘ ~~ˣ⁻⊞-commute kk′~~
~~ˣ⁻⊞-commute (?∷ˡ         kk′~~) = ?∷ˡ ~~ˣ⁻⊞-commute kk′~~
~~ˣ⁻⊞-commute (to-left!∷ˡ  kk′~~) = to-right!∷ˡ ~~ˣ⁻⊞-commute kk′~~
~~ˣ⁻⊞-commute (to-right!∷ˡ kk′~~) = to-left!∷ˡ ~~ˣ⁻⊞-commute kk′~~

~~ˣ⁻⊞-assocˡ : ∀ {kk′~ : k ⍮ k′ ~ˣ⁻} →
               kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
               kk′~₀ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
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
               ∃ (λ kk′~₀′ → kk′~₀′ ~~ˣ⁻ kk′~₀ ⊞ kk′~₂ × kk′~ ~~ˣ⁻ kk′~₀′ ⊞ kk′~₃)
~~ˣ⁻⊞-assocʳ kk′~~ kk′~₁~
  with _ , kk′~₁~ , kk′~~′ ← ~~ˣ⁻⊞-assocˡ (~~ˣ⁻⊞-commute kk′~~) (~~ˣ⁻⊞-commute kk′~₁~) = -, ~~ˣ⁻⊞-commute kk′~₁~ , ~~ˣ⁻⊞-commute kk′~~′

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
                           -------------------
                           ψ₀ BP.is-all-dis
~ˣ∧is-all-del⇒is-all-dis []         ΓDel                  = []
~ˣ∧is-all-del⇒is-all-dis (_ !∷ᵘ ~Γ) (_            ∷ ΓDel) = ~ˣ∧is-all-del⇒is-all-dis ~Γ ΓDel
~ˣ∧is-all-del⇒is-all-dis (_ ?∷ˡ ~Γ) (_            ∷ ΓDel) = refl ∷ ~ˣ∧is-all-del⇒is-all-dis ~Γ ΓDel
~ˣ∧is-all-del⇒is-all-dis (_ !∷ˡ ~Γ) (weakening () ∷ ΓDel)

~ˣ∧∤⇒is-all-dis : ψ₁ ⍮ ψ₀ ~ˣ Γ →
                  Γ ∤[ uMode ] Γ′ →
                  ψ₀ BP.is-all-dis
~ˣ∧∤⇒is-all-dis []         []                             = []
~ˣ∧∤⇒is-all-dis (_ !∷ᵘ ~Γ) (d∤                      ∷ Γ∤) = ~ˣ∧∤⇒is-all-dis ~Γ Γ∤
~ˣ∧∤⇒is-all-dis (_ ?∷ˡ ~Γ) (d∤                      ∷ Γ∤) = refl ∷ ~ˣ∧∤⇒is-all-dis ~Γ Γ∤
~ˣ∧∤⇒is-all-dis (_ !∷ˡ ~Γ) (delete _ (weakening ()) ∷ Γ∤)

~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
                               ψ₀ BP.is-all-dis →
                               eraseˣ ~Γ is-all-dis⁰~ˣ⁻
~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ []         ψ₀Dis          = []
~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ (_ !∷ᵘ ~Γ) ψ₀Dis          = !∷ᵘ (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ ψ₀Dis)
~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ (_ !∷ˡ ~Γ) (()   ∷ ψ₀Dis)
~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ (_ ?∷ˡ ~Γ) (refl ∷ ψ₀Dis) = ?∷ˡ (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ ψ₀Dis)

~ˣ∧is-all-dis⁰~ˣ⁻⇒is-all-dis : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
                               eraseˣ ~Γ is-all-dis⁰~ˣ⁻ →
                               ψ₀ BP.is-all-dis
~ˣ∧is-all-dis⁰~ˣ⁻⇒is-all-dis []         kk′~Dis       = []
~ˣ∧is-all-dis⁰~ˣ⁻⇒is-all-dis (_ !∷ᵘ ~Γ) (!∷ᵘ kk′~Dis) = ~ˣ∧is-all-dis⁰~ˣ⁻⇒is-all-dis ~Γ kk′~Dis
~ˣ∧is-all-dis⁰~ˣ⁻⇒is-all-dis (_ ?∷ˡ ~Γ) (?∷ˡ kk′~Dis) = refl ∷ (~ˣ∧is-all-dis⁰~ˣ⁻⇒is-all-dis ~Γ kk′~Dis)

eraseˣ-is-all-dis⁰~ˣ⁻⇒∤self : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
                              eraseˣ ~Γ is-all-dis⁰~ˣ⁻ →
                              Γ ∤[ uMode ] Γ
eraseˣ-is-all-dis⁰~ˣ⁻⇒∤self []         []            = []
eraseˣ-is-all-dis⁰~ˣ⁻⇒∤self (_ !∷ᵘ ~Γ) (!∷ᵘ kk′~Dis) = keep refl ∷ eraseˣ-is-all-dis⁰~ˣ⁻⇒∤self ~Γ kk′~Dis
eraseˣ-is-all-dis⁰~ˣ⁻⇒∤self (_ ?∷ˡ ~Γ) (?∷ˡ kk′~Dis) = delete (λ ()) unusable ∷ eraseˣ-is-all-dis⁰~ˣ⁻⇒∤self ~Γ kk′~Dis

~ˣ∧∤⇒≡ : ψ₁ ⍮ ψ₀ ~ˣ Γ →
         Γ ∤[ uMode ] Γ′ →
         Γ′ ≡ Γ
~ˣ∧∤⇒≡ ~Γ Γ∤ = ∤-det Γ∤ (eraseˣ-is-all-dis⁰~ˣ⁻⇒∤self ~Γ (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ (~ˣ∧∤⇒is-all-dis ~Γ Γ∤)))

-- ~⊞-preserves-~ˣ : ψ₁ ⍮ ψ₀ ~ˣ Γ →
--                   ψ₀ BP.~ ψ₀₀ ⊞ ψ₀₁ →
--                   ∃₂ (λ Γ₀ Γ₁ → ψ₁ ⍮ ψ₀₀ ~ˣ Γ₀ × ψ₁ ⍮ ψ₀₁ ~ˣ Γ₁ × Γ ~ Γ₀ ⊞ Γ₁)
-- ~⊞-preserves-~ˣ []          BP.[]                      = -, -, [] , [] , []
-- ~⊞-preserves-~ˣ (   ?∷ᵘ ~Γ) ψ₀~
--   with _ , _ , ~Γ₀ , ~Γ₁ , Γ~ ← ~⊞-preserves-~ˣ ~Γ ψ₀~ = -, -, ?∷ᵘ ~Γ₀ , ?∷ᵘ ~Γ₁ , unusable ∷ Γ~
-- ~⊞-preserves-~ˣ (~S !∷ᵘ ~Γ) ψ₀~
--   with _ , _ , ~Γ₀ , ~Γ₁ , Γ~ ← ~⊞-preserves-~ˣ ~Γ ψ₀~ = -, -, ~S !∷ᵘ ~Γ₀ , ~S !∷ᵘ ~Γ₁ , contraction _ ∷ Γ~
-- ~⊞-preserves-~ˣ (   ?∷ˡ ~Γ) ψ₀~
--   with _ , _ , ~Γ₀ , ~Γ₁ , Γ~ ← ~⊞-preserves-~ˣ ~Γ ψ₀~ = -, -, ?∷ˡ ~Γ₀ , ?∷ˡ ~Γ₁ , unusable ∷ Γ~
-- ~⊞-preserves-~ˣ (~S !∷ˡ ~Γ) (d~ BP.∷ ψ₀~)
--   with _ , _ , ~Γ₀ , ~Γ₁ , Γ~ ← ~⊞-preserves-~ˣ ~Γ ψ₀~
--     with d~
-- ...    | BP.to-left                                    = -, -, ~S !∷ˡ ~Γ₀ , ~S !∷ˡ ~Γ₁ , to-left ∷ Γ~
-- ...    | BP.to-right                                   = -, -, ~S !∷ˡ ~Γ₀ , ~S !∷ˡ ~Γ₁ , to-right ∷ Γ~
-- ...    | BP.unusable                                   = -, -, ~S !∷ˡ ~Γ₀ , ~S !∷ˡ ~Γ₁ , unusable ∷ Γ~

-- -- -- Properties of _~ᴹ_
-- -- --
-- -- ~ᴹ⇒++ˣ⁻~ᴹ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) →
-- --             kk′~ ⊢ I ~ᴹ L →
-- --             --------------------------------------------
-- --             kk′~ ++ˣ⁻ k″k‴~ ⊢ I ~ᴹ L
-- -- ~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ `unit                                      = `unit
-- -- ~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`bang ~L) = {!!}
-- --   -- with ~L′ ← ~ᴹ⇒++ˣ⁻~ᴹ (extractˣ⁻ᵘ kk′~) (extractˣ⁻ᵘ k″k‴~) ~L
-- --   --   rewrite sym (extractˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~)                    = `bang ~L′
-- -- ~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`let-bang ~L `in ~M)                      = `let-bang (~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ ~L) `in (~ᴹ⇒++ˣ⁻~ᴹ (!∷ᵘ kk′~) k″k‴~ ~M)
-- -- ~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`#¹ u<)
-- --   rewrite <⇒idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~ u< (ℕ.m≤n⇒m≤n+o _ u<) = `#¹ (ℕ.m≤n⇒m≤n+o _ u<)
-- -- ~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`λ⦂ S~ ∘ ~L)                              = `λ⦂ S~ ∘ ~ᴹ⇒++ˣ⁻~ᴹ (? !∷ˡ kk′~) k″k‴~ ~L
-- -- ~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (~L `$ ~M)                                 = ~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ ~L `$ ~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ ~M
-- -- ~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`#⁰ x<)
-- --   rewrite <⇒idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ kk′~ k″k‴~ x< (ℕ.m≤n⇒m≤n+o _ x<) = `#⁰ (ℕ.m≤n⇒m≤n+o _ x<)
-- -- ~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`unlift-`lift ~L) = {!!}
-- --   -- with ~L′ ← ~ᴹ⇒++ˣ⁻~ᴹ (extractˣ⁻ᵘ kk′~) (extractˣ⁻ᵘ k″k‴~) ~L
-- --   --   rewrite sym (extractˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~)                    = `unlift-`lift ~L′

-- -- Properties of _~ᴹ_ Regarding Typings
-- --
-- ≡∧~ᴹ∧++⊢⇒⊢ : {kk′~ : k ⍮ k′ ~ˣ⁻} →
--              k ≡ length ψ₁ →
--              k′ ≡ length ψ₀₀ →
--              (~L : kk′~ ⊢ I ~ᴹ L) →
--              ψ₁ BP.⍮ ψ₀₀ ++ ψ₀₁ ⊢ I ⦂ P →
--              --------------------------------------
--              ψ₁ BP.⍮ ψ₀₀ ⊢ I ⦂ P
-- ~ᴹ∧++⊢⇒⊢ : {kk′~ : length ψ₁ ⍮ length ψ₀₀ ~ˣ⁻} →
--            (~L : kk′~ ⊢ I ~ᴹ L) →
--            ψ₁ BP.⍮ ψ₀₀ ++ ψ₀₁ ⊢ I ⦂ P →
--            --------------------------------------
--            ψ₁ BP.⍮ ψ₀₀ ⊢ I ⦂ P

-- ≡∧~ᴹ∧++⊢⇒⊢ refl refl = ~ᴹ∧++⊢⇒⊢

-- ~ᴹ∧++⊢⇒⊢           (`unit kk′~Dis)              (BP.`unit ψ₀₀ψ₀₁Dis)              = BP.`unit (All.++⁻ˡ _ ψ₀₀ψ₀₁Dis)
-- ~ᴹ∧++⊢⇒⊢           (`bang kk′~Dis ~L)           (ψ₀₀ψ₀₁Dis BP.⊢`bang ⊢I)          = All.++⁻ˡ _ ψ₀₀ψ₀₁Dis BP.⊢`bang ~ᴹ∧++⊢⇒⊢ ~L ⊢I
-- ~ᴹ∧++⊢⇒⊢ {_} {ψ₀₀} (kk′~~ ⊢`let-bang ~L `in ~M) (ψ₀₀ψ₀₁~ BP.⊢`let-bang ⊢I `in ⊢J)
--   with _ , _ , _ , _ , refl , refl , ψ₀₀~ , _ ← BP.~⊞-preserves-++ ψ₀₀ ψ₀₀ψ₀₁~    = ψ₀₀~ BP.⊢`let-bang ≡∧~ᴹ∧++⊢⇒⊢ refl (sym (proj₁ (BP.length-respects-~⊞ ψ₀₀~))) ~L ⊢I `in ≡∧~ᴹ∧++⊢⇒⊢ refl (sym (proj₂ (BP.length-respects-~⊞ ψ₀₀~))) ~M ⊢J
-- ~ᴹ∧++⊢⇒⊢           (`#¹ u<)                     (ψ₀₀ψ₀₁Dis BP.⊢`#¹ u∈)            = All.++⁻ˡ _ ψ₀₀ψ₀₁Dis BP.⊢`#¹ u∈
-- ~ᴹ∧++⊢⇒⊢           (`λ⦂ ~S ∘ ~L)                (BP.`λ⦂-∘ ⊢I)                     = BP.`λ⦂-∘ (~ᴹ∧++⊢⇒⊢ ~L ⊢I)
-- ~ᴹ∧++⊢⇒⊢ {_} {ψ₀₀} (kk′~~ ⊢ ~L `$ ~M)           (ψ₀₀ψ₀₁~ BP.⊢ ⊢I `$ ⊢J)
--   with _ , _ , _ , _ , refl , refl , ψ₀₀~ , _ ← BP.~⊞-preserves-++ ψ₀₀ ψ₀₀ψ₀₁~    = ψ₀₀~ BP.⊢ ≡∧~ᴹ∧++⊢⇒⊢ refl (sym (proj₁ (BP.length-respects-~⊞ ψ₀₀~))) ~L ⊢I `$ ≡∧~ᴹ∧++⊢⇒⊢ refl (sym (proj₂ (BP.length-respects-~⊞ ψ₀₀~))) ~M ⊢J
-- ~ᴹ∧++⊢⇒⊢           (`#⁰ x<)                     (BP.`#⁰ x∈)                       = BP.`#⁰ BP.>∈⁰-++⇒∈⁰ _ x< x∈
-- ~ᴹ∧++⊢⇒⊢           (`unlift-`lift kk′~Dis ~L)   ⊢I                                = ~ᴹ∧++⊢⇒⊢ ~L ⊢I

~~ˣ⁻⊞-index : ∀ {kk′~ : k ⍮ k′ ~ˣ⁻} {kk′~₀ : k₀ ⍮ k₁ ~ˣ⁻} {kk′~₁ : k₂ ⍮ k₃ ~ˣ⁻} →
              kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
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
           !∷ᵘ (subst (k ⍮_~ˣ⁻) eq kn~) ≡ subst (suc k ⍮_~ˣ⁻) eq (!∷ᵘ kn~)
!∷ᵘsubst _ refl = refl

!∷ˡsubst : ∀ {n m} (kn~ : k ⍮ n ~ˣ⁻) (eq : n ≡ m) →
           !∷ˡ (subst (k ⍮_~ˣ⁻) eq kn~) ≡ subst (k ⍮_~ˣ⁻) (cong suc eq) (!∷ˡ kn~)
!∷ˡsubst _ refl = refl

?∷ˡsubst : ∀ {n m} (kn~ : k ⍮ n ~ˣ⁻) (eq : n ≡ m) →
           ?∷ˡ (subst (k ⍮_~ˣ⁻) eq kn~) ≡ subst (k ⍮_~ˣ⁻) (cong suc eq) (?∷ˡ kn~)
?∷ˡsubst _ refl = refl

subst⊢~ᴹʳ : ∀ {n m kk′~} →
               (n≡m : n ≡ m) →
               subst (k ⍮_~ˣ⁻) n≡m kk′~ ⊢ I ~ᴹ L →
               kk′~ ⊢ I ~ᴹ L
subst⊢~ᴹʳ refl ~L = ~L

subst⊢~ᴹʳ-depth : ∀ {n m kk′~} →
                     (n≡m : n ≡ m) →
                     (~L : subst (k ⍮_~ˣ⁻) n≡m kk′~ ⊢ I ~ᴹ L) →
                     depth~ᴹ ~L ≡ depth~ᴹ (subst⊢~ᴹʳ n≡m ~L)
subst⊢~ᴹʳ-depth refl _ = refl

~~ˣ⁻subst⊞ʳ : ∀ {n m} {kk′~ : k ⍮ k′ ~ˣ⁻} {kk′~₀ : k₀ ⍮ n ~ˣ⁻} {kk′~₁ : k₂ ⍮ k₃ ~ˣ⁻} →
              (n≡m : n ≡ m) →
              kk′~ ~~ˣ⁻ subst (k₀ ⍮_~ˣ⁻) n≡m kk′~₀ ⊞ kk′~₁ →
              kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁
~~ˣ⁻subst⊞ʳ refl kk′~~ = kk′~~

~~ˣ⁻subst⊞ʳ⁻¹ : ∀ {n m} {kk′~ : k ⍮ k′ ~ˣ⁻} {kk′~₀ : k₀ ⍮ n ~ˣ⁻} {kk′~₁ : k₂ ⍮ k₃ ~ˣ⁻} →
                (n≡m : n ≡ m) →
                kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                kk′~ ~~ˣ⁻ subst (k₀ ⍮_~ˣ⁻) n≡m kk′~₀ ⊞ kk′~₁
~~ˣ⁻subst⊞ʳ⁻¹ refl kk′~~ = kk′~~

~~ˣ⁻⊞substʳ : ∀ {n m} {kk′~ : k ⍮ k′ ~ˣ⁻} {kk′~₀ : k₀ ⍮ k₁ ~ˣ⁻} {kk′~₁ : k₂ ⍮ n ~ˣ⁻} →
              (n≡m : n ≡ m) →
              kk′~ ~~ˣ⁻ kk′~₀ ⊞ subst (k₂ ⍮_~ˣ⁻) n≡m kk′~₁ →
              kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁
~~ˣ⁻⊞substʳ refl kk′~~ = kk′~~

subst~~ˣ⁻⊞ʳ⁻¹ : ∀ {n m} {kk′~ : k ⍮ n ~ˣ⁻} {kk′~₀ : k₀ ⍮ k₁ ~ˣ⁻} {kk′~₁ : k₂ ⍮ k₃ ~ˣ⁻} →
                (n≡m : n ≡ m) →
                kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                subst (k ⍮_~ˣ⁻) n≡m kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁
subst~~ˣ⁻⊞ʳ⁻¹ refl kk′~~ = kk′~~

subst~FVofʳ⁻¹ : ∀ {n m} {kk′~ : k ⍮ n ~ˣ⁻} →
                (n≡m : n ≡ m) →
                kk′~ ~FVof L →
                subst (k ⍮_~ˣ⁻) n≡m kk′~ ~FVof L
subst~FVofʳ⁻¹ refl FVL = FVL

~ˣ-cancelˡ-~⊞ : (ψ₀~ : ψ₀ BP.~ ψ₀₀ ⊞ ψ₀₁) →
                (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
                (~Γ₀ : ψ₁ ⍮ ψ₀₀ ~ˣ Γ₀) →
                eraseˣ ~Γ ~~ˣ⁻ eraseˣ ~Γ₀ ⊞ kk′~₁ →
                ∃ (λ Γ₁ → Γ ~ Γ₀ ⊞ Γ₁ × Σ (ψ₁ ⍮ ψ₀₁ ~ˣ Γ₁) (λ ~Γ₁ → kk′~₁ ≡ subst (length ψ₁ ⍮_~ˣ⁻) (proj₂ (BP.length-respects-~⊞ ψ₀~)) (eraseˣ ~Γ₁)))
~ˣ-cancelˡ-~⊞ BP.[] [] [] [] = -, [] , [] , refl
~ˣ-cancelˡ-~⊞ ψ₀~                    (~S !∷ᵘ ~Γ) (~S′ !∷ᵘ ~Γ₀) (!∷ᵘ kk′~~)
  with _ , Γ~ , ~Γ₁ , refl ← ~ˣ-cancelˡ-~⊞ ψ₀~ ~Γ ~Γ₀ kk′~~
     | refl ← ~ᵀ-det ~S ~S′ = -, contraction _ ∷ Γ~ , ~S !∷ᵘ ~Γ₁ , !∷ᵘsubst (eraseˣ ~Γ₁) (proj₂ (BP.length-respects-~⊞ ψ₀~))
~ˣ-cancelˡ-~⊞ (BP.unusable BP.∷ ψ₀~) (~S ?∷ˡ ~Γ) (~S′ ?∷ˡ ~Γ₀) (?∷ˡ kk′~~)
  with _ , Γ~ , ~Γ₁ , refl ← ~ˣ-cancelˡ-~⊞ ψ₀~ ~Γ ~Γ₀ kk′~~
     | refl ← ~ᵀ-det ~S ~S′ = -, unusable ∷ Γ~ , ~S ?∷ˡ ~Γ₁ , ?∷ˡsubst (eraseˣ ~Γ₁) (proj₂ (BP.length-respects-~⊞ ψ₀~))
~ˣ-cancelˡ-~⊞ (BP.to-right BP.∷ ψ₀~) (~S !∷ˡ ~Γ) (~S′ ?∷ˡ ~Γ₀) (to-right!∷ˡ kk′~~)
  with _ , Γ~ , ~Γ₁ , refl ← ~ˣ-cancelˡ-~⊞ ψ₀~ ~Γ ~Γ₀ kk′~~
     | refl ← ~ᵀ-det ~S ~S′ = -, to-right ∷ Γ~ , ~S !∷ˡ ~Γ₁ , !∷ˡsubst (eraseˣ ~Γ₁) (proj₂ (BP.length-respects-~⊞ ψ₀~))
~ˣ-cancelˡ-~⊞ (BP.to-left  BP.∷ ψ₀~) (~S !∷ˡ ~Γ) (~S′ !∷ˡ ~Γ₀) (to-left!∷ˡ kk′~~)
  with _ , Γ~ , ~Γ₁ , refl ← ~ˣ-cancelˡ-~⊞ ψ₀~ ~Γ ~Γ₀ kk′~~
     | refl ← ~ᵀ-det ~S ~S′ = -, to-left ∷ Γ~ , ~S ?∷ˡ ~Γ₁ , ?∷ˡsubst (eraseˣ ~Γ₁) (proj₂ (BP.length-respects-~⊞ ψ₀~))

~d⊞-contract-is-del : d [ m ]~d d₀ ⊞ d₁ →
                      d′ [ m ]~d d₀ ⊞ d₂ →
                      d″ [ m ]~d d₁ ⊞ d₃ →
                      d₂ [ m ]is-del →
                      d₃ [ m ]is-del →
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
                         ∃₂ (λ Γ‴ Δ → Γ‴ ~ Γ′ ⊞ Γ″ × Γ‴ ~ Γ ⊞ Δ × Δ ~ Γ₂ ⊞ Γ₃)
~⊞-contract-is-all-del []        []          []          []              []              = -, -, [] , [] , []
~⊞-contract-is-all-del (d~ ∷ Γ~) (d′~ ∷ Γ′~) (d″~ ∷ Γ″~) (d₂Del ∷ Γ₂Del) (d₃Del ∷ Γ₃Del)
  with _ , _ , d‴~ , d‴~′ , dS~ ← ~d⊞-contract-is-del d~ d′~ d″~ d₂Del d₃Del
     | _ , _ , Γ‴~ , Γ‴~′ , Δ~ ← ~⊞-contract-is-all-del Γ~ Γ′~ Γ″~ Γ₂Del Γ₃Del = -, -, d‴~ ∷ Γ‴~ , d‴~′ ∷ Γ‴~′ , dS~ ∷ Δ~

~⊞-preserves-~ˣ : Γ ~ Γ₀ ⊞ Γ₁ →
                  (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
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
~⊞-preserves-~ˣ []                   []          = -, -, -, -, -, -, [] , [] , [] , [] , [] , BP.[] , [] , [] , []
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

-- ~⊞⁻¹-preserves-~ˣ : Γ ~ Γ₀ ⊞ Γ₁ →
--                     (~Γ₀ : ψ₁ ⍮ ψ₀₀ ~ˣ Γ₀) →
--                     (~Γ₁ : ψ₁ ⍮ ψ₀₁ ~ˣ Γ₁) →
--                     ∃ (λ ψ₀ → ψ₀ BP.~ ψ₀₀ ⊞ ψ₀₁ × Σ (ψ₁ ⍮ ψ₀ ~ˣ Γ) (λ ~Γ → eraseˣ ~Γ ~~ˣ⁻ eraseˣ ~Γ₀ ⊞ eraseˣ ~Γ₁))
-- ~⊞⁻¹-preserves-~ˣ []                    []           []            = -, BP.[] , [] , []
-- ~⊞⁻¹-preserves-~ˣ (contraction _  ∷ Γ~) (~S !∷ᵘ ~Γ₀) (~S′ !∷ᵘ ~Γ₁)
--   with _ , ψ₀~ , ~Γ , kk′~~ ← ~⊞⁻¹-preserves-~ˣ Γ~ ~Γ₀ ~Γ₁         = -, ψ₀~ , ~S !∷ᵘ ~Γ , !∷ᵘ kk′~~
-- ~⊞⁻¹-preserves-~ˣ (unusable       ∷ Γ~) (~S ?∷ˡ ~Γ₀) (~S′ ?∷ˡ ~Γ₁)
--   with _ , ψ₀~ , ~Γ , kk′~~ ← ~⊞⁻¹-preserves-~ˣ Γ~ ~Γ₀ ~Γ₁
--      | refl ← ~ᵀ-inj ~S ~S′                                      = -, BP.unusable BP.∷ ψ₀~ , ~S ?∷ˡ ~Γ , ?∷ˡ kk′~~
-- ~⊞⁻¹-preserves-~ˣ (to-right       ∷ Γ~) (~S ?∷ˡ ~Γ₀) (~S′ !∷ˡ ~Γ₁)
--   with _ , ψ₀~ , ~Γ , kk′~~ ← ~⊞⁻¹-preserves-~ˣ Γ~ ~Γ₀ ~Γ₁
--      | refl ← ~ᵀ-inj ~S ~S′                                      = -, BP.to-right BP.∷ ψ₀~ , ~S !∷ˡ ~Γ , to-right!∷ˡ kk′~~
-- ~⊞⁻¹-preserves-~ˣ (to-left        ∷ Γ~) (~S !∷ˡ ~Γ₀) (~S′ ?∷ˡ ~Γ₁)
--   with _ , ψ₀~ , ~Γ , kk′~~ ← ~⊞⁻¹-preserves-~ˣ Γ~ ~Γ₀ ~Γ₁
--      | refl ← ~ᵀ-inj ~S ~S′                                      = -, BP.to-left BP.∷ ψ₀~ , ~S !∷ˡ ~Γ , to-left!∷ˡ kk′~~
-- ~⊞⁻¹-preserves-~ˣ (contraction () ∷ Γ~) (~S !∷ˡ ~Γ₀) (~S′ !∷ˡ ~Γ₁)

BP~⊞-preserves-~ˣ : ψ₀ BP.~ ψ₀₀ ⊞ ψ₀₁ →
                    (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
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
              kk′~ ≡ kk′~′
~~ˣ⁻⊞⁻¹-det []                  []                   = refl
~~ˣ⁻⊞⁻¹-det (!∷ᵘ         kk′~~) (!∷ᵘ         kk′~′~) = cong !∷ᵘ_ (~~ˣ⁻⊞⁻¹-det kk′~~ kk′~′~)
~~ˣ⁻⊞⁻¹-det (?∷ˡ         kk′~~) (?∷ˡ         kk′~′~) = cong ?∷ˡ_ (~~ˣ⁻⊞⁻¹-det kk′~~ kk′~′~)
~~ˣ⁻⊞⁻¹-det (to-left!∷ˡ  kk′~~) (to-left!∷ˡ  kk′~′~) = cong !∷ˡ_ (~~ˣ⁻⊞⁻¹-det kk′~~ kk′~′~)
~~ˣ⁻⊞⁻¹-det (to-right!∷ˡ kk′~~) (to-right!∷ˡ kk′~′~) = cong !∷ˡ_ (~~ˣ⁻⊞⁻¹-det kk′~~ kk′~′~)

~ᴹ∧∈ᵘ⇒~ᵀ : ψ₁ ⍮ ψ₀ ~ˣ Γ →
           u ⦂[ uMode ] `↑ S ∈ Γ →
           ∃ (λ P → P ~ᵀ S)
~ᴹ∧∈ᵘ⇒~ᵀ (~S ?∷ˡ ~Γ) (there unusable      u∈) = ~ᴹ∧∈ᵘ⇒~ᵀ ~Γ u∈
~ᴹ∧∈ᵘ⇒~ᵀ (~S !∷ᵘ ~Γ) (here ΓDel)              = -, ~S
~ᴹ∧∈ᵘ⇒~ᵀ (~S !∷ᵘ ~Γ) (there (weakening _) u∈) = ~ᴹ∧∈ᵘ⇒~ᵀ ~Γ u∈

~ᴹ∧∈ˡ⇒~ᵀ : ψ₁ ⍮ ψ₀ ~ˣ Γ →
           u ⦂[ lMode ] S ∈ Γ →
           ∃ (λ P → P ~ᵀ S)
~ᴹ∧∈ˡ⇒~ᵀ (~S ?∷ˡ ~Γ) (there unusable       x∈) = ~ᴹ∧∈ˡ⇒~ᵀ ~Γ x∈
~ᴹ∧∈ˡ⇒~ᵀ (~S !∷ˡ ~Γ) (here ΓDel)               = -, ~S
~ᴹ∧∈ˡ⇒~ᵀ (~S !∷ˡ ~Γ) (there (weakening ()) x∈)
~ᴹ∧∈ˡ⇒~ᵀ (~S !∷ᵘ ~Γ) (there (weakening _)  x∈) = ~ᴹ∧∈ˡ⇒~ᵀ ~Γ x∈

~ᴹ∧⊢⇒~ᵀ : ψ₁ ⍮ ψ₀ ~ˣ Γ →
          kk′~ ⊢ I ~ᴹ L →
          Γ ⊢[ lMode ] L ⦂ S →
          ∃ (λ P → P ~ᵀ S)
~ᴹ∧⊢⇒~ᵀ ~Γ (`unit _) (`unit _) = -, `⊤
~ᴹ∧⊢⇒~ᵀ ~Γ (`bang _ ~L) (Γ∤ ⊢`return`lift ⊢L)
  with refl ← ~ˣ∧∤⇒≡ ~Γ Γ∤
    with _ , ~S ← ~ᴹ∧⊢⇒~ᵀ ~Γ ~L ⊢L = -, `! ~S
~ᴹ∧⊢⇒~ᵀ ~Γ (_ ⊢`let-bang ~L `in ~M) (Γ~ ⊢`let-return ⊢L ⦂ ⊢↓ `in ⊢M)
  with _ , _ , _ , _ , _ , _ , Γ~′ , Γ₀′~ , Γ₀″Del , Γ₁′~ , Γ₁″Del , ψ₀~ , ~Γ₀′ , ~Γ₁′ , kk′~~ ← ~⊞-preserves-~ˣ Γ~ ~Γ
    with _ , `! ~T ← ~ᴹ∧⊢⇒~ᵀ ~Γ₀′ ~L (~⊞-is-all-del∧⊢⇒⊢ˡ Γ₀′~ Γ₀″Del ⊢L) = ~ᴹ∧⊢⇒~ᵀ (~T !∷ᵘ ~Γ₁′) ~M (~⊞-is-all-del∧⊢⇒⊢ˡ (contraction _ ∷ Γ₁′~) (weakening _ ∷ Γ₁″Del) ⊢M)
~ᴹ∧⊢⇒~ᵀ ~Γ (`#¹ u∈) (Γ∤ ⊢`unlift`# u∈′ ⦂ ⊢↑)
  with refl ← ~ˣ∧∤⇒≡ ~Γ Γ∤ = ~ᴹ∧∈ᵘ⇒~ᵀ ~Γ u∈′
~ᴹ∧⊢⇒~ᵀ ~Γ (`λ⦂ ~S ∘ ~L) (`λ⦂-∘ ⊢L)
  with _ , ~T ← ~ᴹ∧⊢⇒~ᵀ (~S !∷ˡ ~Γ) ~L ⊢L = -, ~S `⊸ ~T
~ᴹ∧⊢⇒~ᵀ ~Γ (_ ⊢ ~L `$ ~M) (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with _ , _ , _ , _ , _ , _ , Γ~′ , Γ₀′~ , Γ₀″Del , Γ₁′~ , Γ₁″Del , ψ₀~ , ~Γ₀′ , ~Γ₁′ , kk′~~ ← ~⊞-preserves-~ˣ Γ~ ~Γ
    with _ , _ `⊸ ~S ← ~ᴹ∧⊢⇒~ᵀ ~Γ₀′ ~L (~⊞-is-all-del∧⊢⇒⊢ˡ Γ₀′~ Γ₀″Del ⊢L) = -, ~S
~ᴹ∧⊢⇒~ᵀ ~Γ (`#⁰ x∈) (`# x∈′) = ~ᴹ∧∈ˡ⇒~ᵀ ~Γ x∈′
~ᴹ∧⊢⇒~ᵀ ~Γ (`unlift-`lift _ ~L) (Γ∤ ⊢`unlift`lift ⊢L ⦂ ⊢↑)
  with refl ← ~ˣ∧∤⇒≡ ~Γ Γ∤ = ~ᴹ∧⊢⇒~ᵀ ~Γ ~L ⊢L

~ˣ∧∈ᵘ⇒~ᵛ∈ᵘ : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
             u ⦂[ uMode ] `↑ S ∈ Γ →
             ∃ (λ u′ → u′ ~ᵛ u ∈ᵘ eraseˣ ~Γ)
~ˣ∧∈ᵘ⇒~ᵛ∈ᵘ (~S ?∷ˡ ~Γ) (there unusable      u∈)
  with _ , ~u ← ~ˣ∧∈ᵘ⇒~ᵛ∈ᵘ ~Γ u∈                = -, there?∷ˡ ~u
~ˣ∧∈ᵘ⇒~ᵛ∈ᵘ (~S !∷ᵘ ~Γ) (here ΓDel)              = -, here (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ (~ˣ∧is-all-del⇒is-all-dis ~Γ ΓDel))
~ˣ∧∈ᵘ⇒~ᵛ∈ᵘ (~S !∷ᵘ ~Γ) (there (weakening _) u∈)
  with _ , ~u ← ~ˣ∧∈ᵘ⇒~ᵛ∈ᵘ ~Γ u∈                = -, there!∷ᵘ ~u

~ˣ∧∈ˡ⇒~ᵛ∈ˡ : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
             x ⦂[ lMode ] S ∈ Γ →
             ∃ (λ x′ → x′ ~ᵛ x ∈ˡ eraseˣ ~Γ)
~ˣ∧∈ˡ⇒~ᵛ∈ˡ (~S ?∷ˡ ~Γ) (there unusable       x∈)
  with _ , ~x ← ~ˣ∧∈ˡ⇒~ᵛ∈ˡ ~Γ x∈                 = -, there?∷ˡ ~x
~ˣ∧∈ˡ⇒~ᵛ∈ˡ (~S !∷ˡ ~Γ) (here ΓDel)               = -, here (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ (~ˣ∧is-all-del⇒is-all-dis ~Γ ΓDel))
~ˣ∧∈ˡ⇒~ᵛ∈ˡ (~S !∷ˡ ~Γ) (there (weakening ()) x∈)
~ˣ∧∈ˡ⇒~ᵛ∈ˡ (~S !∷ᵘ ~Γ) (there (weakening _)  x∈)
  with _ , ~x ← ~ˣ∧∈ˡ⇒~ᵛ∈ˡ ~Γ x∈                 = -, there!∷ᵘ ~x

⊢⇒~FVof : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
          kk′~ ⊢ I ~ᴹ L →
          Γ ⊢[ lMode ] L ⦂ S →
          eraseˣ ~Γ ~FVof L
⊢⇒~FVof ~Γ (`unit _) (`unit ΓDel) = FV`unit (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ (~ˣ∧is-all-del⇒is-all-dis ~Γ ΓDel))
⊢⇒~FVof ~Γ (`bang _ ~L) (Γ∤ ⊢`return`lift ⊢L)
  with kk′~Dis ← ~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ (~ˣ∧∤⇒is-all-dis ~Γ Γ∤)
    with refl ← ~ˣ∧∤⇒≡ ~Γ Γ∤ = FV`return (FV`lift (⊢⇒~FVof ~Γ ~L ⊢L))
⊢⇒~FVof ~Γ (_ ⊢`let-bang ~L `in ~M) (Γ~ ⊢`let-return ⊢L ⦂ ⊢↓ `in ⊢M)
  with _ , _ , _ , _ , _ , _ , Γ~′ , Γ₀′~ , Γ₀″Del , Γ₁′~ , Γ₁″Del , ψ₀~ , ~Γ₀′ , ~Γ₁′ , kk′~~ ← ~⊞-preserves-~ˣ Γ~ ~Γ
    with ⊢L′ ← ~⊞-is-all-del∧⊢⇒⊢ˡ Γ₀′~ Γ₀″Del ⊢L
      with _ , `! ~T ← ~ᴹ∧⊢⇒~ᵀ ~Γ₀′ ~L ⊢L′ = FV kk′~~ ⊢`let-return ⊢⇒~FVof ~Γ₀′ ~L ⊢L′ `in (⊢⇒~FVof (~T !∷ᵘ ~Γ₁′) ~M (~⊞-is-all-del∧⊢⇒⊢ˡ (contraction _ ∷ Γ₁′~) (weakening _ ∷ Γ₁″Del) ⊢M))
⊢⇒~FVof ~Γ (`#¹ u∈) (Γ∤ ⊢`unlift`# u∈′ ⦂ ⊢↑)
  with refl ← ~ˣ∧∤⇒≡ ~Γ Γ∤ = FV`unlift (FV`#¹ proj₂ (~ˣ∧∈ᵘ⇒~ᵛ∈ᵘ ~Γ u∈′))
⊢⇒~FVof ~Γ (`λ⦂ ~S ∘ ~L) (`λ⦂-∘ ⊢L) = FV`λ⦂-∘ (⊢⇒~FVof (~S !∷ˡ ~Γ) ~L ⊢L)
⊢⇒~FVof ~Γ (_ ⊢ ~L `$ ~M) (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with _ , _ , _ , _ , _ , _ , Γ~′ , Γ₀′~ , Γ₀″Del , Γ₁′~ , Γ₁″Del , ψ₀~ , ~Γ₀′ , ~Γ₁′ , kk′~~ ← ~⊞-preserves-~ˣ Γ~ ~Γ = FV kk′~~ ⊢ ⊢⇒~FVof ~Γ₀′ ~L (~⊞-is-all-del∧⊢⇒⊢ˡ Γ₀′~ Γ₀″Del ⊢L) `$ ⊢⇒~FVof ~Γ₁′ ~M (~⊞-is-all-del∧⊢⇒⊢ˡ Γ₁′~ Γ₁″Del ⊢M)
⊢⇒~FVof ~Γ (`#⁰ x∈) (`# x∈′) = FV`#⁰ proj₂ (~ˣ∧∈ˡ⇒~ᵛ∈ˡ ~Γ x∈′)
⊢⇒~FVof ~Γ (`unlift-`lift _ ~L) (Γ∤ ⊢`unlift`lift ⊢L ⦂ ⊢↑)
  with kk′~Dis ← ~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ (~ˣ∧∤⇒is-all-dis ~Γ Γ∤)
    with refl ← ~ˣ∧∤⇒≡ ~Γ Γ∤ = FV`unlift (FV`lift (⊢⇒~FVof ~Γ ~L ⊢L))

~ˣ∧∈¹⇒~ᵛ∈ᵘ : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
             ψ₀ BP.is-all-dis →
             u′ BP.⦂ P ∈¹ ψ₁ →
             ∃ (λ u → u′ ~ᵛ u ∈ᵘ eraseˣ ~Γ)
~ˣ∧∈¹⇒~ᵛ∈ᵘ (~S !∷ᵘ ~Γ) ψ₀Dis          BP.here        = -, here (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ ψ₀Dis)
~ˣ∧∈¹⇒~ᵛ∈ᵘ (~S !∷ᵘ ~Γ) ψ₀Dis          (BP.there u′∈) = -, there!∷ᵘ (proj₂ (~ˣ∧∈¹⇒~ᵛ∈ᵘ ~Γ ψ₀Dis u′∈))
~ˣ∧∈¹⇒~ᵛ∈ᵘ (~S ?∷ˡ ~Γ) (refl ∷ ψ₀Dis) u′∈
  with _ , ~u ← ~ˣ∧∈¹⇒~ᵛ∈ᵘ ~Γ ψ₀Dis u′∈              = -, there?∷ˡ ~u
~ˣ∧∈¹⇒~ᵛ∈ᵘ (~S !∷ˡ ~Γ) (()   ∷ ψ₀Dis) u′∈

~ˣ∧∈⁰⇒~ᵛ∈ˡ : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
             x′ BP.⦂ P ∈⁰ ψ₀ →
             ∃ (λ x → x′ ~ᵛ x ∈ˡ eraseˣ ~Γ)
~ˣ∧∈⁰⇒~ᵛ∈ˡ (~S !∷ᵘ ~Γ) x′∈             = -, there!∷ᵘ (proj₂ (~ˣ∧∈⁰⇒~ᵛ∈ˡ ~Γ x′∈))
~ˣ∧∈⁰⇒~ᵛ∈ˡ (~S ?∷ˡ ~Γ) (BP.there x′∈)
  with _ , ~x ← ~ˣ∧∈⁰⇒~ᵛ∈ˡ ~Γ x′∈      = -, there?∷ˡ ~x
~ˣ∧∈⁰⇒~ᵛ∈ˡ (~S !∷ˡ ~Γ) (BP.here ψ₀Dis) = -, here (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ ψ₀Dis)

~ᴹ⇒~FVof : kk′~ ⊢ I ~ᴹ L →
           kk′~ ~FVof L
~ᴹ⇒~FVof (`unit kk′~Dis) = FV`unit kk′~Dis
~ᴹ⇒~FVof (`bang kk′~Dis ~L) = FV`return (FV`lift (~ᴹ⇒~FVof ~L))
~ᴹ⇒~FVof (kk′~~ ⊢`let-bang ~L `in ~M) = FV kk′~~ ⊢`let-return ~ᴹ⇒~FVof ~L `in ~ᴹ⇒~FVof ~M
~ᴹ⇒~FVof (`#¹ u∈) = FV`unlift (FV`#¹ u∈)
~ᴹ⇒~FVof (`λ⦂ ~S ∘ ~L) = FV`λ⦂-∘ ~ᴹ⇒~FVof ~L
~ᴹ⇒~FVof (kk′~~ ⊢ ~L `$ ~M) = FV kk′~~ ⊢ ~ᴹ⇒~FVof ~L `$ ~ᴹ⇒~FVof ~M
~ᴹ⇒~FVof (`#⁰ x∈) = FV`#⁰ x∈
~ᴹ⇒~FVof (`unlift-`lift kk′~Dis ~L) = FV`unlift (FV`lift (~ᴹ⇒~FVof ~L))

~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
                              kk′~ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
                              kk′~₀ is-all-dis⁰~ˣ⁻ →
                              kk′~₂ is-all-dis⁰~ˣ⁻ →
                              kk′~₀ ≡ kk′~₂
~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique []                  []                   []             []             = refl
~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique (!∷ᵘ kk′~~)         (!∷ᵘ kk′~~′)         (!∷ᵘ kk′~₀Dis) (!∷ᵘ kk′~₂Dis) = cong !∷ᵘ_ (~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique kk′~~ kk′~~′ kk′~₀Dis kk′~₂Dis)
~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique (?∷ˡ kk′~~)         (?∷ˡ kk′~~′)         (?∷ˡ kk′~₀Dis) (?∷ˡ kk′~₂Dis) = cong ?∷ˡ_ (~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique kk′~~ kk′~~′ kk′~₀Dis kk′~₂Dis)
~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique (to-right!∷ˡ kk′~~) (to-right!∷ˡ kk′~~′) (?∷ˡ kk′~₀Dis) (?∷ˡ kk′~₂Dis) = cong ?∷ˡ_ (~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique kk′~~ kk′~~′ kk′~₀Dis kk′~₂Dis)

~ᵛ∈ᵘ-uniqueʳ : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
               kk′~ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
               u₀ ~ᵛ u ∈ᵘ kk′~₀ →
               u₂ ~ᵛ u ∈ᵘ kk′~₂ →
               kk′~₀ ≡ kk′~₂
~ᵛ∈ᵘ-uniqueʳ (!∷ᵘ kk′~~)         (!∷ᵘ kk′~~′)         (here kk′~₀Dis) (here kk′~₂Dis) = cong !∷ᵘ_ (~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique kk′~~ kk′~~′ kk′~₀Dis kk′~₂Dis)
~ᵛ∈ᵘ-uniqueʳ (!∷ᵘ kk′~~)         (!∷ᵘ kk′~~′)         (there!∷ᵘ ~u)   (there!∷ᵘ ~u′)  = cong !∷ᵘ_ (~ᵛ∈ᵘ-uniqueʳ kk′~~ kk′~~′ ~u ~u′)
~ᵛ∈ᵘ-uniqueʳ (?∷ˡ kk′~~)         (?∷ˡ kk′~~′)         (there?∷ˡ ~u)   (there?∷ˡ ~u′)  = cong ?∷ˡ_ (~ᵛ∈ᵘ-uniqueʳ kk′~~ kk′~~′ ~u ~u′)
~ᵛ∈ᵘ-uniqueʳ (to-right!∷ˡ kk′~~) (to-right!∷ˡ kk′~~′) (there?∷ˡ ~u)   (there?∷ˡ ~u′)  = cong ?∷ˡ_ (~ᵛ∈ᵘ-uniqueʳ kk′~~ kk′~~′ ~u ~u′)

~ᵛ∈ᵘ-uniqueˡ : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
               kk′~ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
               u ~ᵛ u₀ ∈ᵘ kk′~₀ →
               u ~ᵛ u₂ ∈ᵘ kk′~₂ →
               kk′~₀ ≡ kk′~₂
~ᵛ∈ᵘ-uniqueˡ (!∷ᵘ kk′~~)         (!∷ᵘ kk′~~′)         (here kk′~₀Dis) (here kk′~₂Dis) = cong !∷ᵘ_ (~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique kk′~~ kk′~~′ kk′~₀Dis kk′~₂Dis)
~ᵛ∈ᵘ-uniqueˡ (!∷ᵘ kk′~~)         (!∷ᵘ kk′~~′)         (there!∷ᵘ ~u)   (there!∷ᵘ ~u′)  = cong !∷ᵘ_ (~ᵛ∈ᵘ-uniqueˡ kk′~~ kk′~~′ ~u ~u′)
~ᵛ∈ᵘ-uniqueˡ (?∷ˡ kk′~~)         (?∷ˡ kk′~~′)         (there?∷ˡ ~u)   (there?∷ˡ ~u′)  = cong ?∷ˡ_ (~ᵛ∈ᵘ-uniqueˡ kk′~~ kk′~~′ ~u ~u′)
~ᵛ∈ᵘ-uniqueˡ (to-right!∷ˡ kk′~~) (to-right!∷ˡ kk′~~′) (there?∷ˡ ~u)   (there?∷ˡ ~u′)  = cong ?∷ˡ_ (~ᵛ∈ᵘ-uniqueˡ kk′~~ kk′~~′ ~u ~u′)

~ᵛ∈ˡ-uniqueʳ : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
               kk′~ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
               x₀ ~ᵛ x ∈ˡ kk′~₀ →
               x₂ ~ᵛ x ∈ˡ kk′~₂ →
               kk′~₀ ≡ kk′~₂
~ᵛ∈ˡ-uniqueʳ (!∷ᵘ kk′~~)         (!∷ᵘ kk′~~′)         (there!∷ᵘ ~x)   (there!∷ᵘ ~x′)  = cong !∷ᵘ_ (~ᵛ∈ˡ-uniqueʳ kk′~~ kk′~~′ ~x ~x′)
~ᵛ∈ˡ-uniqueʳ (?∷ˡ kk′~~)         (?∷ˡ kk′~~′)         (there?∷ˡ ~x)   (there?∷ˡ ~x′)  = cong ?∷ˡ_ (~ᵛ∈ˡ-uniqueʳ kk′~~ kk′~~′ ~x ~x′)
~ᵛ∈ˡ-uniqueʳ (to-left!∷ˡ kk′~~)  (to-left!∷ˡ kk′~~′)  (here kk′~₀Dis) (here kk′~₂Dis) = cong !∷ˡ_ (~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique kk′~~ kk′~~′ kk′~₀Dis kk′~₂Dis)
~ᵛ∈ˡ-uniqueʳ (to-right!∷ˡ kk′~~) (to-right!∷ˡ kk′~~′) (there?∷ˡ ~x)   (there?∷ˡ ~x′)  = cong ?∷ˡ_ (~ᵛ∈ˡ-uniqueʳ kk′~~ kk′~~′ ~x ~x′)

~ᵛ∈ˡ-uniqueˡ : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
               kk′~ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
               x ~ᵛ x₀ ∈ˡ kk′~₀ →
               x ~ᵛ x₂ ∈ˡ kk′~₂ →
               kk′~₀ ≡ kk′~₂
~ᵛ∈ˡ-uniqueˡ (!∷ᵘ kk′~~)         (!∷ᵘ kk′~~′)         (there!∷ᵘ ~x)   (there!∷ᵘ ~x′)  = cong !∷ᵘ_ (~ᵛ∈ˡ-uniqueˡ kk′~~ kk′~~′ ~x ~x′)
~ᵛ∈ˡ-uniqueˡ (?∷ˡ kk′~~)         (?∷ˡ kk′~~′)         (there?∷ˡ ~x)   (there?∷ˡ ~x′)  = cong ?∷ˡ_ (~ᵛ∈ˡ-uniqueˡ kk′~~ kk′~~′ ~x ~x′)
~ᵛ∈ˡ-uniqueˡ (to-left!∷ˡ kk′~~)  (to-left!∷ˡ kk′~~′)  (here kk′~₀Dis) (here kk′~₂Dis) = cong !∷ˡ_ (~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique kk′~~ kk′~~′ kk′~₀Dis kk′~₂Dis)
~ᵛ∈ˡ-uniqueˡ (to-right!∷ˡ kk′~~) (to-right!∷ˡ kk′~~′) (there?∷ˡ ~x)   (there?∷ˡ ~x′)  = cong ?∷ˡ_ (~ᵛ∈ˡ-uniqueˡ kk′~~ kk′~~′ ~x ~x′)

~ᵛ∈ᵘ∧~ᵛ∈ˡ⇒⊥ : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
              kk′~ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
              u₀ ~ᵛ u ∈ᵘ kk′~₀ →
              x₂ ~ᵛ u ∈ˡ kk′~₂ →
              ⊥
~ᵛ∈ᵘ∧~ᵛ∈ˡ⇒⊥ (!∷ᵘ kk′~~)         (!∷ᵘ kk′~~′)         (there!∷ᵘ ~u) (there!∷ᵘ ~u′) = ~ᵛ∈ᵘ∧~ᵛ∈ˡ⇒⊥ kk′~~ kk′~~′ ~u ~u′
~ᵛ∈ᵘ∧~ᵛ∈ˡ⇒⊥ (?∷ˡ kk′~~)         (?∷ˡ kk′~~′)         (there?∷ˡ ~u) (there?∷ˡ ~u′) = ~ᵛ∈ᵘ∧~ᵛ∈ˡ⇒⊥ kk′~~ kk′~~′ ~u ~u′
~ᵛ∈ᵘ∧~ᵛ∈ˡ⇒⊥ (to-right!∷ˡ kk′~~) (to-right!∷ˡ kk′~~′) (there?∷ˡ ~u) (there?∷ˡ ~u′) = ~ᵛ∈ᵘ∧~ᵛ∈ˡ⇒⊥ kk′~~ kk′~~′ ~u ~u′

~FVof-unique : kk′~ ~~ˣ⁻ kk′~₀ ⊞ kk′~₁ →
               kk′~ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
               kk′~₀ ~FVof L →
               kk′~₂ ~FVof L →
               kk′~₀ ≡ kk′~₂
~FVof-unique kk′~~ kk′~~′ (FV`unit kk′~₀Dis) (FV`unit kk′~₂Dis) = ~~ˣ⁻⊞-is-all-dis⁰~ˣ⁻-unique kk′~~ kk′~~′ kk′~₀Dis kk′~₂Dis
~FVof-unique kk′~~ kk′~~′ (FV`lift FVL) (FV`lift FVL′) = ~FVof-unique kk′~~ kk′~~′ FVL FVL′
~FVof-unique kk′~~ kk′~~′ (FV`unlift FVL) (FV`unlift FVL′) = ~FVof-unique kk′~~ kk′~~′ FVL FVL′
~FVof-unique kk′~~ kk′~~′ (FV`return FVL) (FV`return FVL′) = ~FVof-unique kk′~~ kk′~~′ FVL FVL′
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
         | refl ← ~FVof-unique (!∷ᵘ kk′~~₄) (!∷ᵘ kk′~~₆) FVM FVM′ = ~~ˣ⁻⊞⁻¹-det kk′~₀~ kk′~₂~
~FVof-unique kk′~~ kk′~~′ (FV`#¹ ~u) (FV`#¹ ~u′) = ~ᵛ∈ᵘ-uniqueʳ kk′~~ kk′~~′ ~u ~u′
~FVof-unique kk′~~ kk′~~′ (FV`#¹ ~u) (FV`#⁰ ~x) with () ← ~ᵛ∈ᵘ∧~ᵛ∈ˡ⇒⊥ kk′~~ kk′~~′ ~u ~x
~FVof-unique kk′~~ kk′~~′ (FV`λ⦂-∘ FVL) (FV`λ⦂-∘ FVL′) = !∷ˡ-inj (~FVof-unique (to-left!∷ˡ kk′~~) (to-left!∷ˡ kk′~~′) FVL FVL′)
~FVof-unique kk′~~ kk′~~′ (FV kk′~₀~ ⊢ FVL `$ FVM) (FV kk′~₂~ ⊢ FVL′ `$ FVM′)
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
~FVof-unique kk′~~ kk′~~′ (FV`#⁰ ~x) (FV`#¹ ~u) with () ← ~ᵛ∈ᵘ∧~ᵛ∈ˡ⇒⊥ kk′~~′ kk′~~ ~u ~x
~FVof-unique kk′~~ kk′~~′ (FV`#⁰ ~x) (FV`#⁰ ~x′) = ~ᵛ∈ˡ-uniqueʳ kk′~~ kk′~~′ ~x ~x′

BP⊢⇒~FVof : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
            kk′~ ~~ˣ⁻ eraseˣ ~Γ ⊞ kk′~₁ →
            kk′~ ~~ˣ⁻ kk′~₂ ⊞ kk′~₃ →
            kk′~₂ ⊢ I ~ᴹ L →
            ψ₁ BP.⍮ ψ₀ ⊢ I ⦂ P →
            eraseˣ ~Γ ~FVof L
BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ (`unit _) (BP.`unit ψ₀Dis) = FV`unit (~ˣ∧is-all-dis⇒is-all-dis⁰~ˣ⁻ ~Γ ψ₀Dis)
BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ (`bang _ ~L) (ψ₀Dis BP.⊢`bang ⊢I) = FV`return (FV`lift (BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ ~L ⊢I))
BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ (kk′~₂~ ⊢`let-bang ~L `in ~M) (ψ₀~ BP.⊢`let-bang ⊢I `in ⊢J)
  with _ , _ , Γ~ , ~Γ₀ , ~Γ₁ , kk′~′~ ← BP~⊞-preserves-~ˣ ψ₀~ ~Γ
    with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~′
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~₂~
       | refl , refl , _ , _ ← ~~ˣ⁻⊞-index kk′~′~
      with _ , kk′~Γ₁′~ , kk′~~₀ ← ~~ˣ⁻⊞-assocˡ kk′~~ kk′~′~
         | _ , kk′~₃′~ , kk′~~₀′ ← ~~ˣ⁻⊞-assocˡ kk′~~′ kk′~₂~
         | _ , kk′~Γ₀′~ , kk′~~₁ ← ~~ˣ⁻⊞-assocˡ kk′~~ (~~ˣ⁻⊞-commute kk′~′~)
         | _ , kk′~₂′~ , kk′~~₁′ ← ~~ˣ⁻⊞-assocˡ kk′~~′ (~~ˣ⁻⊞-commute kk′~₂~) = FV kk′~′~ ⊢`let-return BP⊢⇒~FVof ~Γ₀ kk′~~₀ kk′~~₀′ ~L ⊢I `in BP⊢⇒~FVof (proj₂ (~ᵀ-total _) !∷ᵘ ~Γ₁) (!∷ᵘ kk′~~₁) (!∷ᵘ kk′~~₁′) ~M ⊢J
BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ (`#¹ ~u) (ψ₀Dis BP.⊢`#¹ u∈)
  with _ , ~u′ ← ~ˣ∧∈¹⇒~ᵛ∈ᵘ ~Γ ψ₀Dis u∈
    with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~′
      with refl ← ~ᵛ∈ᵘ-uniqueˡ kk′~~′ kk′~~ ~u ~u′ = FV`unlift (FV`#¹ ~u)
BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ (`λ⦂ ~S ∘ ~L) (BP.`λ⦂-∘ ⊢I) = FV`λ⦂-∘ BP⊢⇒~FVof (~S !∷ˡ ~Γ) (to-left!∷ˡ kk′~~) (to-left!∷ˡ kk′~~′) ~L ⊢I
BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ (kk′~₂~ ⊢ ~L `$ ~M) (ψ₀~ BP.⊢ ⊢I `$ ⊢J)
  with _ , _ , Γ~ , ~Γ₀ , ~Γ₁ , kk′~′~ ← BP~⊞-preserves-~ˣ ψ₀~ ~Γ
    with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~′
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~₂~
       | refl , refl , _ , _ ← ~~ˣ⁻⊞-index kk′~′~
      with _ , kk′~Γ₁′~ , kk′~~₀ ← ~~ˣ⁻⊞-assocˡ kk′~~ kk′~′~
         | _ , kk′~₃′~ , kk′~~₀′ ← ~~ˣ⁻⊞-assocˡ kk′~~′ kk′~₂~
         | _ , kk′~Γ₀′~ , kk′~~₁ ← ~~ˣ⁻⊞-assocˡ kk′~~ (~~ˣ⁻⊞-commute kk′~′~)
         | _ , kk′~₂′~ , kk′~~₁′ ← ~~ˣ⁻⊞-assocˡ kk′~~′ (~~ˣ⁻⊞-commute kk′~₂~) = FV kk′~′~ ⊢ BP⊢⇒~FVof ~Γ₀ kk′~~₀ kk′~~₀′ ~L ⊢I `$ BP⊢⇒~FVof ~Γ₁ kk′~~₁ kk′~~₁′ ~M ⊢J
BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ (`#⁰ ~x) (BP.`#⁰ x∈)
  with _ , ~x′ ← ~ˣ∧∈⁰⇒~ᵛ∈ˡ ~Γ x∈
    with refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~′
      with refl ← ~ᵛ∈ˡ-uniqueˡ kk′~~′ kk′~~ ~x ~x′ = FV`#⁰ ~x
BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ (`unlift-`lift _ ~L) ⊢I = FV`unlift (FV`lift (BP⊢⇒~FVof ~Γ kk′~~ kk′~~′ ~L ⊢I))

-- Soundness and Completeness of _~ᴹ_ Regarding Typings
--
~ᴹ-soundness-∈ᵘ : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
                  P ~ᵀ S →
                  u′ ~ᵛ u ∈ᵘ eraseˣ ~Γ →
                  u′ BP.⦂ P ∈¹ ψ₁ →
                  u ⦂[ uMode ] `↑ S ∈ Γ
~ᴹ-soundness-∈ᵘ (~S′ !∷ᵘ ~Γ) ~S (here kk′~Dis) BP.here
  with refl ← ~ᵀ-det ~S′ ~S                                   = here (~ˣ∧is-all-dis⇒is-all-del ~Γ (~ˣ∧is-all-dis⁰~ˣ⁻⇒is-all-dis ~Γ kk′~Dis))
~ᴹ-soundness-∈ᵘ (~S′ !∷ᵘ ~Γ) ~S (there!∷ᵘ ~u)  (BP.there u′∈) = there (weakening _) (~ᴹ-soundness-∈ᵘ ~Γ ~S ~u u′∈)
~ᴹ-soundness-∈ᵘ (~S′ ?∷ˡ ~Γ) ~S (there?∷ˡ ~u)  u′∈            = there unusable (~ᴹ-soundness-∈ᵘ ~Γ ~S ~u u′∈)

~ᴹ-soundness-∈ˡ : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
                  P ~ᵀ S →
                  x′ ~ᵛ x ∈ˡ eraseˣ ~Γ →
                  x′ BP.⦂ P ∈⁰ ψ₀ →
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
       | FVL ← BP⊢⇒~FVof ~Γ₀ kk′~′~ kk′~~ ~L ⊢I
       | FVM ← BP⊢⇒~FVof (~T !∷ᵘ ~Γ₁) (!∷ᵘ (~~ˣ⁻⊞-commute kk′~′~)) (!∷ᵘ (~~ˣ⁻⊞-commute kk′~~)) ~M ⊢J
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
       | FVL ← BP⊢⇒~FVof ~Γ₀ kk′~′~ kk′~~ ~L ⊢I
       | FVM ← BP⊢⇒~FVof ~Γ₁ (~~ˣ⁻⊞-commute kk′~′~) (~~ˣ⁻⊞-commute kk′~~) ~M ⊢J
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
                     u′ BP.⦂ P ∈¹ ψ₁
~ᴹ-completeness-∈ᵘ (~S′ !∷ᵘ ~Γ) ~S (here kk′~Dis) (here ΓDel)
  with refl ← ~ᵀ-inj ~S′ ~S                                                = BP.here
~ᴹ-completeness-∈ᵘ (~S′ !∷ᵘ ~Γ) ~S (there!∷ᵘ ~u)  (there (weakening _) u∈) = BP.there (~ᴹ-completeness-∈ᵘ ~Γ ~S ~u u∈)
~ᴹ-completeness-∈ᵘ (~S′ ?∷ˡ ~Γ) ~S (there?∷ˡ ~u)  (there unusable      u∈) = ~ᴹ-completeness-∈ᵘ ~Γ ~S ~u u∈

~ᴹ-completeness-∈ˡ : (~Γ : ψ₁ ⍮ ψ₀ ~ˣ Γ) →
                     P ~ᵀ S →
                     x′ ~ᵛ x ∈ˡ eraseˣ ~Γ →
                     x ⦂[ lMode ] S ∈ Γ →
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
        with FVL ← subst~FVofʳ⁻¹ eq₀₀ (⊢⇒~FVof ~Γ₀′ ~L ⊢L′)
           | FVM ← subst~FVofʳ⁻¹ eq₀₁ (⊢⇒~FVof (~T !∷ᵘ ~Γ₁′) ~M (~⊞-is-all-del∧⊢⇒⊢ˡ (contraction _ ∷ Γ₁′~) (weakening _ ∷ Γ₁″Del) ⊢M))
          with refl ← ~FVof-unique kk′~~ (~~ˣ⁻subst⊞ʳ⁻¹ eq₀₀ kk′~~′) (~ᴹ⇒~FVof ~L) FVL
             | refl ← trans
                        (~FVof-unique (!∷ᵘ (~~ˣ⁻⊞-commute kk′~~)) (~~ˣ⁻subst⊞ʳ⁻¹ eq₀₁ (~~ˣ⁻⊞-commute (!∷ᵘ kk′~~′))) (~ᴹ⇒~FVof ~M) FVM)
                        (sym (!∷ᵘsubst (eraseˣ ~Γ₁′) eq₀₁))                             = ψ₀~ BP.⊢`let-bang ⊢I `in ⊢J
  where
    ⊢I = ~ᴹ-completeness ~Γ₀′ (`! ~T) (subst⊢~ᴹʳ eq₀₀ ~L) (~⊞-is-all-del∧⊢⇒⊢ʳ (~⊞-commute Γ₀′~) Γ₀″Del ⊢L)
    ⊢J = ~ᴹ-completeness
           (~T !∷ᵘ ~Γ₁′)
           ~S
           (subst⊢~ᴹʳ eq₀₁ (subst (_⊢ _ ~ᴹ _) (!∷ᵘsubst (eraseˣ ~Γ₁′) eq₀₁) ~M))
           (~⊞-is-all-del∧⊢⇒⊢ʳ (contraction _ ∷ ~⊞-commute Γ₁′~) (weakening _ ∷ Γ₁″Del) ⊢M)
~ᴹ-completeness ~Γ ~S          (`#¹ ~u)              (Γ∤ ⊢`unlift`# u∈ ⦂ ⊢↑)
  with ψ₀Dis ← ~ˣ∧∤⇒is-all-dis ~Γ Γ∤
     | refl ← ~ˣ∧∤⇒≡ ~Γ Γ∤ = ψ₀Dis BP.⊢`#¹ ~ᴹ-completeness-∈ᵘ ~Γ ~S ~u u∈
~ᴹ-completeness ~Γ (~S′ `⊸ ~T) (`λ⦂ ~S ∘ ~L)         (`λ⦂-∘ ⊢L)
  with refl ← ~ᵀ-inj ~S ~S′                                                                   = BP.`λ⦂-∘ ~ᴹ-completeness (~S !∷ˡ ~Γ) ~T ~L ⊢L
~ᴹ-completeness ~Γ ~S          (kk′~~ ⊢ ~L `$ ~M)            (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with _ , _ , _ , _ , _ , _ , Γ~′ , Γ₀′~ , Γ₀″Del , Γ₁′~ , Γ₁″Del , ψ₀~ , ~Γ₀′ , ~Γ₁′ , kk′~~′ ← ~⊞-preserves-~ˣ Γ~ ~Γ
    with eq₀₀ , eq₀₁ ← BP.length-respects-~⊞ ψ₀~
       | refl , refl , refl , refl ← ~~ˣ⁻⊞-index kk′~~
       | refl , refl , _ , _ ← ~~ˣ⁻⊞-index kk′~~′
       | ⊢L′ ← ~⊞-is-all-del∧⊢⇒⊢ˡ Γ₀′~ Γ₀″Del ⊢L
      with _ , ~T `⊸ _ ← ~ᴹ∧⊢⇒~ᵀ ~Γ₀′ ~L ⊢L′
        with FVL ← subst~FVofʳ⁻¹ eq₀₀ (⊢⇒~FVof ~Γ₀′ ~L ⊢L′)
           | FVM ← subst~FVofʳ⁻¹ eq₀₁ (⊢⇒~FVof ~Γ₁′ ~M (~⊞-is-all-del∧⊢⇒⊢ˡ Γ₁′~ Γ₁″Del ⊢M))
          with refl ← ~FVof-unique kk′~~ (~~ˣ⁻subst⊞ʳ⁻¹ eq₀₀ kk′~~′) (~ᴹ⇒~FVof ~L) FVL
             | refl ← ~FVof-unique (~~ˣ⁻⊞-commute kk′~~) (~~ˣ⁻subst⊞ʳ⁻¹ eq₀₁ (~~ˣ⁻⊞-commute kk′~~′)) (~ᴹ⇒~FVof ~M) FVM = ψ₀~ BP.⊢ ⊢I `$ ⊢J
  where
    ⊢I = ~ᴹ-completeness ~Γ₀′ (~T `⊸ ~S) (subst⊢~ᴹʳ eq₀₀ ~L) (~⊞-is-all-del∧⊢⇒⊢ʳ (~⊞-commute Γ₀′~) Γ₀″Del ⊢L)
    ⊢J = ~ᴹ-completeness ~Γ₁′ ~T (subst⊢~ᴹʳ eq₀₁ ~M) (~⊞-is-all-del∧⊢⇒⊢ʳ (~⊞-commute Γ₁′~) Γ₁″Del ⊢M)
~ᴹ-completeness ~Γ ~S          (`#⁰ ~x)              (`# x∈)                                  = BP.`#⁰ ~ᴹ-completeness-∈ˡ ~Γ ~S ~x x∈
~ᴹ-completeness ~Γ ~S          (`unlift-`lift kk′~Dis ~L)    (Γ∤ ⊢`unlift`lift ⊢L ⦂ ⊢↑)
  with refl ← ~ˣ∧∤⇒≡ ~Γ Γ∤                                   = ~ᴹ-completeness ~Γ ~S ~L ⊢L
~ᴹ-completeness ~Γ `⊤          (`unit kk′~Dis)               (`unit ΓDel)                     = BP.`unit (~ˣ∧is-all-del⇒is-all-dis ~Γ ΓDel)
~ᴹ-completeness ~Γ (`! ~S)     (`bang kk′~Dis ~L)            (Γ∤ ⊢`return`lift ⊢L)
  with refl ← ~ˣ∧∤⇒≡ ~Γ Γ∤                                                                    = ~ˣ∧∤⇒is-all-dis ~Γ Γ∤ BP.⊢`bang ~ᴹ-completeness ~Γ ~S ~L ⊢L


-- -- -- Properties of _~ᴹ_ Regarding OpSems
-- -- --
-- -- ⟶[≤]-preserves-~ᴹ : kk′~ ⊢ I ~ᴹ L →
-- --                     L ⟶[ uMode ≤] L′ →
-- --                     -------------------
-- --                     kk′~ ⊢ I ~ᴹ L′
-- -- ⟶[≤]-preserves-~ᴹ (`bang ~L)            (ξ-`return[≰ ≰uMode ⇒-] L⟶[≤]) with () ← ≰uMode refl
-- -- ⟶[≤]-preserves-~ᴹ (`bang ~L)            (ξ-`return≤`lift L⟶[≤])        = `bang (⟶[≤]-preserves-~ᴹ ~L L⟶[≤])
-- -- ⟶[≤]-preserves-~ᴹ (`let-bang ~L `in ~M) ξ-`let-return L⟶[≤] `in?       = `let-bang (⟶[≤]-preserves-~ᴹ ~L L⟶[≤]) `in ~M
-- -- ⟶[≤]-preserves-~ᴹ (`let-bang ~L `in ~M) (ξ-`let-return! WL `in M⟶[≤])  = `let-bang ~L `in ⟶[≤]-preserves-~ᴹ ~M M⟶[≤]
-- -- ⟶[≤]-preserves-~ᴹ (`λ⦂ ~S ∘ ~L)        (ξ-`λ⦂[-]-∘ L⟶[≤])              = `λ⦂ ~S ∘ ⟶[≤]-preserves-~ᴹ ~L L⟶[≤]
-- -- ⟶[≤]-preserves-~ᴹ (~L `$ ~M)           ξ- L⟶[≤] `$?                    = ⟶[≤]-preserves-~ᴹ ~L L⟶[≤] `$ ~M
-- -- ⟶[≤]-preserves-~ᴹ (~L `$ ~M)           (ξ-! WL `$ M⟶[≤])               = ~L `$ ⟶[≤]-preserves-~ᴹ ~M M⟶[≤]
-- -- ⟶[≤]-preserves-~ᴹ (`#¹ u<)             (ξ-`unlift[≰ ≰uMode ⇒-] L⟶[≤])  with () ← ≰uMode refl
-- -- ⟶[≤]-preserves-~ᴹ (`#¹ u<)             (ξ-`unlift≤ ())
-- -- ⟶[≤]-preserves-~ᴹ (`unlift-`lift ~L)   (ξ-`unlift[≰ ≰uMode ⇒-] L⟶[≤])  with () ← ≰uMode refl
-- -- ⟶[≤]-preserves-~ᴹ (`unlift-`lift ~L)   (ξ-`unlift≤`lift L⟶[≤])         = `unlift-`lift (⟶[≤]-preserves-~ᴹ ~L L⟶[≤])
-- -- ⟶[≤]-preserves-~ᴹ (`unlift-`lift ~L)   (β-`↑ _ WL)                     = ?

-- -- []⊢~ᴹ⁻¹⇒¬Neut⁰ : [] ⊢ I ~ᴹ L →
-- --                  ---------------
-- --                  ¬ (WeakNeut L)
-- -- []⊢~ᴹ⁻¹⇒¬Neut⁰ (`unlift-`lift ~L)   (`unlift ())
-- -- []⊢~ᴹ⁻¹⇒¬Neut⁰ (`let-bang ~L `in ~M) (`let-return NL `in _) = []⊢~ᴹ⁻¹⇒¬Neut⁰ ~L NL
-- -- []⊢~ᴹ⁻¹⇒¬Neut⁰ (~L `$ ~M)           (NL `$ VM)             = []⊢~ᴹ⁻¹⇒¬Neut⁰ ~L NL

-- -- []⊢~ᴹ⁻¹-respects-Value : [] ⊢ I ~ᴹ L →
-- --                          WeakNorm L →
-- --                          --------------
-- --                          BP.Value I
-- -- []⊢~ᴹ⁻¹-respects-Value ~L            (`neut NL)        with () ← []⊢~ᴹ⁻¹⇒¬Neut⁰ ~L NL
-- -- []⊢~ᴹ⁻¹-respects-Value `unit         `unit             = BP.`unit
-- -- []⊢~ᴹ⁻¹-respects-Value (`bang ~L)    (`return`lift WL) = BP.`bang _
-- -- []⊢~ᴹ⁻¹-respects-Value (`λ⦂ ~S ∘ ~L) (`λ⦂ˡ S ∘ L)      = BP.`λ⦂ _ ∘ _

-- -- ~ᴹ-normalize[≤] : (~L : kk′~ ⊢ I ~ᴹ L) →
-- --                   --------------------------------------------------
-- --                   ∃ (λ L′ → L ⟶[ uMode ≤]* L′
-- --                           × DeferredTerm[ uMode ≤] L′
-- --                           × Σ (kk′~ ⊢ I ~ᴹ L′)
-- --                               (λ ~L′ → depth~ᴹ ~L′ ℕ.≤ depth~ᴹ ~L))
-- -- ~ᴹ-normalize[≤] `unit                                     = -, ε
-- --                                                           , `unit
-- --                                                           , `unit
-- --                                                           , z≤n
-- -- ~ᴹ-normalize[≤] (`bang ~L)
-- --   with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L = -, ξ-of-⟶[ uMode ≤]* `return`lift ξ-`return≤`lift ⟶*L′[≤]
-- --                                                           , `return≤ (`lift WL′)
-- --                                                           , `bang ~L′
-- --                                                           , s≤s L′≤
-- -- ~ᴹ-normalize[≤] (`let-bang ~L `in ~M)
-- --   with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
-- --      | _ , ⟶*M′[≤] , WM′ , ~M′ , M′≤ ← ~ᴹ-normalize[≤] ~M = -, ξ-of-⟶[ uMode ≤]* (`let-return_`in _) ξ-`let-return_`in? ⟶*L′[≤]
-- --                                                               ◅◅ ξ-of-⟶[ uMode ≤]* (`let-return _ `in_) (ξ-`let-return! WL′ `in_) ⟶*M′[≤]
-- --                                                           , `let-return WL′ `in WM′
-- --                                                           , `let-bang ~L′ `in ~M′
-- --                                                           , s≤s (ℕ.⊔-mono-≤ L′≤ M′≤)
-- -- ~ᴹ-normalize[≤] (`#¹ u<)                                  = -, ε
-- --                                                           , `unlift≤ (`neut (`# _))
-- --                                                           , `#¹ u<
-- --                                                           , z≤n
-- -- ~ᴹ-normalize[≤] (`λ⦂ ~S ∘ ~L)
-- --   with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L = -, ξ-of-⟶[ uMode ≤]* (`λ⦂ˡ _ ∘_) ξ-`λ⦂[-]-∘_ ⟶*L′[≤]
-- --                                                           , `λ⦂ˡ _ ∘ WL′
-- --                                                           , `λ⦂ ~S ∘ ~L′
-- --                                                           , s≤s L′≤
-- -- ~ᴹ-normalize[≤] (~L `$ ~M)
-- --   with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
-- --      | _ , ⟶*M′[≤] , WM′ , ~M′ , M′≤ ← ~ᴹ-normalize[≤] ~M = -, ξ-of-⟶[ uMode ≤]* (_`$ _) ξ-_`$? ⟶*L′[≤]
-- --                                                               ◅◅ ξ-of-⟶[ uMode ≤]* (_ `$_) (ξ-! WL′ `$_) ⟶*M′[≤]
-- --                                                           , WL′ `$ WM′
-- --                                                           , ~L′ `$ ~M′
-- --                                                           , s≤s (ℕ.⊔-mono-≤ L′≤ M′≤)
-- -- ~ᴹ-normalize[≤] (`#⁰ x<)                                  = -, ε
-- --                                                           , `# _
-- --                                                           , `#⁰ x<
-- --                                                           , z≤n
-- -- ~ᴹ-normalize[≤] (`unlift-`lift ~L)
-- --   with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L = -, ξ-of-⟶[ uMode ≤]* `unlift`lift ξ-`unlift≤`lift ⟶*L′[≤]
-- --                                                               ◅◅ β-`↑ refl WL′ ◅ ε
-- --                                                           , WL′
-- --                                                           , ?
-- --                                                           , ?

-- -- Value~ᴹ-normalize-helper : (~L : kk′~ ⊢ I ~ᴹ L) →
-- --                            BP.Value I →
-- --                            Acc ℕ._<_ (depth~ᴹ ~L) →
-- --                            --------------------------------------------------
-- --                            ∃ (λ L′ → L ⟶* L′ × WeakNorm L′ × kk′~ ⊢ I ~ᴹ L′)
-- -- Value~ᴹ-normalize-helper `unit              VI rec                              = -, ε , `unit , `unit
-- -- Value~ᴹ-normalize-helper (`bang ~L)          VI (acc r)
-- --   with _ , ⟶*L′[≤] , WL′ , ~L′ , _ ← ~ᴹ-normalize[≤] ~L                         = -, ξ-of-↝*-⟶* _⟶[ _ ≤]_ `return`lift ξ-`return`lift ⟶*L′[≤]
-- --                                                                                 , `return`lift WL′
-- --                                                                                 , `bang ~L′
-- -- Value~ᴹ-normalize-helper (`λ⦂ ~S ∘ ~L)      VI rec                              = -, ε , `λ⦂ˡ _ ∘ _ , `λ⦂ ~S ∘ ~L
-- -- Value~ᴹ-normalize-helper (`unlift-`lift ~L) VI (acc r)
-- --   with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
-- --     with _ , ⟶*L″ , VL″ , ~L″ ← Value~ᴹ-normalize-helper ~L′ VI (r _ (s≤s L′≤)) = -, ξ-of-↝*-⟶* _⟶[ uMode ≤]_ `unlift`lift ξ-`unlift`lift ⟶*L′[≤]
-- --                                                                                     ◅◅ β-`↑ WL′ ◅ ⟶*L″
-- --                                                                                 , VL″
-- --                                                                                 , ?

-- -- Value~ᴹ-normalize : kk′~ ⊢ I ~ᴹ L →
-- --                     BP.Value I →
-- --                     --------------------------------------------------
-- --                     ∃ (λ L′ → L ⟶* L′ × WeakNorm L′ × kk′~ ⊢ I ~ᴹ L′)
-- -- Value~ᴹ-normalize ~L VI = Value~ᴹ-normalize-helper ~L VI (ℕ.<-wellFounded _)

-- -- `bang-~ᴹ-inv-helper : (~L : kk′~ ⊢ BP.`bang I ~ᴹ L) →
-- --                      Acc ℕ._<_ (depth~ᴹ ~L) →
-- --                      ------------------------------------
-- --                      ∃ (λ L′ → L ⟶* `return`lift L′
-- --                              × DeferredTerm[ uMode ≤] L′
-- --                              × kk′~ ⊢ I ~ᴹ L′)
-- -- `bang-~ᴹ-inv-helper (`bang ~L)          rec
-- --   with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L                  = -, ξ-of-↝*-⟶* _⟶[ _ ≤]_ `return`lift ξ-`return`lift ⟶*L′[≤]
-- --                                                                            , WL′
-- --                                                                            , ?
-- -- `bang-~ᴹ-inv-helper (`unlift-`lift ~L) (acc r)
-- --   with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
-- --     with _ , ⟶*`bangL″ , WL″ , ~L″ ← `bang-~ᴹ-inv-helper ~L′ (r _ (s≤s L′≤)) = -, ξ-of-↝*-⟶* _⟶[ uMode ≤]_ `unlift`lift ξ-`unlift`lift ⟶*L′[≤]
-- --                                                                                ◅◅ β-`↑ WL′ ◅ ⟶*`bangL″
-- --                                                                            , WL″
-- --                                                                            , ?

-- -- `bang-~ᴹ-inv : kk′~ ⊢ BP.`bang I ~ᴹ L →
-- --               ------------------------------------
-- --               ∃ (λ L′ → L ⟶* `return`lift L′
-- --                       × DeferredTerm[ uMode ≤] L′
-- --                       × kk′~ ⊢ I ~ᴹ L′)
-- -- `bang-~ᴹ-inv ~L = `bang-~ᴹ-inv-helper ~L (ℕ.<-wellFounded _)

-- -- `λ⦂-∙-~ᴹ-inv-helper : (~L : kk′~ ⊢ BP.`λ⦂ P ∘ I ~ᴹ L) →
-- --                       Acc ℕ._<_ (depth~ᴹ ~L) →
-- --                       ----------------------------------
-- --                       ∃₂ (λ S′ L′ → L ⟶* `λ⦂ˡ S′ ∘ L′
-- --                                   × true !∷ˡ kk′~ ⊢ I ~ᴹ L′
-- --                                   × P ~ᵀ S′)
-- -- `λ⦂-∙-~ᴹ-inv-helper (`λ⦂ ~S ∘ ~L)      rec                                         = -, -, ε
-- --                                                                                    , ~L
-- --                                                                                    , ~S
-- -- `λ⦂-∙-~ᴹ-inv-helper (`unlift-`lift ~L) (acc r)
-- --   with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
-- --     with _ , _ , ⟶*`λ⦂ˡS″∘L″ , ~L″ , ~S″ ← `λ⦂-∙-~ᴹ-inv-helper ~L′ (r _ (s≤s L′≤)) = -, -, ξ-of-↝*-⟶* _⟶[ uMode ≤]_ `unlift`lift ξ-`unlift`lift ⟶*L′[≤]
-- --                                                                                        ◅◅ β-`↑ WL′ ◅ ⟶*`λ⦂ˡS″∘L″
-- --                                                                                    , ?
-- --                                                                                    , ~S″

-- -- `λ⦂-∙-~ᴹ-inv : kk′~ ⊢ BP.`λ⦂ P ∘ I ~ᴹ L →
-- --                ---------------------------------
-- --                ∃₂ (λ S′ L′ → L ⟶* `λ⦂ˡ S′ ∘ L′
-- --                            × true !∷ˡ kk′~ ⊢ I ~ᴹ L′
-- --                            × P ~ᵀ S′)
-- -- `λ⦂-∙-~ᴹ-inv ~L = `λ⦂-∙-~ᴹ-inv-helper ~L (ℕ.<-wellFounded _)

-- -- wkidx[↑]-idxˣ⁻ᵘ : (kk′~ : k ⍮ k′ ~ˣ⁻) (0k₀~ : 0 ⍮ k₀ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) →
-- --                   (u< : u ℕ.< k + k″) →
-- --                   -------------------------------------------------------------------------------------------------------------
-- --                   wkidx[ lengthˣ⁻ 0k₀~ ↑ lengthˣ⁻ kk′~ ] (idxˣ⁻ᵘ (kk′~ ++ˣ⁻ k″k‴~) u<) ≡ idxˣ⁻ᵘ (kk′~ ++ˣ⁻ 0k₀~ ++ˣ⁻ k″k‴~) u<
-- -- wkidx[↑]-idxˣ⁻ᵘ             []           0k₀~ k″k‴~ u<                                               = ≥⇒lengthˣ⁻+idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ 0k₀~ k″k‴~ z≤n u< u<
-- -- wkidx[↑]-idxˣ⁻ᵘ             (  ?∷ˡ kk′~) 0k₀~ k″k‴~ u<
-- --   rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~) (idxˣ⁻ᵘ (kk′~ ++ˣ⁻ k″k‴~) u<) = cong suc (wkidx[↑]-idxˣ⁻ᵘ kk′~ 0k₀~ k″k‴~ u<)
-- -- wkidx[↑]-idxˣ⁻ᵘ             (_ !∷ˡ kk′~) 0k₀~ k″k‴~ u<
-- --   rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~) (idxˣ⁻ᵘ (kk′~ ++ˣ⁻ k″k‴~) u<) = cong suc (wkidx[↑]-idxˣ⁻ᵘ kk′~ 0k₀~ k″k‴~ u<)
-- -- wkidx[↑]-idxˣ⁻ᵘ             (  ?∷ᵘ kk′~) 0k₀~ k″k‴~ u<
-- --   rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~) (idxˣ⁻ᵘ (kk′~ ++ˣ⁻ k″k‴~) u<) = cong suc (wkidx[↑]-idxˣ⁻ᵘ kk′~ 0k₀~ k″k‴~ u<)
-- -- wkidx[↑]-idxˣ⁻ᵘ {u = zero}  (  !∷ᵘ kk′~) 0k₀~ k″k‴~ (s≤s u<)                                         = refl
-- -- wkidx[↑]-idxˣ⁻ᵘ {u = suc u} (  !∷ᵘ kk′~) 0k₀~ k″k‴~ (s≤s u<)
-- --   rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~) (idxˣ⁻ᵘ (kk′~ ++ˣ⁻ k″k‴~) u<) = cong suc (wkidx[↑]-idxˣ⁻ᵘ kk′~ 0k₀~ k″k‴~ u<)

-- -- wkidx[↑]-idxˣ⁻ˡ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k₀0~ : k₀ ⍮ 0 ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) →
-- --                   (x< : x ℕ.< k′ + k‴) →
-- --                   -------------------------------------------------------------------------------------------------------------
-- --                   wkidx[ lengthˣ⁻ k₀0~ ↑ lengthˣ⁻ kk′~ ] (idxˣ⁻ˡ (kk′~ ++ˣ⁻ k″k‴~) x<) ≡ idxˣ⁻ˡ (kk′~ ++ˣ⁻ k₀0~ ++ˣ⁻ k″k‴~) x<
-- -- wkidx[↑]-idxˣ⁻ˡ             []           k₀0~ k″k‴~ x<                                               = ≥⇒lengthˣ⁻+idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ k₀0~ k″k‴~ z≤n x< x<
-- -- wkidx[↑]-idxˣ⁻ˡ             (  ?∷ᵘ kk′~) k₀0~ k″k‴~ x<
-- --   rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ k₀0~) (lengthˣ⁻ kk′~) (idxˣ⁻ˡ (kk′~ ++ˣ⁻ k″k‴~) x<) = cong suc (wkidx[↑]-idxˣ⁻ˡ kk′~ k₀0~ k″k‴~ x<)
-- -- wkidx[↑]-idxˣ⁻ˡ             (  !∷ᵘ kk′~) k₀0~ k″k‴~ x<
-- --   rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ k₀0~) (lengthˣ⁻ kk′~) (idxˣ⁻ˡ (kk′~ ++ˣ⁻ k″k‴~) x<) = cong suc (wkidx[↑]-idxˣ⁻ˡ kk′~ k₀0~ k″k‴~ x<)
-- -- wkidx[↑]-idxˣ⁻ˡ             (  ?∷ˡ kk′~) k₀0~ k″k‴~ x<
-- --   rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ k₀0~) (lengthˣ⁻ kk′~) (idxˣ⁻ˡ (kk′~ ++ˣ⁻ k″k‴~) x<) = cong suc (wkidx[↑]-idxˣ⁻ˡ kk′~ k₀0~ k″k‴~ x<)
-- -- wkidx[↑]-idxˣ⁻ˡ {x = zero}  (_ !∷ˡ kk′~) k₀0~ k″k‴~ (s≤s x<)                                         = refl
-- -- wkidx[↑]-idxˣ⁻ˡ {x = suc x} (_ !∷ˡ kk′~) k₀0~ k″k‴~ (s≤s x<)
-- --   rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ k₀0~) (lengthˣ⁻ kk′~) (idxˣ⁻ˡ (kk′~ ++ˣ⁻ k″k‴~) x<) = cong suc (wkidx[↑]-idxˣ⁻ˡ kk′~ k₀0~ k″k‴~ x<)

-- -- wk[0↑¹]≡ : ∀ u E →
-- --            ----------------------
-- --            BP.wk[ 0 ↑¹ u ] E ≡ E
-- -- wk[0↑¹]≡ u BP.`unit = refl
-- -- wk[0↑¹]≡ u (BP.`bang E) = cong BP.`bang (wk[0↑¹]≡ u E)
-- -- wk[0↑¹]≡ u (BP.`let-bang E `in F) = cong₂ BP.`let-bang_`in_ (wk[0↑¹]≡ u E) (wk[0↑¹]≡ (suc u) F)
-- -- wk[0↑¹]≡ u (BP.`λ⦂ S ∘ E) = cong (BP.`λ⦂ _ ∘_) (wk[0↑¹]≡ u E)
-- -- wk[0↑¹]≡ u (E BP.`$ F) = cong₂ BP._`$_ (wk[0↑¹]≡ u E) (wk[0↑¹]≡ u F)
-- -- wk[0↑¹]≡ u (BP.`#¹ v) = cong BP.`#¹_ (wkidx[0↑]≡ u v)
-- -- wk[0↑¹]≡ u (BP.`#⁰ y) = refl

-- -- wk[0↑⁰]≡ : ∀ x E →
-- --            ----------------------
-- --            BP.wk[ 0 ↑⁰ x ] E ≡ E
-- -- wk[0↑⁰]≡ x BP.`unit = refl
-- -- wk[0↑⁰]≡ x (BP.`bang E) = refl
-- -- wk[0↑⁰]≡ x (BP.`let-bang E `in F) = cong₂ BP.`let-bang_`in_ (wk[0↑⁰]≡ x E) (wk[0↑⁰]≡ x F)
-- -- wk[0↑⁰]≡ x (BP.`λ⦂ S ∘ E) = cong (BP.`λ⦂ _ ∘_) (wk[0↑⁰]≡ (suc x) E)
-- -- wk[0↑⁰]≡ x (E BP.`$ F) = cong₂ BP._`$_ (wk[0↑⁰]≡ x E) (wk[0↑⁰]≡ x F)
-- -- wk[0↑⁰]≡ x (BP.`#¹ v) = refl
-- -- wk[0↑⁰]≡ x (BP.`#⁰ y) = cong BP.`#⁰_ (wkidx[0↑]≡ x y)

-- -- ~ᴹ∧≥⇒wk[↑⁰]≡ : ∀ k₀ →
-- --                {kk′~ : k ⍮ k′ ~ˣ⁻} →
-- --                kk′~ ⊢ I ~ᴹ L →
-- --                x ℕ.≥ k′ →
-- --                -----------------------
-- --                BP.wk[ k₀ ↑⁰ x ] I ≡ I
-- -- ~ᴹ∧≥⇒wk[↑⁰]≡ _ `unit                 x≥                   = refl
-- -- ~ᴹ∧≥⇒wk[↑⁰]≡ _ (`bang ~M)            x≥                   = refl
-- -- ~ᴹ∧≥⇒wk[↑⁰]≡ _ (`let-bang ~M `in ~N) x≥                   = cong₂ BP.`let-bang_`in_ (~ᴹ∧≥⇒wk[↑⁰]≡ _ ~M x≥) (~ᴹ∧≥⇒wk[↑⁰]≡ _ ~N x≥)
-- -- ~ᴹ∧≥⇒wk[↑⁰]≡ _ (`#¹ u<)              x≥                   = refl
-- -- ~ᴹ∧≥⇒wk[↑⁰]≡ _ (`λ⦂ ~S ∘ ~M)         x≥                   = cong (BP.`λ⦂ _ ∘_) (~ᴹ∧≥⇒wk[↑⁰]≡ _ ~M (s≤s x≥))
-- -- ~ᴹ∧≥⇒wk[↑⁰]≡ _ (~M `$ ~N)            x≥                   = cong₂ BP._`$_ (~ᴹ∧≥⇒wk[↑⁰]≡ _ ~M x≥) (~ᴹ∧≥⇒wk[↑⁰]≡ _ ~N x≥)
-- -- ~ᴹ∧≥⇒wk[↑⁰]≡ _ (`#⁰ y<)              x≥
-- --   rewrite dec-no (_ ℕ.≤? _) (ℕ.<⇒≱ (ℕ.<-transˡ y< x≥)) = refl
-- -- ~ᴹ∧≥⇒wk[↑⁰]≡ _ (`unlift-`lift ~M)    x≥                   = ~ᴹ∧≥⇒wk[↑⁰]≡ _ ~M z≤n 

-- -- wk[↑¹]~ᴹwk[↑]ᶜ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k₀0~ : k₀ ⍮ 0 ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
-- --                  kk′~ ++ˣ⁻ k″k‴~ ⊢ I ~ᴹ L →
-- --                  ----------------------------------------------------------------------------------------
-- --                  kk′~ ++ˣ⁻ k₀0~ ++ˣ⁻ k″k‴~ ⊢ BP.wk[ k₀ ↑¹ k ] I ~ᴹ wk[ lengthˣ⁻ k₀0~ ↑ lengthˣ⁻ kk′~ ] L
-- -- wk[↑¹]~ᴹwk[↑]ᶜ {_} {0}  {_}  {_}  {0}  kk′~ k₀0~ {k″k‴~} (`unlift-`lift ~L) = ?
-- --   -- rewrite extractˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~
-- --   --   with ~L′ ← wk[↑¹]~ᴹwk[↑]ᶜ (extractˣ⁻ᵘ kk′~) (extractˣ⁻ᵘ k₀0~) ~L
-- --   --     rewrite sym (extractˣ⁻ᵘ-++ˣ⁻ k₀0~ k″k‴~)
-- --   --           | sym (extractˣ⁻ᵘ-++ˣ⁻ kk′~ (k₀0~ ++ˣ⁻ k″k‴~))
-- --   --           | lengthˣ⁻-extractˣ⁻ᵘ kk′~
-- --   --           | lengthˣ⁻-extractˣ⁻ᵘ k₀0~                                                                   = `unlift-`lift ~L′
-- -- wk[↑¹]~ᴹwk[↑]ᶜ {_} {0}  {_}  {_}  {0}  kk′~ k₀0~ {k″k‴~} (`bang ~L) = ?
-- --   -- rewrite extractˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~
-- --   --   with ~L′ ← wk[↑¹]~ᴹwk[↑]ᶜ (extractˣ⁻ᵘ kk′~) (extractˣ⁻ᵘ k₀0~) ~L
-- --   --     rewrite sym (extractˣ⁻ᵘ-++ˣ⁻ k₀0~ k″k‴~)
-- --   --           | sym (extractˣ⁻ᵘ-++ˣ⁻ kk′~ (k₀0~ ++ˣ⁻ k″k‴~))
-- --   --           | lengthˣ⁻-extractˣ⁻ᵘ kk′~
-- --   --           | lengthˣ⁻-extractˣ⁻ᵘ k₀0~                                                                   = `bang ~L′
-- -- wk[↑¹]~ᴹwk[↑]ᶜ                        kk′~ k₀0~         `unit                                                = `unit
-- -- wk[↑¹]~ᴹwk[↑]ᶜ                    kk′~ k₀0~         (`let-bang ~L `in ~M)                                 = `let-bang wk[↑¹]~ᴹwk[↑]ᶜ kk′~ k₀0~ ~L `in wk[↑¹]~ᴹwk[↑]ᶜ (!∷ᵘ kk′~) k₀0~ ~M
-- -- wk[↑¹]~ᴹwk[↑]ᶜ {k} {_}  {k₀} {k″} kk′~ k₀0~ {k″k‴~} (`#¹_ {u = u} u<)
-- --   with u ℕ.≥? k
-- -- ...  | no  u≱k
-- --     with u<k ← ℕ.≰⇒> u≱k
-- --       rewrite sym (<⇒idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~ u<k u<)
-- --             | dec-no (_ ℕ.≤? _) (ℕ.<⇒≱ (idxˣ⁻ᵘ<lengthˣ⁻ kk′~ u<k))
-- --             | <⇒idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ kk′~ (k₀0~ ++ˣ⁻ k″k‴~) u<k (ℕ.<-transˡ u<k (ℕ.m≤m+n _ _))             = `#¹ ℕ.<-transˡ u<k (ℕ.m≤m+n _ _)
-- -- ...  | yes u≥k
-- --     with u∸k< ← subst (u ∸ k ℕ.<_) (ℕ.m+n∸m≡n k _) (ℕ.∸-monoˡ-< u< u≥k)
-- --        | k₀+u< ← ℕ.+-monoʳ-< k₀ u<
-- --        | k₀+u∸keq ← sym (ℕ.+-∸-assoc k₀ u≥k)
-- --        | k₀+[u∸k]∸k₀eq ← sym (ℕ.m+n∸m≡n k₀ (u ∸ k))
-- --       with k₀+[u∸k]< ← ℕ.+-monoʳ-< k₀ u∸k<
-- --          | k₀+[u∸k]-k₀< ← subst (ℕ._< k″) k₀+[u∸k]∸k₀eq u∸k<
-- --         with k₀+u∸k< ← subst (ℕ._< k₀ + k″) k₀+u∸keq k₀+[u∸k]<
-- --           rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~ u≥k u< u∸k<)
-- --                 | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ᵘ k″k‴~ u∸k<)))
-- --                 | sym (ℕ.+-assoc (lengthˣ⁻ k₀0~) (lengthˣ⁻ kk′~) (idxˣ⁻ᵘ k″k‴~ u∸k<))
-- --                 | sym (ℕ.+-assoc k₀ k k″)
-- --                 | ℕ.+-comm (lengthˣ⁻ k₀0~) (lengthˣ⁻ kk′~)
-- --                 | ℕ.+-comm k₀ k
-- --                 | ℕ.+-assoc (lengthˣ⁻ kk′~) (lengthˣ⁻ k₀0~) (idxˣ⁻ᵘ k″k‴~ u∸k<)
-- --                 | ℕ.+-assoc k k₀ k″
-- --                 | idxˣ⁻ᵘ-<-irrelevant′ k″k‴~ u∸k< k₀+[u∸k]-k₀< k₀+[u∸k]∸k₀eq
-- --                 | ≥⇒lengthˣ⁻+idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ k₀0~ k″k‴~ (ℕ.m≤m+n _ _) k₀+[u∸k]< k₀+[u∸k]-k₀<
-- --                 | idxˣ⁻ᵘ-<-irrelevant′ (k₀0~ ++ˣ⁻ k″k‴~) k₀+[u∸k]< k₀+u∸k< k₀+u∸keq
-- --                 | ≥⇒lengthˣ⁻+idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ kk′~ (k₀0~ ++ˣ⁻ k″k‴~) (ℕ.m≤n⇒m≤o+n _ u≥k) k₀+u< k₀+u∸k< = `#¹ k₀+u<
-- -- wk[↑¹]~ᴹwk[↑]ᶜ {k} {k′}           kk′~ k₀0~         (`λ⦂ ~S ∘ ~L)
-- --   with ~L′ ← wk[↑¹]~ᴹwk[↑]ᶜ (true !∷ˡ kk′~) k₀0~ ~L
-- --     rewrite ℕ.+-suc k k′                                                                                 = `λ⦂ ~S ∘ ~L′
-- -- wk[↑¹]~ᴹwk[↑]ᶜ                    kk′~ k₀0~         (~L `$ ~M)                                           = wk[↑¹]~ᴹwk[↑]ᶜ kk′~ k₀0~ ~L `$ wk[↑¹]~ᴹwk[↑]ᶜ kk′~ k₀0~ ~M
-- -- wk[↑¹]~ᴹwk[↑]ᶜ                    kk′~ k₀0~ {k″k‴~} (`#⁰ x<)
-- --   rewrite wkidx[↑]-idxˣ⁻ˡ kk′~ k₀0~ k″k‴~ x<                                                             = `#⁰ x<

-- -- wk[↑⁰]~ᴹwk[↑]ᵖ : (kk′~ : k ⍮ k′ ~ˣ⁻) (0k₀~ : 0 ⍮ k₀ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
-- --                  kk′~ ++ˣ⁻ k″k‴~ ⊢ I ~ᴹ L →
-- --                  -----------------------------------------------------------------------------------------
-- --                  kk′~ ++ˣ⁻ 0k₀~ ++ˣ⁻ k″k‴~ ⊢ BP.wk[ k₀ ↑⁰ k′ ] I ~ᴹ wk[ lengthˣ⁻ 0k₀~ ↑ lengthˣ⁻ kk′~ ] L
-- -- wk[↑⁰]~ᴹwk[↑]ᵖ {_} {0}  {_}  {_}  {0}  kk′~ 0k₀~ {k″k‴~} (`bang {I = I} ~L) = ?
-- --   -- rewrite extractˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~
-- --   --   with ~L′ ← wk[↑¹]~ᴹwk[↑]ᶜ (extractˣ⁻ᵘ kk′~) (extractˣ⁻ᵘ 0k₀~) ~L
-- --   --     rewrite wk[0↑¹]≡ k I
-- --   --           | sym (extractˣ⁻ᵘ-++ˣ⁻ 0k₀~ k″k‴~)
-- --   --           | sym (extractˣ⁻ᵘ-++ˣ⁻ kk′~ (0k₀~ ++ˣ⁻ k″k‴~))
-- --   --           | lengthˣ⁻-extractˣ⁻ᵘ kk′~
-- --   --           | lengthˣ⁻-extractˣ⁻ᵘ 0k₀~                                                                    = `bang ~L′
-- -- wk[↑⁰]~ᴹwk[↑]ᵖ {k} {0}  {k₀} {_}  {0}  kk′~ 0k₀~ {k″k‴~} (`unlift-`lift {I = I} ~L) = ?
-- --   -- rewrite extractˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~
-- --   --   with ~L′ ← wk[↑¹]~ᴹwk[↑]ᶜ (extractˣ⁻ᵘ kk′~) (extractˣ⁻ᵘ 0k₀~) ~L
-- --   --     rewrite wk[0↑¹]≡ k I
-- --   --           | sym (extractˣ⁻ᵘ-++ˣ⁻ 0k₀~ k″k‴~)
-- --   --           | sym (extractˣ⁻ᵘ-++ˣ⁻ kk′~ (0k₀~ ++ˣ⁻ k″k‴~))
-- --   --           | lengthˣ⁻-extractˣ⁻ᵘ kk′~
-- --   --           | lengthˣ⁻-extractˣ⁻ᵘ 0k₀~
-- --   --           | ~ᴹ∧≥⇒wk[↑⁰]≡ k₀ ~L (z≤n {k′})                                                                = `unlift-`lift ~L′
-- -- wk[↑⁰]~ᴹwk[↑]ᵖ                         kk′~ 0k₀~         `unit                                            = `unit
-- -- wk[↑⁰]~ᴹwk[↑]ᵖ                         kk′~ 0k₀~         (`let-bang ~L `in ~M)                             = `let-bang wk[↑⁰]~ᴹwk[↑]ᵖ kk′~ 0k₀~ ~L `in wk[↑⁰]~ᴹwk[↑]ᵖ (!∷ᵘ kk′~) 0k₀~ ~M
-- -- wk[↑⁰]~ᴹwk[↑]ᵖ                         kk′~ 0k₀~ {k″k‴~} (`#¹ u<)
-- --   rewrite wkidx[↑]-idxˣ⁻ᵘ kk′~ 0k₀~ k″k‴~ u<                                                              = `#¹ u<
-- -- wk[↑⁰]~ᴹwk[↑]ᵖ {k} {k′}                kk′~ 0k₀~         (`λ⦂ ~S ∘ ~L)
-- --   with ~L′ ← wk[↑⁰]~ᴹwk[↑]ᵖ (true !∷ˡ kk′~) 0k₀~ ~L
-- --     rewrite ℕ.+-suc k k′                                                                                  = `λ⦂ ~S ∘ ~L′
-- -- wk[↑⁰]~ᴹwk[↑]ᵖ                         kk′~ 0k₀~         (~L `$ ~M)                                       = wk[↑⁰]~ᴹwk[↑]ᵖ kk′~ 0k₀~ ~L `$ wk[↑⁰]~ᴹwk[↑]ᵖ kk′~ 0k₀~ ~M
-- -- wk[↑⁰]~ᴹwk[↑]ᵖ {_} {k′} {k₀} {_}  {k‴} kk′~ 0k₀~ {k″k‴~} (`#⁰_ {x = x} x<)
-- --   with x ℕ.≥? k′
-- -- ...  | no  x≱k′
-- --     with x<k′ ← ℕ.≰⇒> x≱k′
-- --       rewrite sym (<⇒idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ kk′~ k″k‴~ x<k′ x<)
-- --             | dec-no (_ ℕ.≤? _) (ℕ.<⇒≱ (idxˣ⁻ˡ<lengthˣ⁻ kk′~ x<k′))
-- --             | <⇒idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ kk′~ (0k₀~ ++ˣ⁻ k″k‴~) x<k′ (ℕ.<-transˡ x<k′ (ℕ.m≤m+n _ _))            = `#⁰ ℕ.<-transˡ x<k′ (ℕ.m≤m+n _ _)
-- -- ...  | yes x≥k′
-- --     with x∸k′< ← subst (x ∸ k′ ℕ.<_) (ℕ.m+n∸m≡n k′ _) (ℕ.∸-monoˡ-< x< x≥k′)
-- --        | k₀+x< ← ℕ.+-monoʳ-< k₀ x<
-- --        | k₀+x∸k′eq ← sym (ℕ.+-∸-assoc k₀ x≥k′)
-- --        | k₀+[x∸k′]∸k₀eq ← sym (ℕ.m+n∸m≡n k₀ (x ∸ k′))
-- --       with k₀+[x∸k′]< ← ℕ.+-monoʳ-< k₀ x∸k′<
-- --          | k₀+[x∸k′]-k₀< ← subst (ℕ._< k‴) k₀+[x∸k′]∸k₀eq x∸k′<
-- --         with k₀+x∸k′< ← subst (ℕ._< k₀ + k‴) k₀+x∸k′eq k₀+[x∸k′]<
-- --           rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ kk′~ k″k‴~ x≥k′ x< x∸k′<)
-- --                 | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ˡ k″k‴~ x∸k′<)))
-- --                 | sym (ℕ.+-assoc (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~) (idxˣ⁻ˡ k″k‴~ x∸k′<))
-- --                 | sym (ℕ.+-assoc k₀ k′ k‴)
-- --                 | ℕ.+-comm (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~)
-- --                 | ℕ.+-comm k₀ k′
-- --                 | ℕ.+-assoc (lengthˣ⁻ kk′~) (lengthˣ⁻ 0k₀~) (idxˣ⁻ˡ k″k‴~ x∸k′<)
-- --                 | ℕ.+-assoc k′ k₀ k‴
-- --                 | idxˣ⁻ˡ-<-irrelevant′ k″k‴~ x∸k′< k₀+[x∸k′]-k₀< k₀+[x∸k′]∸k₀eq
-- --                 | ≥⇒lengthˣ⁻+idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ 0k₀~ k″k‴~ (ℕ.m≤m+n _ _) k₀+[x∸k′]< k₀+[x∸k′]-k₀<
-- --                 | idxˣ⁻ˡ-<-irrelevant′ (0k₀~ ++ˣ⁻ k″k‴~) k₀+[x∸k′]< k₀+x∸k′< k₀+x∸k′eq
-- --                 | ≥⇒lengthˣ⁻+idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ kk′~ (0k₀~ ++ˣ⁻ k″k‴~) (ℕ.m≤n⇒m≤o+n _ x≥k′) k₀+x< k₀+x∸k′< = `#⁰ k₀+x<

-- -- ~ᴹ∧≥⇒[/⁰]≡ : {kk′~ : k ⍮ k′ ~ˣ⁻} →
-- --              ∀ I →
-- --              kk′~ ⊢ J ~ᴹ M →
-- --              x ℕ.≥ k′ →
-- --              --------------------
-- --              BP.[ I /⁰ x ] J ≡ J
-- -- ~ᴹ∧≥⇒[/⁰]≡ _ `unit                 x≥                  = refl
-- -- ~ᴹ∧≥⇒[/⁰]≡ _ (`bang ~M)            x≥                  = refl
-- -- ~ᴹ∧≥⇒[/⁰]≡ _ (`let-bang ~M `in ~N) x≥                  = cong₂ BP.`let-bang_`in_ (~ᴹ∧≥⇒[/⁰]≡ _ ~M x≥) (~ᴹ∧≥⇒[/⁰]≡ _ ~N x≥)
-- -- ~ᴹ∧≥⇒[/⁰]≡ _ (`#¹ u<)              x≥                  = refl
-- -- ~ᴹ∧≥⇒[/⁰]≡ _ (`λ⦂ ~S ∘ ~M)         x≥                  = cong (BP.`λ⦂ _ ∘_) (~ᴹ∧≥⇒[/⁰]≡ _ ~M (s≤s x≥))
-- -- ~ᴹ∧≥⇒[/⁰]≡ _ (~M `$ ~N)            x≥                  = cong₂ BP._`$_ (~ᴹ∧≥⇒[/⁰]≡ _ ~M x≥) (~ᴹ∧≥⇒[/⁰]≡ _ ~N x≥)
-- -- ~ᴹ∧≥⇒[/⁰]≡ _ (`#⁰ y<)              x≥
-- --   rewrite dec-no (_ ℕ.≤? _) (ℕ.<⇒≱ (ℕ.<-transˡ y< x≥)) = refl
-- -- ~ᴹ∧≥⇒[/⁰]≡ _ (`unlift-`lift ~M)    x≥                  = ~ᴹ∧≥⇒[/⁰]≡ _ ~M z≤n 

-- -- [/¹]~ᴹ[/]ᶜ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
-- --              extractˣ⁻ᵘ (kk′~ ++ˣ⁻ k″k‴~) ⊢ I ~ᴹ L →
-- --              kk′~ ++ˣ⁻ !∷ᵘ k″k‴~ ⊢ J ~ᴹ M →
-- --              ----------------------------------------------------------------------------
-- --              kk′~ ++ˣ⁻ k″k‴~ ⊢ BP.[ I /¹ k ] J ~ᴹ [ `lift L /[ uMode ] lengthˣ⁻ kk′~ ] M
-- -- [/¹]~ᴹ[/]ᶜ {_} {0}  {_}  {0}  kk′~ {k″k‴~} ~L (`unlift-`lift ~M) = ?
-- --   -- rewrite sym (extractˣ⁻ᵘ-idempotent (kk′~ ++ˣ⁻ k″k‴~))
-- --   --       | extractˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~
-- --   --       | extractˣ⁻ᵘ-++ˣ⁻ kk′~ (!∷ᵘ k″k‴~)
-- --   --   with ~M′ ← [/¹]~ᴹ[/]ᶜ (extractˣ⁻ᵘ kk′~) ~L ~M
-- --   --     rewrite sym (extractˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~)
-- --   --           | lengthˣ⁻-extractˣ⁻ᵘ kk′~                                             = `unlift-`lift ~M′
-- -- [/¹]~ᴹ[/]ᶜ {_} {0}  {_}  {0}  kk′~ {k″k‴~} ~L (`bang ~M) = ?
-- --   -- rewrite sym (extractˣ⁻ᵘ-idempotent (kk′~ ++ˣ⁻ k″k‴~))
-- --   --       | extractˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~
-- --   --       | extractˣ⁻ᵘ-++ˣ⁻ kk′~ (!∷ᵘ k″k‴~)
-- --   --   with ~M′ ← [/¹]~ᴹ[/]ᶜ (extractˣ⁻ᵘ kk′~) ~L ~M
-- --   --     rewrite sym (extractˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~)
-- --   --           | lengthˣ⁻-extractˣ⁻ᵘ kk′~                                             = `bang ~M′
-- -- [/¹]~ᴹ[/]ᶜ                    kk′~         ~L `unit                                     = `unit
-- -- [/¹]~ᴹ[/]ᶜ               kk′~         ~L (`let-bang ~M `in ~N)                      = `let-bang [/¹]~ᴹ[/]ᶜ kk′~ ~L ~M `in [/¹]~ᴹ[/]ᶜ (!∷ᵘ kk′~) (wk[↑¹]~ᴹwk[↑]ᶜ [] (!∷ᵘ []) ~L) ~N
-- -- [/¹]~ᴹ[/]ᶜ {k} {_}  {k″} kk′~ {k″k‴~} ~L (`#¹_ {u = u} u<)
-- --   with u ℕ.≥? k
-- -- ...  | no  u≱k
-- --     with u<k ← ℕ.≰⇒> u≱k
-- --       rewrite sym (<⇒idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ kk′~ (!∷ᵘ k″k‴~) u<k u<)
-- --             | dec-no (_ ℕ.≤? _) (ℕ.<⇒≱ (idxˣ⁻ᵘ<lengthˣ⁻ kk′~ u<k))
-- --             | <⇒idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~ u<k (ℕ.m≤n⇒m≤n+o _ u<k)              = `#¹ ℕ.m≤n⇒m≤n+o _ u<k
-- -- ...  | yes u≥k
-- --     with u∸k< ← subst (u ∸ k ℕ.<_) (ℕ.m+n∸m≡n k _) (ℕ.∸-monoˡ-< u< u≥k)
-- --       rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ kk′~ (!∷ᵘ k″k‴~) u≥k u< u∸k<)
-- --             | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ᵘ (!∷ᵘ k″k‴~) u∸k<)))
-- --         with u ℕ.≟ k
-- -- ...        | no  u≢k
-- --           with u>k ← ℕ.≤∧≢⇒< u≥k (≢-sym u≢k)
-- --              | s≤s u∸k≤ ← u∸k<
-- --             with suc u′ ← u
-- --               with u′≥k ← ℕ.≤-pred u>k
-- --                 rewrite ℕ.+-∸-assoc 1 u′≥k
-- --                       | dec-no (_ ℕ.≟ _) (ℕ.m+1+n≢m (lengthˣ⁻ kk′~) {idxˣ⁻ᵘ k″k‴~ u∸k≤})
-- --                       | ℕ.+-suc (lengthˣ⁻ kk′~) (idxˣ⁻ᵘ k″k‴~ u∸k≤)
-- --                       | ℕ.+-suc k k″
-- --                   with u′< ← ℕ.≤-pred u<
-- --                     rewrite ≥⇒lengthˣ⁻+idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~ u′≥k u′< u∸k≤ = `#¹ u′<
-- -- ...        | yes refl
-- --           with s≤s _ ← u∸k<
-- --             rewrite ℕ.n∸n≡0 k
-- --                   | proj₂ (dec-yes (_ ℕ.≟ _) (ℕ.+-identityʳ (lengthˣ⁻ kk′~)))      = ?
-- -- [/¹]~ᴹ[/]ᶜ {k} {k′} {_}  {_}  {E} kk′~         ~L (`λ⦂ ~S ∘ ~M)
-- --   with ~L′ ← wk[↑¹]~ᴹwk[↑]ᶜ [] (?∷ˡ []) ~L
-- --     with ~M′ ← [/¹]~ᴹ[/]ᶜ (!∷ˡ kk′~) ~L′ ~M
-- --       rewrite wk[0↑¹]≡ 0 E
-- --             | ℕ.+-suc k k′                                                         = `λ⦂ ~S ∘ ~M′
-- -- [/¹]~ᴹ[/]ᶜ               kk′~         ~L (~M `$ ~N)                                = [/¹]~ᴹ[/]ᶜ kk′~ ~L ~M `$ [/¹]~ᴹ[/]ᶜ kk′~ ~L ~N
-- -- [/¹]~ᴹ[/]ᶜ {_} {k′}      kk′~ {k″k‴~} ~L (`#⁰_ {x = x} x<)
-- --   with x ℕ.≥? k′
-- -- ...  | no  x≱k′
-- --     with x<k′ ← ℕ.≰⇒> x≱k′
-- --       rewrite sym (<⇒idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ kk′~ (!∷ᵘ k″k‴~) x<k′ x<)
-- --             | dec-no (_ ℕ.≥? _) (ℕ.<⇒≱ (idxˣ⁻ˡ<lengthˣ⁻ kk′~ x<k′))
-- --             | <⇒idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ kk′~ k″k‴~ x<k′ x<                              = `#⁰ x<
-- -- ...  | yes x≥k′
-- --     with x∸k′< ← subst (x ∸ k′ ℕ.<_) (ℕ.m+n∸m≡n k′ _) (ℕ.∸-monoˡ-< x< x≥k′)
-- --       rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ kk′~ (!∷ᵘ k″k‴~) x≥k′ x< x∸k′<)
-- --             | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ˡ (!∷ᵘ k″k‴~) x∸k′<)))
-- --             | dec-no (_ ℕ.≟ _) (ℕ.m+1+n≢m (lengthˣ⁻ kk′~) {idxˣ⁻ˡ k″k‴~ x∸k′<})
-- --             | ℕ.+-suc (lengthˣ⁻ kk′~) (idxˣ⁻ˡ k″k‴~ x∸k′<)
-- --             | ≥⇒lengthˣ⁻+idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ kk′~ k″k‴~ x≥k′ x< x∸k′<               = `#⁰ x<

-- -- ~ᴹ[/]ᵖ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
-- --          ∀ L →
-- --          kk′~ ++ˣ⁻ ?∷ˡ k″k‴~ ⊢ J ~ᴹ M →
-- --          --------------------------------------------------------
-- --          kk′~ ++ˣ⁻ k″k‴~ ⊢ J ~ᴹ [ L /[ lMode ] lengthˣ⁻ kk′~ ] M
-- -- ~ᴹ[/]ᵖ {_} {0}  {_} {0}  kk′~ {k″k‴~} _ (`unlift-`lift ~M) = ?
-- --   -- rewrite extractˣ⁻ᵘ-++ˣ⁻ kk′~ (?∷ˡ k″k‴~)
-- --   --   with ~M′ ← ~ᴹ[/]ᵖ (extractˣ⁻ᵘ kk′~) (`unlift `unit) ~M
-- --   --     rewrite sym (extractˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~)
-- --   --           | lengthˣ⁻-extractˣ⁻ᵘ kk′~                               = `unlift-`lift ~M′
-- -- ~ᴹ[/]ᵖ {_} {0}  {_} {0}  kk′~ {k″k‴~} _ (`bang ~M) = ?
-- --   -- rewrite extractˣ⁻ᵘ-++ˣ⁻ kk′~ (?∷ˡ k″k‴~)
-- --   --   with ~M′ ← ~ᴹ[/]ᵖ (extractˣ⁻ᵘ kk′~) (`unlift `unit) ~M
-- --   --     rewrite sym (extractˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~)
-- --   --           | lengthˣ⁻-extractˣ⁻ᵘ kk′~                               = `bang ~M′
-- -- ~ᴹ[/]ᵖ          kk′~         _ `unit                                 = `unit
-- -- ~ᴹ[/]ᵖ          kk′~         _ (`let-bang ~M `in ~N)                  = `let-bang ~ᴹ[/]ᵖ kk′~ _ ~M `in ~ᴹ[/]ᵖ (!∷ᵘ kk′~) _ ~N
-- -- ~ᴹ[/]ᵖ {k}      kk′~ {k″k‴~} _ (`#¹_ {u = u} u<)
-- --   with u ℕ.≥? k
-- -- ...  | no  u≱k
-- --     rewrite sym (<⇒idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ kk′~ (?∷ˡ k″k‴~) (ℕ.≰⇒> u≱k) u<)
-- --           | dec-no (_ ℕ.≥? _) (ℕ.<⇒≱ (idxˣ⁻ᵘ<lengthˣ⁻ kk′~ (ℕ.≰⇒> u≱k)))
-- --           | <⇒idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~ (ℕ.≰⇒> u≱k) u<           = `#¹ u<
-- -- ...  | yes u≥k
-- --     with u∸k< ← subst (u ∸ k ℕ.<_) (ℕ.m+n∸m≡n k _) (ℕ.∸-monoˡ-< u< u≥k)
-- --       rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ kk′~ (?∷ˡ k″k‴~) u≥k u< u∸k<)
-- --             | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ᵘ (?∷ˡ k″k‴~) u∸k<)))
-- --             | dec-no (_ ℕ.≟ _) (ℕ.m+1+n≢m (lengthˣ⁻ kk′~) {idxˣ⁻ᵘ k″k‴~ u∸k<})
-- --             | ℕ.+-suc (lengthˣ⁻ kk′~) (idxˣ⁻ᵘ k″k‴~ u∸k<)
-- --             | ≥⇒lengthˣ⁻+idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~ u≥k u< u∸k<   = `#¹ u<
-- -- ~ᴹ[/]ᵖ          kk′~         _ (`λ⦂ ~S ∘ ~M)                         = `λ⦂ ~S ∘ (~ᴹ[/]ᵖ (!∷ˡ kk′~) _ ~M)
-- -- ~ᴹ[/]ᵖ          kk′~         _ (~M `$ ~N)                            = ~ᴹ[/]ᵖ kk′~ _ ~M `$ ~ᴹ[/]ᵖ kk′~ _ ~N
-- -- ~ᴹ[/]ᵖ {_} {k′} kk′~ {k″k‴~} _ (`#⁰_ {x = x} x<)
-- --   with x ℕ.≥? k′
-- -- ...  | no  x≱k′
-- --     with x<k′ ← ℕ.≰⇒> x≱k′
-- --       rewrite sym (<⇒idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ kk′~ (?∷ˡ k″k‴~) x<k′ x<)
-- --             | dec-no (_ ℕ.≥? _) (ℕ.<⇒≱ (idxˣ⁻ˡ<lengthˣ⁻ kk′~ x<k′))
-- --             | <⇒idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ kk′~ k″k‴~ x<k′ x<                = `#⁰ x<
-- -- ...  | yes x≥k′
-- --     with x∸k′< ← subst (x ∸ k′ ℕ.<_) (ℕ.m+n∸m≡n k′ _) (ℕ.∸-monoˡ-< x< x≥k′)
-- --       rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ kk′~ (?∷ˡ k″k‴~) x≥k′ x< x∸k′<)
-- --             | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ˡ (?∷ˡ k″k‴~) x∸k′<)))
-- --             | dec-no (_ ℕ.≟ _) (ℕ.m+1+n≢m (lengthˣ⁻ kk′~) {idxˣ⁻ˡ k″k‴~ x∸k′<})
-- --             | ℕ.+-suc (lengthˣ⁻ kk′~) (idxˣ⁻ˡ k″k‴~ x∸k′<)
-- --             | ≥⇒lengthˣ⁻+idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ kk′~ k″k‴~ x≥k′ x< x∸k′< = `#⁰ x<

-- -- [/⁰]~ᴹ[/]ᵖ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
-- --              kk′~ ++ˣ⁻ k″k‴~ ⊢ I ~ᴹ L →
-- --              kk′~ ++ˣ⁻ !∷ˡ k″k‴~ ⊢ J ~ᴹ M →
-- --              -----------------------------------------------------------------------
-- --              kk′~ ++ˣ⁻ k″k‴~ ⊢ BP.[ I /⁰ k′ ] J ~ᴹ [ L /[ lMode ] lengthˣ⁻ kk′~ ] M
-- -- -- [/⁰]~ᴹ[/]ᵖ {_} {0}  {_}  {0}            kk′~ {k″k‴~} ~L (`bang ~M) = ?
-- --   -- rewrite extractˣ⁻ᵘ-++ˣ⁻ kk′~ (!∷ˡ k″k‴~)
-- --   --   with ~M′ ← ~ᴹ[/]ᵖ (extractˣ⁻ᵘ kk′~) (`unlift `unit) ~M
-- --   --     rewrite sym (extractˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~)
-- --   --           | lengthˣ⁻-extractˣ⁻ᵘ kk′~                                               = `bang ~M′
-- -- -- [/⁰]~ᴹ[/]ᵖ {_} {0}  {_}  {0}          kk′~ {k″k‴~} ~L (`unlift-`lift ~M) = ?
-- --   -- rewrite ~ᴹ∧≥⇒[/⁰]≡ E ~M (z≤n {k′})
-- --   --       | extractˣ⁻ᵘ-++ˣ⁻ kk′~ (!∷ˡ k″k‴~)
-- --   --   with ~M′ ← ~ᴹ[/]ᵖ (extractˣ⁻ᵘ kk′~) (`unlift `unit) ~M
-- --   --     rewrite sym (extractˣ⁻ᵘ-++ˣ⁻ kk′~ k″k‴~)
-- --   --           | lengthˣ⁻-extractˣ⁻ᵘ kk′~                                               = `unlift-`lift ~M′
-- -- [/⁰]~ᴹ[/]ᵖ                              kk′~         ~L `unit                        = `unit
-- -- [/⁰]~ᴹ[/]ᵖ                              kk′~         ~L (`let-bang ~M `in ~N)         = `let-bang [/⁰]~ᴹ[/]ᵖ kk′~ ~L ~M `in [/⁰]~ᴹ[/]ᵖ (!∷ᵘ kk′~) (wk[↑¹]~ᴹwk[↑]ᶜ [] (!∷ᵘ []) ~L) ~N
-- -- [/⁰]~ᴹ[/]ᵖ {k} {_}  {_}  {_}  {_}   {L} kk′~ {k″k‴~} ~L (`#¹_ {u = u} u<)
-- --   with u ℕ.≥? k
-- -- ...  | no  u≱k
-- --     rewrite sym (<⇒idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ kk′~ (!∷ˡ k″k‴~) (ℕ.≰⇒> u≱k) u<)
-- --           | <⇒idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ kk′~ (?∷ˡ k″k‴~) (ℕ.≰⇒> u≱k) u<                     = ~ᴹ[/]ᵖ kk′~ L (`#¹ u<)
-- -- ...  | yes u≥k
-- --     with u∸k< ← subst (u ∸ k ℕ.<_) (ℕ.m+n∸m≡n k _) (ℕ.∸-monoˡ-< u< u≥k)
-- --       rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ kk′~ (!∷ˡ k″k‴~) u≥k u< u∸k<)
-- --             | ≥⇒lengthˣ⁻+idxˣ⁻ᵘ≡idxˣ⁻ᵘ-++ˣ⁻ kk′~ (?∷ˡ k″k‴~) u≥k u< u∸k<             = ~ᴹ[/]ᵖ kk′~ L (`#¹ u<) 
-- -- [/⁰]~ᴹ[/]ᵖ {k} {k′}                     kk′~         ~L (`λ⦂ ~S ∘ ~M)
-- --   with ~M′ ← [/⁰]~ᴹ[/]ᵖ (!∷ˡ kk′~) (wk[↑⁰]~ᴹwk[↑]ᵖ [] (!∷ˡ []) ~L) ~M
-- --     rewrite ℕ.+-suc k k′                                                             = `λ⦂ ~S ∘ ~M′
-- -- [/⁰]~ᴹ[/]ᵖ                              kk′~         ~L (~M `$ ~N)                   = [/⁰]~ᴹ[/]ᵖ kk′~ ~L ~M `$ [/⁰]~ᴹ[/]ᵖ kk′~ ~L ~N
-- -- [/⁰]~ᴹ[/]ᵖ {_} {k′} {_}  {k‴}           kk′~ {k″k‴~} ~L (`#⁰_ {x = x} x<)
-- --   with x ℕ.≥? k′
-- -- ...  | no  x≱k′
-- --     with x<k′ ← ℕ.≰⇒> x≱k′
-- --       rewrite sym (<⇒idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ kk′~ (!∷ˡ k″k‴~) x<k′ x<)
-- --             | dec-no (_ ℕ.≥? _) (ℕ.<⇒≱ (idxˣ⁻ˡ<lengthˣ⁻ kk′~ x<k′))
-- --             | <⇒idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ kk′~ k″k‴~ x<k′ (ℕ.m≤n⇒m≤n+o _ x<k′)              = `#⁰ ℕ.m≤n⇒m≤n+o _ x<k′
-- -- ...  | yes x≥k′
-- --     with x∸k′< ← subst (x ∸ k′ ℕ.<_) (ℕ.m+n∸m≡n k′ _) (ℕ.∸-monoˡ-< x< x≥k′)
-- --       rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ kk′~ (!∷ˡ k″k‴~) x≥k′ x< x∸k′<)
-- --             | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ˡ (!∷ˡ k″k‴~) x∸k′<)))
-- --         with x ℕ.≟ k′
-- -- ...        | no  x≢k′
-- --           with x>k′ ← ℕ.≤∧≢⇒< x≥k′ (≢-sym x≢k′)
-- --              | s≤s x∸k′≤ ← x∸k′<
-- --             with suc x′ ← x
-- --               with x′≥k′ ← ℕ.≤-pred x>k′
-- --                 rewrite ℕ.+-∸-assoc 1 (ℕ.≤-pred x>k′)
-- --                       | dec-no (_ ℕ.≟ _) (ℕ.m+1+n≢m (lengthˣ⁻ kk′~) {idxˣ⁻ˡ k″k‴~ x∸k′≤})
-- --                       | ℕ.+-suc (lengthˣ⁻ kk′~) (idxˣ⁻ˡ k″k‴~ x∸k′≤)
-- --                       | ℕ.+-suc k′ k‴
-- --                   with x′< ← ℕ.≤-pred x<
-- --                     rewrite ≥⇒lengthˣ⁻+idxˣ⁻ˡ≡idxˣ⁻ˡ-++ˣ⁻ kk′~ k″k‴~ x′≥k′ x′< x∸k′≤ = `#⁰ x′<
-- -- ...        | yes refl
-- --           with s≤s _ ← x∸k′<
-- --             rewrite ℕ.n∸n≡0 k′
-- --                   | proj₂ (dec-yes (_ ℕ.≟ _) (ℕ.+-identityʳ (lengthˣ⁻ kk′~)))        = ~L


-- -- -- Bisimulation Properties of _~ᴹ_ Regarding OpSems
-- -- --
-- -- ~ᴹ-simulation-helper : I BP.⟶ I′ →
-- --                        (~L : [] ⊢ I ~ᴹ L) →
-- --                        Acc ℕ._<_ (depth~ᴹ ~L) →
-- --                        -----------------------------------
-- --                        ∃ (λ L′ → L ⟶* L′ × [] ⊢ I′ ~ᴹ L′)
-- -- ~ᴹ-simulation-helper I⟶                    (`unlift-`lift ~L)   (acc r)
-- --   with _ , ⟶*L′[≤] , VL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
-- --     with _ , ⟶*L″ , ~L″ ← ~ᴹ-simulation-helper I⟶ ~L′ (r _ (s≤s L′≤))        = -, ξ-of-↝*-⟶* _⟶[ uMode ≤]_ `unlift`lift ξ-`unlift`lift ⟶*L′[≤]
-- --                                                                                  ◅◅ β-`↑ VL′ ◅ ⟶*L″
-- --                                                                              , ~L″
-- -- ~ᴹ-simulation-helper BP.ξ-`let-bang I⟶ `in- (`let-bang ~L `in ~M) (acc r)
-- --   with _ , ⟶*L′ , ~L′ ← ~ᴹ-simulation-helper I⟶ ~L (r _ (s≤s (ℕ.m≤m⊔n _ _))) = -, ξ-of-⟶* (`let-return_`in _) ξ-`let-return_`in- ⟶*L′
-- --                                                                                , `let-bang ~L′ `in ~M
-- -- ~ᴹ-simulation-helper BP.β-`!               (`let-bang ~L `in ~M) (acc r)
-- --   with _ , ⟶*`bangL′ , WL′ , ~L ← `bang-~ᴹ-inv ~L                              = -, ξ-of-⟶* (`let-return_`in _) ξ-`let-return_`in- ⟶*`bangL′
-- --                                                                                  ◅◅ β-`↓ (`lift WL′) ◅ ε
-- --                                                                              , [/¹]~ᴹ[/]ᶜ [] ~L ~M
-- -- ~ᴹ-simulation-helper BP.ξ- I⟶ `$?          (~L `$ ~M)           (acc r)
-- --   with _ , ⟶*L′ , ~L′ ← ~ᴹ-simulation-helper I⟶ ~L (r _ (s≤s (ℕ.m≤m⊔n _ _))) = -, ξ-of-⟶* (_`$ _) ξ-_`$? ⟶*L′
-- --                                                                              , ~L′ `$ ~M
-- -- ~ᴹ-simulation-helper (BP.ξ-! VI `$ J⟶)     (~L `$ ~M)           (acc r)
-- --   with _ , ⟶*L′ , VL′ , ~L′ ← Value~ᴹ-normalize ~L VI
-- --      | _ , ⟶*M′ , ~M′ ← ~ᴹ-simulation-helper J⟶ ~M (r _ (s≤s (ℕ.m≤n⊔m _ _))) = -, ξ-of-⟶* (_`$ _) ξ-_`$? ⟶*L′
-- --                                                                                  ◅◅ ξ-of-⟶* (_ `$_) (ξ-! VL′ `$_) ⟶*M′
-- --                                                                              , ~L′ `$ ~M′
-- -- ~ᴹ-simulation-helper (BP.β-`⊸ VJ)          (~L `$ ~M)           (acc r)
-- --   with _ , _ , ⟶*`λ⦂ˡS′∘L′ , ~L′ , ~S′ ← `λ⦂-∙-~ᴹ-inv ~L
-- --      | _ , ⟶*M′ , VM′ , ~M′ ← Value~ᴹ-normalize ~M VJ                        = -, ξ-of-⟶* (_`$ _) ξ-_`$? ⟶*`λ⦂ˡS′∘L′
-- --                                                                                  ◅◅ ξ-of-⟶* (_ `$_) ξ-! `λ⦂ˡ _ ∘ _ `$_ ⟶*M′
-- --                                                                                  ◅◅ β-`⊸ VM′ ◅ ε
-- --                                                                              , [/⁰]~ᴹ[/]ᵖ [] ~M′ ~L′

-- -- ~ᴹ-simulation : I BP.⟶ I′ →
-- --                 [] ⊢ I ~ᴹ L →
-- --                 -----------------------------------
-- --                 ∃ (λ L′ → L ⟶* L′ × [] ⊢ I′ ~ᴹ L′)
-- -- ~ᴹ-simulation I⟶ ~L = ~ᴹ-simulation-helper I⟶ ~L (ℕ.<-wellFounded _)

-- -- ~ᴹ⁻¹-simulation : L ⟶ L′ →
-- --                   [] ⊢ I ~ᴹ L →
-- --                   -----------------------------------------------
-- --                   ∃ (λ I′ → I BP.⟶* I′ × [] ⊢ I′ ~ᴹ L′)
-- -- ~ᴹ⁻¹-simulation (ξ-`unlift (ξ-`lift L⟶[≤])) (`unlift-`lift ~L)        = -, ε , `unlift-`lift (⟶[≤]-preserves-~ᴹ ~L L⟶[≤])
-- -- ~ᴹ⁻¹-simulation (β-`↑ WL′)                  (`unlift-`lift ~L)        = -, ε , ~L
-- -- ~ᴹ⁻¹-simulation (ξ-`return (ξ-`lift L⟶[≤])) (`bang ~L)                 = -, ε , `bang (⟶[≤]-preserves-~ᴹ ~L L⟶[≤])
-- -- ~ᴹ⁻¹-simulation ξ-`let-return L⟶ `in-       (`let-bang ~L `in ~M)
-- --   with _ , I⟶* , ~L′ ← ~ᴹ⁻¹-simulation L⟶ ~L                          = -, BP.ξ-of-⟶* (BP.`let-bang_`in _) BP.ξ-`let-bang_`in- I⟶* , `let-bang ~L′ `in ~M
-- -- ~ᴹ⁻¹-simulation (β-`↓ (`lift WL))           (`let-bang `bang ~L `in ~M) = -, BP.β-`! ◅ ε , [/¹]~ᴹ[/]ᶜ [] ~L ~M
-- -- ~ᴹ⁻¹-simulation ξ- L⟶ `$?                   (~L `$ ~M)
-- --   with _ , I⟶* , ~L′ ← ~ᴹ⁻¹-simulation L⟶ ~L                          = -, BP.ξ-of-⟶* (BP._`$ _) BP.ξ-_`$? I⟶* , ~L′ `$ ~M
-- -- ~ᴹ⁻¹-simulation (ξ-! VL′ `$ M⟶)             (~L `$ ~M)
-- --   with _ , J⟶* , ~M′ ← ~ᴹ⁻¹-simulation M⟶ ~M                          = -, BP.ξ-of-⟶* (_ BP.`$_) (BP.ξ-! []⊢~ᴹ⁻¹-respects-Value ~L VL′ `$_) J⟶* , ~L `$ ~M′
-- -- ~ᴹ⁻¹-simulation (β-`⊸ VM)                   ((`λ⦂ ~S ∘ ~L) `$ ~M)     = -, BP.β-`⊸ ([]⊢~ᴹ⁻¹-respects-Value ~M VM) ◅ ε , [/⁰]~ᴹ[/]ᵖ [] ~M ~L

