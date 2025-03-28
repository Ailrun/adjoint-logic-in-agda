------------------------------------------------------------
-- Translation of Original λ□ [Davies & Pfenning 2001] into Adjoint λ□
------------------------------------------------------------
--
-- This module provides an translation relation between original λ□
-- and adjoint λ□, the proofs of completeness and soundness of the
-- relation regarding their typings, and bisimulation of the relation
-- regarding their operational semantics.
--

{-# OPTIONS --safe #-}
module Calculus.AdjND.Embedding.LambdaBox where

open import Agda.Primitive
open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n; s≤s; _+_; _∸_)
import Data.Nat.Induction as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃; ∃₂; -,_)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary using (Rel; Antisymmetric; IsPartialOrder; IsDecPartialOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; ≢-sym)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (dec-yes; dec-no)

open import Calculus.GeneralOpSem using (wkidx[_↑_]_; idx[_/_]_along_)
open import Calculus.GeneralOpSem.Properties
open import Calculus.AdjND.Embedding.LambdaBox.ModeSpec
import Calculus.AdjND.Syntax as S
import Calculus.AdjND.Typing as T
import Calculus.AdjND.Typing.Properties as TP
import Calculus.AdjND.OpSem as O
open S ℳ²
open T ℳ²
open TP ℳ²
open O ℳ²
import Calculus.LambdaBox.Syntax as DP
import Calculus.LambdaBox.OpSem as DP
import Calculus.LambdaBox.Typing as DP
import Calculus.LambdaBox.Typing.Properties as DP
open DP.Variables

infix   4 _~ᵀ_
infix   4 _⍮_~ˣ_
infix   4 _⍮_~ˣ⁻
infix   4 _⊢_~ᴹ_
infixr  5 _++ˣ⁻_

-- Pattern Synonyms for Syntax
--
pattern `↓ S = `↓[ cMode ⇒ pMode ] S
pattern `↑ S = `↑[ pMode ⇒ cMode ] S

pattern `lift L                     = `lift[ pMode ⇒ cMode ] L
pattern `unlift L                   = `unlift[ cMode ⇒ pMode ] L
pattern `return L                   = `return[ cMode ⇒ pMode ] L
pattern `let-return_`in_    L M     = `let-return[ pMode ⇒ cMode ] L `in M
pattern `let-return[_]_`in_ c≰p L M = `let-return[≰ c≰p ⇒ cMode ] L `in M
pattern `λ⦂ᵖ_∘_ S L                 = `λ⦂[ pMode ] S ∘ L
pattern `unlift`lift L              = `unlift (`lift L)
pattern `unlift`#_ x                = `unlift (`# x)
pattern `return`lift L              = `return (`lift L)

-- Pattern Synonyms for Typing
--
pattern ⊢`⊤         = `⊤[ _ ]
pattern ⊢`↓ neq ⊢S  = `↓[-⇒ p≤c , neq ][ _ ] ⊢S
pattern ⊢`↑ neq ⊢S  = `↑[-⇒ p≤c , neq ][ _ ] ⊢S
pattern ⊢_`⊸_ ⊢S ⊢T = ⊢S `⊸[ _ ] ⊢T

pattern ⊢`lift ⊢L                              = `lift[-⇒-] ⊢L
pattern _⊢`unlift_⦂_ Γ∤ ⊢L ⊢S                  = Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢S
pattern _⊢`return_ Γ∤ ⊢L                       = Γ∤ ⊢`return[-⇒-] ⊢L
pattern _&_⊢`let-return_⦂_`in_ Γ~ Γ₀∤ ⊢L ⊢S ⊢M = Γ~ & Γ₀∤ ⊢`let-return[ refl ⇒-] ⊢L ⦂ ⊢S `in ⊢M
pattern _⊢`unlift`lift_⦂_ Γ∤ ⊢L ⊢S             = Γ∤ ⊢`unlift ⊢`lift ⊢L ⦂ ⊢S
pattern _⊢`unlift`#_⦂_ Γ∤ x∈ ⊢S                = Γ∤ ⊢`unlift `# x∈ ⦂ ⊢S
pattern _⊢`return`lift_ Γ∤ ⊢L                  = Γ∤ ⊢`return ⊢`lift ⊢L

-- Pattern Synonyms for OpSem
--
pattern `unlift≤ VL = `unlift[≤ refl ⇒ pMode ] VL
pattern `return≤ VL = `return[≤ refl ⇒ pMode ] VL

pattern ξ-`lift L⟶                       = ξ-`lift[-⇒-] L⟶
pattern ξ-`unlift L⟶                     = ξ-`unlift[-⇒-] L⟶
pattern ξ-`unlift≤ L⟶                    = ξ-`unlift[≤ refl ⇒-] L⟶
pattern ξ-`return L⟶                     = ξ-`return[-⇒-] L⟶
pattern ξ-`return≤ L⟶                    = ξ-`return[≤ refl ⇒-] L⟶
pattern ξ-`let-return_`in- L⟶            = ξ-`let-return[-⇒-] L⟶ `in-
pattern ξ-`let-return[_]_`in? c≰p L⟶     = ξ-`let-return[≰ c≰p ⇒-] L⟶ `in?
pattern ξ-`let-return![_]_`in_ c≰p WL M⟶ = ξ-`let-return[≰ c≰p ⇒-]! WL `in M⟶
pattern ξ-`unlift`lift L⟶                = ξ-`unlift (ξ-`lift L⟶)
pattern ξ-`unlift≤`lift L⟶               = ξ-`unlift≤ (ξ-`lift L⟶)
pattern ξ-`return`lift L⟶                = ξ-`return (ξ-`lift L⟶)
pattern ξ-`return≤`lift L⟶               = ξ-`return≤ (ξ-`lift L⟶)

c≰p : ¬ (cMode ≤ₘ² pMode)
c≰p ()

------------------------------------------------------------
-- Bisimilar Embedding Relation
------------------------------------------------------------

-- Embedding Relation for Types
--
data _~ᵀ_ : DP.Type → Type → Set where
  `⊤   : ------------
         DP.`⊤ ~ᵀ `⊤

  `□   : A ~ᵀ S →
         ---------------------
         DP.`□ A ~ᵀ `↓ (`↑ S)

  _`→_ : A ~ᵀ S →
         B ~ᵀ T →
         --------------------
         A DP.`→ B ~ᵀ S `⊸ T

-- Embedding Relation for Contexts
--
data _⍮_~ˣ_ : DP.Context → DP.Context → Context → Set where
  []    : --------------
          [] ⍮ [] ~ˣ []

  _!∷ᶜ_ : A ~ᵀ S →
          Ψ₁ ⍮ Ψ₀ ~ˣ Γ →
          -----------------------------------------
          A ∷ Ψ₁ ⍮ Ψ₀ ~ˣ (`↑ S , cMode , true) ∷ Γ

  ?∷ᵖ_  : Ψ₁ ⍮ Ψ₀ ~ˣ Γ →
          -----------------------------------
          Ψ₁ ⍮ Ψ₀ ~ˣ (S , pMode , false) ∷ Γ

  _!∷ᵖ_ : A ~ᵀ S →
          Ψ₁ ⍮ Ψ₀ ~ˣ Γ →
          --------------------------------------
          Ψ₁ ⍮ A ∷ Ψ₀ ~ˣ (S , pMode , true) ∷ Γ

-- Embedding Relation for Context Skeleton
--
-- To track de Bruijn indices in the embedding relation,
-- We need to track the structure of the context embedding.
data _⍮_~ˣ⁻ : ℕ → ℕ → Set where
  []   : ----------
         0 ⍮ 0 ~ˣ⁻

  !∷ᶜ_ : k ⍮ k′ ~ˣ⁻ →
         ---------------
         suc k ⍮ k′ ~ˣ⁻

  ?∷ᵖ_ : k ⍮ k′ ~ˣ⁻ →
         -------------
         k ⍮ k′ ~ˣ⁻

  !∷ᵖ_ : k ⍮ k′ ~ˣ⁻ →
         ---------------
         k ⍮ suc k′ ~ˣ⁻

-- Operations for The Context Embeddings
variable
  kk′~ : k ⍮ k′ ~ˣ⁻

eraseˣ : Ψ₁ ⍮ Ψ₀ ~ˣ Γ → length Ψ₁ ⍮ length Ψ₀ ~ˣ⁻
eraseˣ []         = []
eraseˣ (_ !∷ᶜ ~Γ) = !∷ᶜ eraseˣ ~Γ
eraseˣ   (?∷ᵖ ~Γ) = ?∷ᵖ eraseˣ ~Γ
eraseˣ (_ !∷ᵖ ~Γ) = !∷ᵖ eraseˣ ~Γ

_++ˣ⁻_ : k ⍮ k′ ~ˣ⁻ → k″ ⍮ k‴ ~ˣ⁻ → k + k″ ⍮ k′ + k‴ ~ˣ⁻
[]         ++ˣ⁻ k″k‴~ = k″k‴~
(!∷ᶜ kk′~) ++ˣ⁻ k″k‴~ = !∷ᶜ (kk′~ ++ˣ⁻ k″k‴~)
(?∷ᵖ kk′~) ++ˣ⁻ k″k‴~ = ?∷ᵖ (kk′~ ++ˣ⁻ k″k‴~)
(!∷ᵖ kk′~) ++ˣ⁻ k″k‴~ = !∷ᵖ (kk′~ ++ˣ⁻ k″k‴~)

extractˣ⁻ᶜ : k ⍮ k′ ~ˣ⁻ → k ⍮ 0 ~ˣ⁻
extractˣ⁻ᶜ []         = []
extractˣ⁻ᶜ (!∷ᶜ kk′~) = !∷ᶜ extractˣ⁻ᶜ kk′~
extractˣ⁻ᶜ (?∷ᵖ kk′~) = ?∷ᵖ extractˣ⁻ᶜ kk′~
extractˣ⁻ᶜ (!∷ᵖ kk′~) = ?∷ᵖ extractˣ⁻ᶜ kk′~

extractˣᶜ : Ψ₁ ⍮ Ψ₀ ~ˣ Γ →
            -------------------------
            ∃ (λ Γ′ → Ψ₁ ⍮ [] ~ˣ Γ′)
extractˣᶜ []                        = _ , []
extractˣᶜ (S~ !∷ᶜ ~Γ)               = _ , S~ !∷ᶜ proj₂ (extractˣᶜ ~Γ)
extractˣᶜ (?∷ᵖ_ {_} {_} {_} {S} ~Γ) = (S , _ , _) ∷ _ , ?∷ᵖ proj₂ (extractˣᶜ ~Γ)
extractˣᶜ (_!∷ᵖ_ {_} {S} S~ ~Γ)     = (S , _ , _) ∷ _ , ?∷ᵖ proj₂ (extractˣᶜ ~Γ)

lengthˣ⁻ : k ⍮ k′ ~ˣ⁻ → ℕ
lengthˣ⁻ []         = 0
lengthˣ⁻ (!∷ᶜ kk′~) = suc (lengthˣ⁻ kk′~)
lengthˣ⁻ (?∷ᵖ kk′~) = suc (lengthˣ⁻ kk′~)
lengthˣ⁻ (!∷ᵖ kk′~) = suc (lengthˣ⁻ kk′~)

idxˣ⁻ᶜ : k ⍮ k′ ~ˣ⁻ → u ℕ.< k → ℕ
idxˣ⁻ᶜ             (?∷ᵖ kk′~) u<         = suc (idxˣ⁻ᶜ kk′~ u<)
idxˣ⁻ᶜ             (!∷ᵖ kk′~) u<         = suc (idxˣ⁻ᶜ kk′~ u<)
idxˣ⁻ᶜ {u = 0}     (!∷ᶜ kk′~) (ℕ.s≤s u<) = 0
idxˣ⁻ᶜ {u = suc u} (!∷ᶜ kk′~) (ℕ.s≤s u<) = suc (idxˣ⁻ᶜ kk′~ u<)

idxˣ⁻ᵖ : k ⍮ k′ ~ˣ⁻ → x ℕ.< k′ → ℕ
idxˣ⁻ᵖ             (!∷ᶜ kk′~) x<         = suc (idxˣ⁻ᵖ kk′~ x<)
idxˣ⁻ᵖ             (?∷ᵖ kk′~) x<         = suc (idxˣ⁻ᵖ kk′~ x<)
idxˣ⁻ᵖ {x = 0}     (!∷ᵖ kk′~) (ℕ.s≤s x<) = 0
idxˣ⁻ᵖ {x = suc x} (!∷ᵖ kk′~) (ℕ.s≤s x<) = suc (idxˣ⁻ᵖ kk′~ x<)

-- Embedding Relation for Terms
--
data _⊢_~ᴹ_ : k ⍮ k′ ~ˣ⁻ → DP.Term → Term → Set where
  `unit         : -------------------------
                  kk′~ ⊢ DP.`unit ~ᴹ `unit

  `box          : extractˣ⁻ᶜ kk′~ ⊢ E ~ᴹ L →
                  -----------------------------------
                  kk′~ ⊢ DP.`box E ~ᴹ `return`lift L

  `let-box_`in_ : kk′~ ⊢ E ~ᴹ L →
                  !∷ᶜ kk′~ ⊢ F ~ᴹ M →
                  --------------------------------------------------
                  kk′~ ⊢ DP.`let-box E `in F ~ᴹ `let-return L `in M

  `#¹_          : (u< : DP.u ℕ.< k) →
                  -------------------------------------------------
                  kk′~ ⊢ DP.`#¹ DP.u ~ᴹ `unlift`# (idxˣ⁻ᶜ kk′~ u<)

  `λ⦂_∙_        : A ~ᵀ S →
                  !∷ᵖ kk′~ ⊢ E ~ᴹ L →
                  ----------------------------------
                  kk′~ ⊢ DP.`λ⦂ A ∙ E ~ᴹ `λ⦂ᵖ S ∘ L

  _`$_          : kk′~ ⊢ E ~ᴹ L →
                  kk′~ ⊢ F ~ᴹ M →
                  ---------------------------
                  kk′~ ⊢ E DP.`$ F ~ᴹ L `$ M

  `#⁰_          : (x< : x ℕ.< k′) →
                  ---------------------------------------
                  kk′~ ⊢ DP.`#⁰ x ~ᴹ `# (idxˣ⁻ᵖ kk′~ x<)

  `unlift-`lift : extractˣ⁻ᶜ kk′~ ⊢ E ~ᴹ L →
                  ---------------------------
                  kk′~ ⊢ E ~ᴹ `unlift`lift L

-- Properties of ℳ²
--
is-del² : ∀ m d →
          --------------
          d [ m ]is-del
is-del² _ false = unusable
is-del² _ true  = weakening _

is-all-del² : ∀ Γ →
              --------------
              Γ is-all-del
is-all-del² []      = []
is-all-del² (_ ∷ Γ) = is-del² _ _ ∷ is-all-del² _

~d⊞² : ∀ m d →
       ----------------
       d [ m ]~d d ⊞ d
~d⊞² _ false = unusable
~d⊞² _ true  = contraction _

~⊞² : ∀ Γ →
      ----------
      Γ ~ Γ ⊞ Γ
~⊞² []      = []
~⊞² (_ ∷ Γ) = ~d⊞² _ _ ∷ ~⊞² _

d∤ᵖ : ∀ m d →
      d [ m ]∤[ pMode ]d d
d∤ᵖ cMode d = keep p≤c
d∤ᵖ pMode d = keep refl

∤ᵖ : ∀ Γ →
     Γ ∤[ pMode ] Γ
∤ᵖ []                = []
∤ᵖ ((_ , m , d) ∷ Γ) = (d∤ᵖ m d) ∷ (∤ᵖ Γ)

-- A termination measure for _⊢_~ᴹ_
depth~ᴹ : kk′~ ⊢ E ~ᴹ L → ℕ
depth~ᴹ `unit                = 0
depth~ᴹ (`box ~L)            = suc (depth~ᴹ ~L)
depth~ᴹ (`let-box ~L `in ~M) = suc (depth~ᴹ ~L ℕ.⊔ depth~ᴹ ~M)
depth~ᴹ (`#¹ u)              = 0
depth~ᴹ (`λ⦂ ~S ∙ ~L)        = suc (depth~ᴹ ~L)
depth~ᴹ (~L `$ ~M)           = suc (depth~ᴹ ~L ℕ.⊔ depth~ᴹ ~M)
depth~ᴹ (`#⁰ x)              = 0
depth~ᴹ (`unlift-`lift ~L)   = suc (depth~ᴹ ~L)

-- Properties of _~ᵀ_
--
-- In fact, _~ᵀ_ can be replaced by an injective function.
~ᵀ-det : A ~ᵀ S →
         A ~ᵀ S′ →
         ----------
         S ≡ S′
~ᵀ-det `⊤         `⊤           = refl
~ᵀ-det (`□ ~S)    (`□ ~S′)
  rewrite ~ᵀ-det ~S ~S′        = refl
~ᵀ-det (~S `→ ~T) (~S′ `→ ~T′)
  rewrite ~ᵀ-det ~S ~S′
        | ~ᵀ-det ~T ~T′        = refl

~ᵀ-inj : A ~ᵀ S →
         A′ ~ᵀ S →
         ----------
         A ≡ A′
~ᵀ-inj `⊤         `⊤           = refl
~ᵀ-inj (`□ ~S)    (`□ ~S′)
  rewrite ~ᵀ-inj ~S ~S′        = refl
~ᵀ-inj (~S `→ ~T) (~S′ `→ ~T′)
  rewrite ~ᵀ-inj ~S ~S′
        | ~ᵀ-inj ~T ~T′        = refl

~ᵀ-total : ∀ A →
           -----------------
           ∃ (λ S → A ~ᵀ S)
~ᵀ-total DP.`⊤       = -, `⊤
~ᵀ-total (A DP.`→ B) = -, proj₂ (~ᵀ-total A) `→ proj₂ (~ᵀ-total B)
~ᵀ-total (DP.`□ A)   = -, `□ (proj₂ (~ᵀ-total A))

~ᵀ⇒⊢ : A ~ᵀ S →
       ----------------
       ⊢[ pMode ] S ⦂⋆
~ᵀ⇒⊢ `⊤         = ⊢`⊤
~ᵀ⇒⊢ (`□ ~S)    = ⊢`↓ (λ ()) (⊢`↑ (λ ()) (~ᵀ⇒⊢ ~S))
~ᵀ⇒⊢ (~S `→ ~T) = ⊢ ~ᵀ⇒⊢ ~S `⊸ ~ᵀ⇒⊢ ~T

∈ᵖ⇒~ᵀ : Ψ₁ ⍮ Ψ₀ ~ˣ Γ →
        x ⦂[ pMode ] S ∈ Γ →
        ---------------------
        ∃ (λ A → A ~ᵀ S)
∈ᵖ⇒~ᵀ (_  !∷ᶜ ~Γ) (there _ x∈) = ∈ᵖ⇒~ᵀ ~Γ x∈
∈ᵖ⇒~ᵀ    (?∷ᵖ ~Γ) (there _ x∈) = ∈ᵖ⇒~ᵀ ~Γ x∈
∈ᵖ⇒~ᵀ (~S !∷ᵖ ~Γ) (here _)     = -, ~S
∈ᵖ⇒~ᵀ (_  !∷ᵖ ~Γ) (there _ x∈) = ∈ᵖ⇒~ᵀ ~Γ x∈

∈ᶜ⇒~ᵀ : Ψ₁ ⍮ Ψ₀ ~ˣ Γ →
        x ⦂[ cMode ] `↑ S ∈ Γ →
        ------------------------
        ∃ (λ A → A ~ᵀ S)
∈ᶜ⇒~ᵀ (~S !∷ᶜ ~Γ) (here _)     = -, ~S
∈ᶜ⇒~ᵀ (_  !∷ᶜ ~Γ) (there _ x∈) = ∈ᶜ⇒~ᵀ ~Γ x∈
∈ᶜ⇒~ᵀ    (?∷ᵖ ~Γ) (there _ x∈) = ∈ᶜ⇒~ᵀ ~Γ x∈
∈ᶜ⇒~ᵀ (_  !∷ᵖ ~Γ) (there _ x∈) = ∈ᶜ⇒~ᵀ ~Γ x∈

-- Properties of the Operations for the Context Embeddings
--
extractˣᶜ-∤ : (~Γ : Ψ₁ ⍮ Ψ₀ ~ˣ Γ) →
              ---------------------------------
              let (Γ′ , ~Γ′) = extractˣᶜ ~Γ in
              Γ ∤[ cMode ] Γ′
extractˣᶜ-∤ []          = []
extractˣᶜ-∤ (~S !∷ᶜ ~Γ) = keep refl ∷ extractˣᶜ-∤ ~Γ
extractˣᶜ-∤    (?∷ᵖ ~Γ) = delete (λ ()) unusable ∷ extractˣᶜ-∤ ~Γ
extractˣᶜ-∤ (~S !∷ᵖ ~Γ) = delete (λ ()) (weakening _) ∷ extractˣᶜ-∤ ~Γ

extractˣᶜ-eraseˣ-extractˣ⁻ᶜ : (~Γ : Ψ₁ ⍮ Ψ₀ ~ˣ Γ) →
                              ------------------------------------
                              let (Γ′ , ~Γ′) = extractˣᶜ ~Γ in
                              extractˣ⁻ᶜ (eraseˣ ~Γ) ≡ eraseˣ ~Γ′
extractˣᶜ-eraseˣ-extractˣ⁻ᶜ []          = refl
extractˣᶜ-eraseˣ-extractˣ⁻ᶜ (~S !∷ᶜ ~Γ) = cong !∷ᶜ_ (extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ)
extractˣᶜ-eraseˣ-extractˣ⁻ᶜ    (?∷ᵖ ~Γ) = cong ?∷ᵖ_ (extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ)
extractˣᶜ-eraseˣ-extractˣ⁻ᶜ (~S !∷ᵖ ~Γ) = cong ?∷ᵖ_ (extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ)

idxˣ⁻ᶜ-extractˣᶜ-eraseˣ : (~Γ : Ψ₁ ⍮ Ψ₀ ~ˣ Γ) →
                          (u< : u ℕ.< length Ψ₁) →
                          -----------------------------------------------
                          let (Γ′ , ~Γ′) = extractˣᶜ ~Γ in
                          idxˣ⁻ᶜ (eraseˣ ~Γ) u< ≡ idxˣ⁻ᶜ (eraseˣ ~Γ′) u<
idxˣ⁻ᶜ-extractˣᶜ-eraseˣ                     (_ !∷ᵖ ~Γ) u<       = cong suc (idxˣ⁻ᶜ-extractˣᶜ-eraseˣ ~Γ u<)
idxˣ⁻ᶜ-extractˣᶜ-eraseˣ                       (?∷ᵖ ~Γ) u<       = cong suc (idxˣ⁻ᶜ-extractˣᶜ-eraseˣ ~Γ u<)
idxˣ⁻ᶜ-extractˣᶜ-eraseˣ {_ ∷ Δ} {u = 0}     (_ !∷ᶜ ~Γ) (s≤s u<) = refl
idxˣ⁻ᶜ-extractˣᶜ-eraseˣ {_ ∷ Δ} {u = suc u} (_ !∷ᶜ ~Γ) (s≤s u<) = cong suc (idxˣ⁻ᶜ-extractˣᶜ-eraseˣ ~Γ u<)

idxˣ⁻ᶜ-extractˣ⁻ᶜ : (kk′~ : k ⍮ k′ ~ˣ⁻) →
                    (u< : u ℕ.< k) →
                    ---------------------------------------------
                    idxˣ⁻ᶜ kk′~ u< ≡ idxˣ⁻ᶜ (extractˣ⁻ᶜ kk′~) u<
idxˣ⁻ᶜ-extractˣ⁻ᶜ                         (!∷ᵖ kk′~) u<       = cong suc (idxˣ⁻ᶜ-extractˣ⁻ᶜ kk′~ u<)
idxˣ⁻ᶜ-extractˣ⁻ᶜ                         (?∷ᵖ kk′~) u<       = cong suc (idxˣ⁻ᶜ-extractˣ⁻ᶜ kk′~ u<)
idxˣ⁻ᶜ-extractˣ⁻ᶜ {k = suc _} {u = 0}     (!∷ᶜ kk′~) (s≤s u<) = refl
idxˣ⁻ᶜ-extractˣ⁻ᶜ {k = suc _} {u = suc u} (!∷ᶜ kk′~) (s≤s u<) = cong suc (idxˣ⁻ᶜ-extractˣ⁻ᶜ kk′~ u<)

lengthˣ⁻-extractˣ⁻ᶜ : (kk′~ : k ⍮ k′ ~ˣ⁻) →
                      -------------------------------------------
                      lengthˣ⁻ (extractˣ⁻ᶜ kk′~) ≡ lengthˣ⁻ kk′~
lengthˣ⁻-extractˣ⁻ᶜ []         = refl
lengthˣ⁻-extractˣ⁻ᶜ (!∷ᶜ kk′~) = cong suc (lengthˣ⁻-extractˣ⁻ᶜ kk′~)
lengthˣ⁻-extractˣ⁻ᶜ (?∷ᵖ kk′~) = cong suc (lengthˣ⁻-extractˣ⁻ᶜ kk′~)
lengthˣ⁻-extractˣ⁻ᶜ (!∷ᵖ kk′~) = cong suc (lengthˣ⁻-extractˣ⁻ᶜ kk′~)

extractˣ⁻ᶜ-++ˣ⁻ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) →
                  ---------------------------------------------------------------------
                  extractˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) ≡ extractˣ⁻ᶜ kk′~ ++ˣ⁻ extractˣ⁻ᶜ k″k‴~
extractˣ⁻ᶜ-++ˣ⁻ []         k″k‴~ = refl
extractˣ⁻ᶜ-++ˣ⁻ (!∷ᶜ kk′~) k″k‴~ = cong !∷ᶜ_ (extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~)
extractˣ⁻ᶜ-++ˣ⁻ (?∷ᵖ kk′~) k″k‴~ = cong ?∷ᵖ_ (extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~)
extractˣ⁻ᶜ-++ˣ⁻ (!∷ᵖ kk′~) k″k‴~ = cong ?∷ᵖ_ (extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~)

extractˣ⁻ᶜ-idempotent : (kk′~ : k ⍮ k′ ~ˣ⁻) →
                        -----------------------------------------------
                        extractˣ⁻ᶜ (extractˣ⁻ᶜ kk′~) ≡ extractˣ⁻ᶜ kk′~
extractˣ⁻ᶜ-idempotent []         = refl
extractˣ⁻ᶜ-idempotent (!∷ᶜ kk′~) = cong !∷ᶜ_ (extractˣ⁻ᶜ-idempotent kk′~)
extractˣ⁻ᶜ-idempotent (?∷ᵖ kk′~) = cong ?∷ᵖ_ (extractˣ⁻ᶜ-idempotent kk′~)
extractˣ⁻ᶜ-idempotent (!∷ᵖ kk′~) = cong ?∷ᵖ_ (extractˣ⁻ᶜ-idempotent kk′~)

∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ : (~Γ : Ψ₁ ⍮ Ψ₀ ~ˣ Γ) →
                    A ~ᵀ S →
                    (u< : u ℕ.< length Ψ₁) →
                    u DP.⦂ A ∈ Ψ₁ →
                    ------------------------------------------
                    idxˣ⁻ᶜ (eraseˣ ~Γ) u< ⦂[ cMode ] `↑ S ∈ Γ
∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈                 (?∷ᵖ ~Γ) ~S u<       u∈            = there unusable (∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ ~Γ ~S u< u∈)
∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈             (_   !∷ᵖ ~Γ) ~S u<       u∈            = there (weakening _) (∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ ~Γ ~S u< u∈)
∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ {u = zero}  (~S′ !∷ᶜ ~Γ) ~S (s≤s u<) DP.here
  rewrite ~ᵀ-det ~S′ ~S                                              = here (is-all-del² _)
∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ {u = suc _} (_   !∷ᶜ ~Γ) ~S (s≤s u<) (DP.there u∈) = there (weakening _) (∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ ~Γ ~S u< u∈)

idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ : (~Γ : Ψ₁ ⍮ Ψ₀ ~ˣ Γ) →
                    A ~ᵀ S →
                    (u< : u ℕ.< length Ψ₁) →
                    idxˣ⁻ᶜ (eraseˣ ~Γ) u< ⦂[ cMode ] `↑ S ∈ Γ →
                    --------------------------------------------
                    u DP.⦂ A ∈ Ψ₁
idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ             (~S′ !∷ᵖ ~Γ) ~S u<       (there _ u∈) = idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ ~Γ ~S u< u∈
idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ                 (?∷ᵖ ~Γ) ~S u<       (there _ u∈) = idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ ~Γ ~S u< u∈
idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ {u = zero}  (~S′ !∷ᶜ ~Γ) ~S (s≤s u<) (here _)
  rewrite ~ᵀ-inj ~S′ ~S                                             = DP.here
idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ {u = suc _} (~S′ !∷ᶜ ~Γ) ~S (s≤s u<) (there _ u∈) = DP.there (idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ ~Γ ~S u< u∈)

∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ : (~Γ : Ψ₁ ⍮ Ψ₀ ~ˣ Γ) →
                    A ~ᵀ S →
                    (x< : x ℕ.< length Ψ₀) →
                    x DP.⦂ A ∈ Ψ₀ →
                    ---------------------------------------
                    idxˣ⁻ᵖ (eraseˣ ~Γ) x< ⦂[ pMode ] S ∈ Γ
∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈             (_   !∷ᶜ ~Γ) ~S x<       x∈            = there (weakening _) (∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ ~Γ ~S x< x∈)
∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈                 (?∷ᵖ ~Γ) ~S x<       x∈            = there unusable (∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ ~Γ ~S x< x∈)
∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ {x = zero}  (~S′ !∷ᵖ ~Γ) ~S (s≤s x<) DP.here
  rewrite ~ᵀ-det ~S′ ~S                                              = here (is-all-del² _)
∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ {x = suc _} (_   !∷ᵖ ~Γ) ~S (s≤s x<) (DP.there x∈) = there (weakening _) (∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ ~Γ ~S x< x∈)

idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ : (~Γ : Ψ₁ ⍮ Ψ₀ ~ˣ Γ) →
                    A ~ᵀ S →
                    (x< : x ℕ.< length Ψ₀) →
                    idxˣ⁻ᵖ (eraseˣ ~Γ) x< ⦂[ pMode ] S ∈ Γ →
                    -----------------------------------------
                    x DP.⦂ A ∈ Ψ₀
idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ             (_   !∷ᶜ ~Γ) ~S x<       (there _ x∈) = idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ ~Γ ~S x< x∈
idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ                 (?∷ᵖ ~Γ) ~S x<       (there _ x∈) = idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ ~Γ ~S x< x∈
idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ {x = zero}  (~S′ !∷ᵖ ~Γ) ~S (s≤s x<) (here _)
  rewrite ~ᵀ-inj ~S′ ~S                                             = DP.here
idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ {x = suc _} (_   !∷ᵖ ~Γ) ~S (s≤s x<) (there _ x∈) = DP.there (idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ ~Γ ~S x< x∈)

<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) →
                       (u< : u ℕ.< k) (u<′ : u ℕ.< k + k″) →
                       ----------------------------------------------
                       idxˣ⁻ᶜ kk′~ u< ≡ idxˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) u<′
<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻             (?∷ᵖ kk′~) k″k‴~ u<        u<′       = cong suc (<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u< u<′)
<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻             (!∷ᵖ kk′~) k″k‴~ u<        u<′       = cong suc (<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u< u<′)
<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ {u = zero}  (!∷ᶜ kk′~) k″k‴~ (s≤s u<)  (s≤s u<′) = refl
<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ {u = suc _} (!∷ᶜ kk′~) k″k‴~ (s≤s u<)  (s≤s u<′) = cong suc (<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u< u<′)

idxˣ⁻ᶜ-<-irrelevant : (kk′~ : k ⍮ k′ ~ˣ⁻) →
                      (u< : u ℕ.< k) (u<′ : u ℕ.< k) →
                      ---------------------------------
                      idxˣ⁻ᶜ kk′~ u< ≡ idxˣ⁻ᶜ kk′~ u<′
idxˣ⁻ᶜ-<-irrelevant             (?∷ᵖ kk′~) u<        u<′      = cong suc (idxˣ⁻ᶜ-<-irrelevant kk′~ u< u<′)
idxˣ⁻ᶜ-<-irrelevant             (!∷ᵖ kk′~) u<        u<′      = cong suc (idxˣ⁻ᶜ-<-irrelevant kk′~ u< u<′)
idxˣ⁻ᶜ-<-irrelevant {u = zero}  (!∷ᶜ kk′~) (s≤s u<) (s≤s u<′) = refl
idxˣ⁻ᶜ-<-irrelevant {u = suc u} (!∷ᶜ kk′~) (s≤s u<) (s≤s u<′) = cong suc (idxˣ⁻ᶜ-<-irrelevant kk′~ u< u<′)

idxˣ⁻ᶜ-<-irrelevant′ : (kk′~ : k ⍮ k′ ~ˣ⁻) →
                       (u< : u ℕ.< k) (u′< : u′ ℕ.< k) →
                       u ≡ u′ →
                       ----------------------------------
                       idxˣ⁻ᶜ kk′~ u< ≡ idxˣ⁻ᶜ kk′~ u′<
idxˣ⁻ᶜ-<-irrelevant′ kk′~ u< u′< refl = idxˣ⁻ᶜ-<-irrelevant kk′~ u< u′<

idxˣ⁻ᶜ<lengthˣ⁻ : (kk′~ : k ⍮ k′ ~ˣ⁻) →
                  (u< : u ℕ.< k) →
                  ---------------------------------
                  idxˣ⁻ᶜ kk′~ u< ℕ.< lengthˣ⁻ kk′~
idxˣ⁻ᶜ<lengthˣ⁻             (?∷ᵖ kk′~) u<       = s≤s (idxˣ⁻ᶜ<lengthˣ⁻ kk′~ u<)
idxˣ⁻ᶜ<lengthˣ⁻             (!∷ᵖ kk′~) u<       = s≤s (idxˣ⁻ᶜ<lengthˣ⁻ kk′~ u<)
idxˣ⁻ᶜ<lengthˣ⁻ {u = zero}  (!∷ᶜ kk′~) (s≤s u<) = s≤s z≤n
idxˣ⁻ᶜ<lengthˣ⁻ {u = suc u} (!∷ᶜ kk′~) (s≤s u<) = s≤s (idxˣ⁻ᶜ<lengthˣ⁻ kk′~ u<)

≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) →
                                u ℕ.≥ k →
                                (u<′ : u ℕ.< k + k″) (u<″ : u ∸ k ℕ.< k″) →
                                ----------------------------------------------------------------
                                lengthˣ⁻ kk′~ + idxˣ⁻ᶜ k″k‴~ u<″ ≡ idxˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) u<′
≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻             []         k″k‴~ u≥       u<′       u<″ = idxˣ⁻ᶜ-<-irrelevant k″k‴~ u<″ u<′
≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻             (?∷ᵖ kk′~) k″k‴~ u≥       u<′       u<″ = cong suc (≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u≥ u<′ u<″)
≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻             (!∷ᵖ kk′~) k″k‴~ u≥       u<′       u<″ = cong suc (≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u≥ u<′ u<″)
≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ {u = suc u} (!∷ᶜ kk′~) k″k‴~ (s≤s u≥) (s≤s u<′) u<″ = cong suc (≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u≥ u<′ u<″)

idxˣ⁻ᵖ<lengthˣ⁻ : (kk′~ : k ⍮ k′ ~ˣ⁻) →
                  (x< : x ℕ.< k′) →
                  ---------------------------------
                  idxˣ⁻ᵖ kk′~ x< ℕ.< lengthˣ⁻ kk′~
idxˣ⁻ᵖ<lengthˣ⁻             (!∷ᶜ kk′~) x<       = s≤s (idxˣ⁻ᵖ<lengthˣ⁻ kk′~ x<)
idxˣ⁻ᵖ<lengthˣ⁻             (?∷ᵖ kk′~) x<       = s≤s (idxˣ⁻ᵖ<lengthˣ⁻ kk′~ x<)
idxˣ⁻ᵖ<lengthˣ⁻ {x = zero}  (!∷ᵖ kk′~) (s≤s x<) = s≤s z≤n
idxˣ⁻ᵖ<lengthˣ⁻ {x = suc u} (!∷ᵖ kk′~) (s≤s x<) = s≤s (idxˣ⁻ᵖ<lengthˣ⁻ kk′~ x<)

<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) →
                       (x< : x ℕ.< k′) (x<′ : x ℕ.< k′ + k‴) →
                       ----------------------------------------------
                       idxˣ⁻ᵖ kk′~ x< ≡ idxˣ⁻ᵖ (kk′~ ++ˣ⁻ k″k‴~) x<′
<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻             (!∷ᶜ kk′~) k″k‴~ x<        x<′       = cong suc (<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x< x<′)
<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻             (?∷ᵖ kk′~) k″k‴~ x<        x<′       = cong suc (<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x< x<′)
<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ {x = zero}  (!∷ᵖ kk′~) k″k‴~ (s≤s x<)  (s≤s x<′) = refl
<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ {x = suc _} (!∷ᵖ kk′~) k″k‴~ (s≤s x<)  (s≤s x<′) = cong suc (<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x< x<′)

idxˣ⁻ᵖ-<-irrelevant : (kk′~ : k ⍮ k′ ~ˣ⁻) →
                      (x< : x ℕ.< k′) (x<′ : x ℕ.< k′) →
                      -----------------------------------
                      idxˣ⁻ᵖ kk′~ x< ≡ idxˣ⁻ᵖ kk′~ x<′
idxˣ⁻ᵖ-<-irrelevant             (!∷ᶜ kk′~) x<        x<′      = cong suc (idxˣ⁻ᵖ-<-irrelevant kk′~ x< x<′)
idxˣ⁻ᵖ-<-irrelevant             (?∷ᵖ kk′~) x<        x<′      = cong suc (idxˣ⁻ᵖ-<-irrelevant kk′~ x< x<′)
idxˣ⁻ᵖ-<-irrelevant {x = zero}  (!∷ᵖ kk′~) (s≤s x<) (s≤s x<′) = refl
idxˣ⁻ᵖ-<-irrelevant {x = suc u} (!∷ᵖ kk′~) (s≤s x<) (s≤s x<′) = cong suc (idxˣ⁻ᵖ-<-irrelevant kk′~ x< x<′)

idxˣ⁻ᵖ-<-irrelevant′ : (kk′~ : k ⍮ k′ ~ˣ⁻) →
                       (x< : x ℕ.< k′) (x′< : x′ ℕ.< k′) →
                       x ≡ x′ →
                       ------------------------------------
                       idxˣ⁻ᵖ kk′~ x< ≡ idxˣ⁻ᵖ kk′~ x′<
idxˣ⁻ᵖ-<-irrelevant′ kk′~ x< x′< refl = idxˣ⁻ᵖ-<-irrelevant kk′~ x< x′<

≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) →
                                x ℕ.≥ k′ →
                                (x<′ : x ℕ.< k′ + k‴) (x<″ : x ∸ k′ ℕ.< k‴) →
                                ----------------------------------------------------------------
                                lengthˣ⁻ kk′~ + idxˣ⁻ᵖ k″k‴~ x<″ ≡ idxˣ⁻ᵖ (kk′~ ++ˣ⁻ k″k‴~) x<′
≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻             []         k″k‴~ x≥       x<′       x<″ = idxˣ⁻ᵖ-<-irrelevant k″k‴~ x<″ x<′
≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻             (!∷ᶜ kk′~) k″k‴~ x≥       x<′       x<″ = cong suc (≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x≥ x<′ x<″)
≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻             (?∷ᵖ kk′~) k″k‴~ x≥       x<′       x<″ = cong suc (≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x≥ x<′ x<″)
≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ {x = suc u} (!∷ᵖ kk′~) k″k‴~ (s≤s x≥) (s≤s x<′) x<″ = cong suc (≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x≥ x<′ x<″)

∤-extractˣᶜ : (~Γ : Ψ₁ ⍮ Ψ₀ ~ˣ Γ) →
              Γ ∤[ cMode ] Γ′ →
              --------------------------
              Γ′ ≡ proj₁ (extractˣᶜ ~Γ)
∤-extractˣᶜ []         []                     = refl
∤-extractˣᶜ (_ !∷ᶜ ~Γ) (delete ≰cMode _ ∷ Γ∤) with () ← ≰cMode refl
∤-extractˣᶜ (_ !∷ᶜ ~Γ) (keep   _        ∷ Γ∤) = cong (_ ∷_) (∤-extractˣᶜ ~Γ Γ∤)
∤-extractˣᶜ   (?∷ᵖ ~Γ) (delete ≰cMode _ ∷ Γ∤) = cong (_ ∷_) (∤-extractˣᶜ ~Γ Γ∤)
∤-extractˣᶜ (_ !∷ᵖ ~Γ) (delete ≰cMode _ ∷ Γ∤) = cong (_ ∷_) (∤-extractˣᶜ ~Γ Γ∤)

-- Properties of _~ᴹ_
--
~ᴹ⇒++ˣ⁻~ᴹ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) →
            kk′~ ⊢ E ~ᴹ L →
            --------------------------------------------
            kk′~ ++ˣ⁻ k″k‴~ ⊢ E ~ᴹ L
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ `unit                                      = `unit
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`box ~L)
  with ~L′ ← ~ᴹ⇒++ˣ⁻~ᴹ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k″k‴~) ~L
    rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~)                    = `box ~L′
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`let-box ~L `in ~M)                       = `let-box (~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ ~L) `in (~ᴹ⇒++ˣ⁻~ᴹ (!∷ᶜ kk′~) k″k‴~ ~M)
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`#¹ u<)
  rewrite <⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u< (ℕ.m≤n⇒m≤n+o _ u<) = `#¹ (ℕ.m≤n⇒m≤n+o _ u<)
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`λ⦂ S~ ∙ ~L)                              = `λ⦂ S~ ∙ ~ᴹ⇒++ˣ⁻~ᴹ (!∷ᵖ kk′~) k″k‴~ ~L
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (~L `$ ~M)                                 = ~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ ~L `$ ~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ ~M
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`#⁰ x<)
  rewrite <⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x< (ℕ.m≤n⇒m≤n+o _ x<) = `#⁰ (ℕ.m≤n⇒m≤n+o _ x<)
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`unlift-`lift ~L)
  with ~L′ ← ~ᴹ⇒++ˣ⁻~ᴹ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k″k‴~) ~L
    rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~)                    = `unlift-`lift ~L′

extractˣ⁻ᶜ⁻¹-~ᴹ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) →
                  kk′~ ++ˣ⁻ extractˣ⁻ᶜ k″k‴~ ⊢ E ~ᴹ L →
                  --------------------------------------------
                  kk′~ ++ˣ⁻ k″k‴~ ⊢ E ~ᴹ L
extractˣ⁻ᶜ⁻¹-~ᴹ          kk′~ k″k‴~ `unit                           = `unit
extractˣ⁻ᶜ⁻¹-~ᴹ          kk′~ k″k‴~ (`box ~L)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ (extractˣ⁻ᶜ k″k‴~)
    with ~L′ ← extractˣ⁻ᶜ⁻¹-~ᴹ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k″k‴~) ~L
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~)                      = `box ~L′
extractˣ⁻ᶜ⁻¹-~ᴹ          kk′~ k″k‴~ (`let-box ~L `in ~M)            = `let-box extractˣ⁻ᶜ⁻¹-~ᴹ kk′~ k″k‴~ ~L `in extractˣ⁻ᶜ⁻¹-~ᴹ (!∷ᶜ kk′~) k″k‴~ ~M
extractˣ⁻ᶜ⁻¹-~ᴹ          kk′~ k″k‴~ (`#¹ u<)
  rewrite idxˣ⁻ᶜ-extractˣ⁻ᶜ (kk′~ ++ˣ⁻ extractˣ⁻ᶜ k″k‴~) u<
        | extractˣ⁻ᶜ-++ˣ⁻ kk′~ (extractˣ⁻ᶜ k″k‴~)
        | extractˣ⁻ᶜ-idempotent k″k‴~
        | sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~)
        | sym (idxˣ⁻ᶜ-extractˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) u<)              = `#¹ u<
extractˣ⁻ᶜ⁻¹-~ᴹ          kk′~ k″k‴~ (`λ⦂ ~S ∙ ~L)                   = `λ⦂ ~S ∙ extractˣ⁻ᶜ⁻¹-~ᴹ (!∷ᵖ kk′~) k″k‴~ ~L
extractˣ⁻ᶜ⁻¹-~ᴹ          kk′~ k″k‴~ (~L `$ ~M)                      = extractˣ⁻ᶜ⁻¹-~ᴹ kk′~ k″k‴~ ~L `$ extractˣ⁻ᶜ⁻¹-~ᴹ kk′~ k″k‴~ ~M
extractˣ⁻ᶜ⁻¹-~ᴹ {_} {k′} kk′~ k″k‴~ (`#⁰_ {x = x} x<)
  with x<′ ← subst (x ℕ.<_) (ℕ.+-identityʳ k′) x<
    rewrite sym (<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ (extractˣ⁻ᶜ k″k‴~) x<′ x<)
          | <⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x<′ (ℕ.m≤n⇒m≤n+o _ x<′) = `#⁰ ℕ.m≤n⇒m≤n+o _ x<′
extractˣ⁻ᶜ⁻¹-~ᴹ          kk′~ k″k‴~ (`unlift-`lift ~L)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ (extractˣ⁻ᶜ k″k‴~)
    with ~L′ ← extractˣ⁻ᶜ⁻¹-~ᴹ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k″k‴~) ~L
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~)                      = `unlift-`lift ~L′

extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) →
                          (~L : kk′~ ++ˣ⁻ extractˣ⁻ᶜ k″k‴~ ⊢ E ~ᴹ L) →
                          -----------------------------------------------------
                          depth~ᴹ (extractˣ⁻ᶜ⁻¹-~ᴹ kk′~ k″k‴~ ~L) ≡ depth~ᴹ ~L
extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ          kk′~ k″k‴~ `unit                   = refl
extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ          kk′~ k″k‴~ (`box ~L)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ (extractˣ⁻ᶜ k″k‴~)
    with ~L′ ← extractˣ⁻ᶜ⁻¹-~ᴹ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k″k‴~) ~L
       | eq ← extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ  (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k″k‴~) ~L
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~)                      = cong suc eq
extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ          kk′~ k″k‴~ (`let-box ~L `in ~M)    = cong suc
                                                                        (cong₂ ℕ._⊔_
                                                                          (extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ kk′~ k″k‴~ ~L)
                                                                          (extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ (!∷ᶜ kk′~) k″k‴~ ~M))
extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ          kk′~ k″k‴~ (`#¹ u<)
  rewrite idxˣ⁻ᶜ-extractˣ⁻ᶜ (kk′~ ++ˣ⁻ extractˣ⁻ᶜ k″k‴~) u<
        | extractˣ⁻ᶜ-++ˣ⁻ kk′~ (extractˣ⁻ᶜ k″k‴~)
        | extractˣ⁻ᶜ-idempotent k″k‴~
        | sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~)
        | sym (idxˣ⁻ᶜ-extractˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) u<)              = refl
extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ          kk′~ k″k‴~ (`λ⦂ ~S ∙ ~L)           = cong suc (extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ (!∷ᵖ kk′~) k″k‴~ ~L)
extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ          kk′~ k″k‴~ (~L `$ ~M)              = cong suc
                                                                        (cong₂ ℕ._⊔_
                                                                          (extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ kk′~ k″k‴~ ~L)
                                                                          (extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ kk′~ k″k‴~ ~M))
extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ {_} {k′} kk′~ k″k‴~ (`#⁰_ {x = x} x<)
  with x<′ ← subst (x ℕ.<_) (ℕ.+-identityʳ k′) x<
    rewrite sym (<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ (extractˣ⁻ᶜ k″k‴~) x<′ x<)
          | <⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x<′ (ℕ.m≤n⇒m≤n+o _ x<′) = refl
extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ          kk′~ k″k‴~ (`unlift-`lift ~L)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ (extractˣ⁻ᶜ k″k‴~)
    with ~L′ ← extractˣ⁻ᶜ⁻¹-~ᴹ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k″k‴~) ~L
       | eq ← extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k″k‴~) ~L
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~)                      = cong suc eq

-- Properties of _~ᴹ_ Regarding Typings
--
~ᴹ∧++⊢⇒⊢-helper : {kk′~ : length Ψ₁ ⍮ length Ψ₀₀ ~ˣ⁻} →
                  (~L : kk′~ ⊢ E ~ᴹ L) →
                  Ψ₁ DP.⍮ Ψ₀₀ ++ Ψ₀₁ ⊢ E ⦂ B →
                  Acc ℕ._<_ (depth~ᴹ ~L) →
                  --------------------------------------
                  Ψ₁ DP.⍮ Ψ₀₀ ⊢ E ⦂ B
~ᴹ∧++⊢⇒⊢-helper `unit                DP.`unit                rec     = DP.`unit
~ᴹ∧++⊢⇒⊢-helper (`box ~L)            (DP.`box ⊢E)            rec     = DP.`box ⊢E
~ᴹ∧++⊢⇒⊢-helper (`let-box ~L `in ~M) (DP.`let-box ⊢E `in ⊢F) (acc r) = DP.`let-box ~ᴹ∧++⊢⇒⊢-helper ~L ⊢E (r (s≤s (ℕ.m≤m⊔n _ _))) `in ~ᴹ∧++⊢⇒⊢-helper ~M ⊢F (r (s≤s (ℕ.m≤n⊔m _ _)))
~ᴹ∧++⊢⇒⊢-helper (`#¹ u<)             (DP.`#¹ u∈)             rec     = DP.`#¹ u∈
~ᴹ∧++⊢⇒⊢-helper (`λ⦂ ~S ∙ ~L)        (DP.`λ⦂-∙ ⊢E)           (acc r) = DP.`λ⦂-∙ (~ᴹ∧++⊢⇒⊢-helper ~L ⊢E (r (ℕ.n<1+n _)))
~ᴹ∧++⊢⇒⊢-helper (~L `$ ~M)           (⊢E DP.`$ ⊢F)           (acc r) = ~ᴹ∧++⊢⇒⊢-helper ~L ⊢E (r (s≤s (ℕ.m≤m⊔n _ _))) DP.`$ ~ᴹ∧++⊢⇒⊢-helper ~M ⊢F (r (s≤s (ℕ.m≤n⊔m _ _)))
~ᴹ∧++⊢⇒⊢-helper (`#⁰ x<)             (DP.`#⁰ x∈)             rec     = DP.`#⁰ DP.>∈-++⇒∈ _ x< x∈
~ᴹ∧++⊢⇒⊢-helper (`unlift-`lift ~L)   ⊢E                      (acc r) = ~ᴹ∧++⊢⇒⊢-helper
                                                                         (extractˣ⁻ᶜ⁻¹-~ᴹ [] _ ~L)
                                                                         ⊢E
                                                                         (r (subst (ℕ._< suc (depth~ᴹ ~L)) (sym (extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ [] _ ~L)) (ℕ.n<1+n _)))

~ᴹ∧++⊢⇒⊢ : {kk′~ : length Ψ₁ ⍮ length Ψ₀₀ ~ˣ⁻} →
           kk′~ ⊢ E ~ᴹ L →
           Ψ₁ DP.⍮ Ψ₀₀ ++ Ψ₀₁ ⊢ E ⦂ B →
           --------------------------------------
           Ψ₁ DP.⍮ Ψ₀₀ ⊢ E ⦂ B
~ᴹ∧++⊢⇒⊢ ~L ⊢E = ~ᴹ∧++⊢⇒⊢-helper ~L ⊢E (ℕ.<-wellFounded _)

~ᴹ∧⊢⇒~ᵀ : (~Γ : Ψ₁ ⍮ Ψ₀ ~ˣ Γ) →
          eraseˣ ~Γ ⊢ E ~ᴹ L →
          Γ ⊢[ pMode ] L ⦂ S →
          ∃ (λ A → A ~ᵀ S)
~ᴹ∧⊢⇒~ᵀ ~Γ `unit                (`unit _)                                     = -, `⊤
~ᴹ∧⊢⇒~ᵀ ~Γ (`box ~L)            (Γ∤ ⊢`return`lift ⊢L)
  rewrite extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ
        | ∤-extractˣᶜ ~Γ Γ∤                                                   = -, `□ (proj₂ (~ᴹ∧⊢⇒~ᵀ (proj₂ (extractˣᶜ ~Γ)) ~L ⊢L))
~ᴹ∧⊢⇒~ᵀ ~Γ (`let-box ~L `in ~M) (Γ~ & Γ₀∤ ⊢`let-return ⊢L ⦂ ⊢↓ `in ⊢M)
  rewrite ∤-det (∤ᵖ _) Γ₀∤
    with _ , `□ ~T ← ~ᴹ∧⊢⇒~ᵀ ~Γ ~L (~⊞-is-all-del∧⊢⇒⊢ˡ Γ~ (is-all-del² _) ⊢L) = ~ᴹ∧⊢⇒~ᵀ (~T !∷ᶜ ~Γ) ~M (~⊞-is-all-del∧⊢⇒⊢ʳ (contraction _ ∷ Γ~) (is-all-del² _) ⊢M)
~ᴹ∧⊢⇒~ᵀ ~Γ (`#¹ u<)             (Γ∤ ⊢`unlift`# u∈ ⦂ ⊢↑)
  rewrite ∤-extractˣᶜ ~Γ Γ∤                                                   = ∈ᶜ⇒~ᵀ (proj₂ (extractˣᶜ ~Γ)) u∈ 
~ᴹ∧⊢⇒~ᵀ ~Γ (`λ⦂ ~S ∙ ~L)        (`λ⦂-∘ ⊢L)                                    = -, ~S `→ (proj₂ (~ᴹ∧⊢⇒~ᵀ (~S !∷ᵖ ~Γ) ~L ⊢L))
~ᴹ∧⊢⇒~ᵀ ~Γ (~L `$ ~M)           (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with _ , _ `→ ~S ← ~ᴹ∧⊢⇒~ᵀ ~Γ ~L (~⊞-is-all-del∧⊢⇒⊢ˡ Γ~ (is-all-del² _) ⊢L) = -, ~S
~ᴹ∧⊢⇒~ᵀ ~Γ (`#⁰ x<)             (`# x∈)                                       = ∈ᵖ⇒~ᵀ ~Γ x∈
~ᴹ∧⊢⇒~ᵀ ~Γ (`unlift-`lift ~L)   (Γ∤ ⊢`unlift`lift ⊢L ⦂ ⊢↑)
  rewrite extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ
        | ∤-extractˣᶜ ~Γ Γ∤                                                   = ~ᴹ∧⊢⇒~ᵀ (proj₂ (extractˣᶜ ~Γ)) ~L ⊢L

-- Soundness and Completeness of _~ᴹ_ Regarding Typings
--
~ᴹ-soundness : (~Γ : Ψ₁ ⍮ Ψ₀ ~ˣ Γ) →
               A ~ᵀ S →
               eraseˣ ~Γ ⊢ E ~ᴹ L →
               Ψ₁ DP.⍮ Ψ₀ ⊢ E ⦂ A →
               -----------------------
               Γ ⊢[ pMode ] L ⦂ S
~ᴹ-soundness ~Γ ~S          (`let-box ~L `in ~M) (DP.`let-box_`in_ {B = B} ⊢E ⊢F)
  with _ , ~T ← ~ᵀ-total B                                                        = ~⊞² _ & ∤ᵖ _ ⊢`let-return ~ᴹ-soundness ~Γ (`□ ~T) ~L ⊢E  ⦂ ⊢`↓ (λ ()) (⊢`↑ (λ ()) (~ᵀ⇒⊢ ~T)) `in ~ᴹ-soundness (~T !∷ᶜ ~Γ) ~S ~M ⊢F
~ᴹ-soundness ~Γ ~S          (`#¹ u<)             (DP.`#¹ u∈)
  with _ , ~Γ′ ← extractˣᶜ ~Γ
     | ∤Γ′ ← extractˣᶜ-∤ ~Γ
     | eq ← idxˣ⁻ᶜ-extractˣᶜ-eraseˣ ~Γ u<                                         = ∤Γ′ ⊢`unlift`# subst (_⦂[ _ ] _ ∈ _) (sym eq) (∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ ~Γ′ ~S u< u∈) ⦂ (⊢`↑ (λ ()) (~ᵀ⇒⊢ ~S))
~ᴹ-soundness ~Γ (~S′ `→ ~T) (`λ⦂ ~S ∙ ~L)        (DP.`λ⦂-∙ ⊢E)
  with refl ← ~ᵀ-det ~S′ ~S                                                       = `λ⦂-∘ ~ᴹ-soundness (~S !∷ᵖ ~Γ) ~T ~L ⊢E
~ᴹ-soundness ~Γ ~S          (~L `$ ~M)           (DP._`$_ {B = B} ⊢E ⊢F)
  with _ , ~T ← ~ᵀ-total B                                                        = ~⊞² _ ⊢ ~ᴹ-soundness ~Γ (~T `→ ~S) ~L ⊢E ⦂ ⊢ ~ᵀ⇒⊢ ~T `⊸ ~ᵀ⇒⊢ ~S `$ ~ᴹ-soundness ~Γ ~T ~M ⊢F
~ᴹ-soundness ~Γ ~S          (`#⁰ x<)             (DP.`#⁰ x∈)                      = `# ∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ ~Γ ~S x< x∈
~ᴹ-soundness ~Γ ~S          (`unlift-`lift ~L)   ⊢E
  with _ , ~Γ′ ← extractˣᶜ ~Γ
     | ∤Γ′ ← extractˣᶜ-∤ ~Γ
     | eq ← extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ                                        = ∤Γ′ ⊢`unlift`lift (~ᴹ-soundness ~Γ′ ~S (subst (_⊢ _ ~ᴹ _) eq ~L) (~ᴹ∧++⊢⇒⊢ ~L ⊢E)) ⦂ (⊢`↑ (λ ()) (~ᵀ⇒⊢ ~S))
~ᴹ-soundness ~Γ `⊤          `unit                DP.`unit                         = `unit (is-all-del² _)
~ᴹ-soundness ~Γ (`□ ~S)     (`box ~L)            (DP.`box ⊢E)
  with _ , ~Γ′ ← extractˣᶜ ~Γ
     | ∤Γ′ ← extractˣᶜ-∤ ~Γ
     | eq ← extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ                                        = ∤Γ′ ⊢`return`lift (~ᴹ-soundness ~Γ′ ~S (subst (_⊢ _ ~ᴹ _) eq ~L) ⊢E)

~ᴹ-completeness : (~Γ : Ψ₁ ⍮ Ψ₀ ~ˣ Γ) →
                  A ~ᵀ S →
                  eraseˣ ~Γ ⊢ E ~ᴹ L →
                  Γ ⊢[ pMode ] L ⦂ S →
                  -----------------------
                  Ψ₁ DP.⍮ Ψ₀ ⊢ E ⦂ A
~ᴹ-completeness ~Γ ~S          (`let-box ~L `in ~M) (Γ~ & Γ₀∤ ⊢`let-return ⊢L ⦂ ⊢↓ `in ⊢M)
  rewrite ∤-det (∤ᵖ _) Γ₀∤
    with ⊢L′ ← ~⊞-is-all-del∧⊢⇒⊢ˡ Γ~ (is-all-del² _) ⊢L
      with _ , `□ ~T ← ~ᴹ∧⊢⇒~ᵀ ~Γ ~L ⊢L′                                             = DP.`let-box ~ᴹ-completeness ~Γ (`□ ~T) ~L ⊢L′ `in ~ᴹ-completeness (~T !∷ᶜ ~Γ) ~S ~M (~⊞-is-all-del∧⊢⇒⊢ʳ (contraction _ ∷ Γ~) (is-all-del² _) ⊢M)
~ᴹ-completeness ~Γ ~S          (`#¹ u<)             (Γ∤ ⊢`unlift`# u∈ ⦂ ⊢↑)
  rewrite idxˣ⁻ᶜ-extractˣᶜ-eraseˣ ~Γ u<
        | ∤-extractˣᶜ ~Γ Γ∤                                                          = DP.`#¹ idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ (proj₂ (extractˣᶜ ~Γ)) ~S u< u∈ 
~ᴹ-completeness ~Γ (~S′ `→ ~T) (`λ⦂ ~S ∙ ~L)        (`λ⦂-∘ ⊢L)
  with refl ← ~ᵀ-inj ~S ~S′                                                          = DP.`λ⦂-∙ ~ᴹ-completeness (~S !∷ᵖ ~Γ) ~T ~L ⊢L
~ᴹ-completeness ~Γ ~S          (~L `$ ~M)           (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with ⊢L′ ← ~⊞-is-all-del∧⊢⇒⊢ˡ Γ~ (is-all-del² _) ⊢L
    with _ , ~⊸@(~T `→ ~S′) ← ~ᴹ∧⊢⇒~ᵀ ~Γ ~L ⊢L′
      with refl ← ~ᵀ-inj ~S ~S′                                                      = ~ᴹ-completeness ~Γ ~⊸ ~L ⊢L′ DP.`$ ~ᴹ-completeness ~Γ ~T ~M (~⊞-is-all-del∧⊢⇒⊢ʳ Γ~ (is-all-del² _) ⊢M)
~ᴹ-completeness ~Γ ~S          (`#⁰ x<)             (`# x∈)                          = DP.`#⁰ idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ ~Γ ~S x< x∈
~ᴹ-completeness ~Γ ~S          (`unlift-`lift ~L)   (Γ∤ ⊢`unlift`lift ⊢L ⦂ ⊢↑)
  rewrite extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ
        | ∤-extractˣᶜ ~Γ Γ∤                                                          = DP.⊢⇒++⊢ _ (~ᴹ-completeness (proj₂ (extractˣᶜ ~Γ)) ~S ~L ⊢L)
~ᴹ-completeness ~Γ `⊤          `unit                (`unit _)                        = DP.`unit
~ᴹ-completeness ~Γ (`□ ~S)     (`box ~L)            (Γ∤ ⊢`return`lift ⊢L)
  rewrite extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ
        | ∤-extractˣᶜ ~Γ Γ∤                                                          = DP.`box (~ᴹ-completeness (proj₂ (extractˣᶜ ~Γ)) ~S ~L ⊢L)


-- Properties of _~ᴹ_ Regarding OpSems
--
⟶[≤]-preserves-~ᴹ : kk′~ ⊢ E ~ᴹ L →
                    L ⟶[ cMode ≤] L′ →
                    -------------------
                    kk′~ ⊢ E ~ᴹ L′
⟶[≤]-preserves-~ᴹ (`box ~L)            (ξ-`return[≰ ≰cMode ⇒-] L⟶[≤]) with () ← ≰cMode refl
⟶[≤]-preserves-~ᴹ (`box ~L)            (ξ-`return≤`lift L⟶[≤])        = `box (⟶[≤]-preserves-~ᴹ ~L L⟶[≤])
⟶[≤]-preserves-~ᴹ (`let-box ~L `in ~M) ξ-`let-return[ c≰p ] L⟶[≤] `in?       = `let-box (⟶[≤]-preserves-~ᴹ ~L L⟶[≤]) `in ~M
⟶[≤]-preserves-~ᴹ (`let-box ~L `in ~M) (ξ-`let-return![ c≰p ] WL `in M⟶[≤])  = `let-box ~L `in ⟶[≤]-preserves-~ᴹ ~M M⟶[≤]
⟶[≤]-preserves-~ᴹ (`λ⦂ ~S ∙ ~L)        (ξ-`λ⦂[-]-∘ L⟶[≤])             = `λ⦂ ~S ∙ ⟶[≤]-preserves-~ᴹ ~L L⟶[≤]
⟶[≤]-preserves-~ᴹ (~L `$ ~M)           ξ- L⟶[≤] `$?                   = ⟶[≤]-preserves-~ᴹ ~L L⟶[≤] `$ ~M
⟶[≤]-preserves-~ᴹ (~L `$ ~M)           (ξ-! WL `$ M⟶[≤])              = ~L `$ ⟶[≤]-preserves-~ᴹ ~M M⟶[≤]
⟶[≤]-preserves-~ᴹ (`#¹ u<)             (ξ-`unlift[≰ ≰cMode ⇒-] L⟶[≤]) with () ← ≰cMode refl
⟶[≤]-preserves-~ᴹ (`#¹ u<)             (ξ-`unlift≤ ())
⟶[≤]-preserves-~ᴹ (`unlift-`lift ~L)   (ξ-`unlift[≰ ≰cMode ⇒-] L⟶[≤]) with () ← ≰cMode refl
⟶[≤]-preserves-~ᴹ (`unlift-`lift ~L)   (ξ-`unlift≤`lift L⟶[≤])        = `unlift-`lift (⟶[≤]-preserves-~ᴹ ~L L⟶[≤])
⟶[≤]-preserves-~ᴹ (`unlift-`lift ~L)   (β-`↑ _ WL)                    = extractˣ⁻ᶜ⁻¹-~ᴹ [] _ ~L

[]⊢~ᴹ⁻¹⇒¬Neut⁰ : [] ⊢ E ~ᴹ L →
                 ---------------
                 ¬ (WeakNeut L)
[]⊢~ᴹ⁻¹⇒¬Neut⁰ (`unlift-`lift ~L)   (`unlift ())
[]⊢~ᴹ⁻¹⇒¬Neut⁰ (`let-box ~L `in ~M) (`let-return NL `in _) = []⊢~ᴹ⁻¹⇒¬Neut⁰ ~L NL
[]⊢~ᴹ⁻¹⇒¬Neut⁰ (~L `$ ~M)           (NL `$ VM)             = []⊢~ᴹ⁻¹⇒¬Neut⁰ ~L NL

[]⊢~ᴹ⁻¹-respects-Value : [] ⊢ E ~ᴹ L →
                         WeakNorm L →
                         --------------
                         DP.Value E
[]⊢~ᴹ⁻¹-respects-Value ~L            (`neut NL)        with () ← []⊢~ᴹ⁻¹⇒¬Neut⁰ ~L NL
[]⊢~ᴹ⁻¹-respects-Value `unit         `unit             = DP.`unit
[]⊢~ᴹ⁻¹-respects-Value (`box ~L)     (`return`lift WL) = DP.`box _
[]⊢~ᴹ⁻¹-respects-Value (`λ⦂ ~S ∙ ~L) (`λ⦂ᵖ S ∘ L)      = DP.`λ⦂ _ ∙ _

~ᴹ-normalize[≤] : (~L : kk′~ ⊢ E ~ᴹ L) →
                  --------------------------------------------------
                  ∃ (λ L′ → L ⟶[ cMode ≤]* L′
                          × DeferredTerm[ cMode ≤] L′
                          × Σ (kk′~ ⊢ E ~ᴹ L′)
                              (λ ~L′ → depth~ᴹ ~L′ ℕ.≤ depth~ᴹ ~L))
~ᴹ-normalize[≤] `unit                                     = -, ε
                                                          , `unit
                                                          , `unit
                                                          , z≤n
~ᴹ-normalize[≤] (`box ~L)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L = -, ξ-of-⟶[ cMode ≤]* `return`lift ξ-`return≤`lift ⟶*L′[≤]
                                                          , `return≤ (`lift WL′)
                                                          , `box ~L′
                                                          , s≤s L′≤
~ᴹ-normalize[≤] (`let-box ~L `in ~M)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
     | _ , ⟶*M′[≤] , WM′ , ~M′ , M′≤ ← ~ᴹ-normalize[≤] ~M = -, ξ-of-⟶[ cMode ≤]* (`let-return_`in _) ξ-`let-return[ c≰p ]_`in? ⟶*L′[≤]
                                                              ◅◅ ξ-of-⟶[ cMode ≤]* (`let-return _ `in_) (ξ-`let-return![ c≰p ] WL′ `in_) ⟶*M′[≤]
                                                          , `let-return[ c≰p ] WL′ `in WM′
                                                          , `let-box ~L′ `in ~M′
                                                          , s≤s (ℕ.⊔-mono-≤ L′≤ M′≤)
~ᴹ-normalize[≤] (`#¹ u<)                                  = -, ε
                                                          , `unlift≤ (`neut (`# _))
                                                          , `#¹ u<
                                                          , z≤n
~ᴹ-normalize[≤] (`λ⦂ ~S ∙ ~L)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L = -, ξ-of-⟶[ cMode ≤]* (`λ⦂ᵖ _ ∘_) ξ-`λ⦂[-]-∘_ ⟶*L′[≤]
                                                          , `λ⦂ᵖ _ ∘ WL′
                                                          , `λ⦂ ~S ∙ ~L′
                                                          , s≤s L′≤
~ᴹ-normalize[≤] (~L `$ ~M)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
     | _ , ⟶*M′[≤] , WM′ , ~M′ , M′≤ ← ~ᴹ-normalize[≤] ~M = -, ξ-of-⟶[ cMode ≤]* (_`$ _) ξ-_`$? ⟶*L′[≤]
                                                              ◅◅ ξ-of-⟶[ cMode ≤]* (_ `$_) (ξ-! WL′ `$_) ⟶*M′[≤]
                                                          , WL′ `$ WM′
                                                          , ~L′ `$ ~M′
                                                          , s≤s (ℕ.⊔-mono-≤ L′≤ M′≤)
~ᴹ-normalize[≤] (`#⁰ x<)                                  = -, ε
                                                          , `# _
                                                          , `#⁰ x<
                                                          , z≤n
~ᴹ-normalize[≤] (`unlift-`lift ~L)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L = -, ξ-of-⟶[ cMode ≤]* `unlift`lift ξ-`unlift≤`lift ⟶*L′[≤]
                                                              ◅◅ β-`↑ refl WL′ ◅ ε
                                                          , WL′
                                                          , extractˣ⁻ᶜ⁻¹-~ᴹ [] _ ~L′
                                                          , ℕ.m≤n⇒m≤1+n (subst (ℕ._≤ _) (sym (extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ [] _ ~L′)) L′≤)

Value~ᴹ-normalize-helper : (~L : kk′~ ⊢ E ~ᴹ L) →
                           DP.Value E →
                           Acc ℕ._<_ (depth~ᴹ ~L) →
                           --------------------------------------------------
                           ∃ (λ L′ → L ⟶* L′ × WeakNorm L′ × kk′~ ⊢ E ~ᴹ L′)
Value~ᴹ-normalize-helper `unit              VE rec                            = -, ε , `unit , `unit
Value~ᴹ-normalize-helper (`box ~L)          VE (acc r)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , _ ← ~ᴹ-normalize[≤] ~L                       = -, ξ-of-↝*-⟶* _⟶[ _ ≤]_ `return`lift ξ-`return`lift ⟶*L′[≤]
                                                                              , `return`lift WL′
                                                                              , `box ~L′
Value~ᴹ-normalize-helper (`λ⦂ ~S ∙ ~L)      VE rec                            = -, ε , `λ⦂ᵖ _ ∘ _ , `λ⦂ ~S ∙ ~L
Value~ᴹ-normalize-helper (`unlift-`lift ~L) VE (acc r)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
    with _ , ⟶*L″ , VL″ , ~L″ ← Value~ᴹ-normalize-helper ~L′ VE (r (s≤s L′≤)) = -, ξ-of-↝*-⟶* _⟶[ cMode ≤]_ `unlift`lift ξ-`unlift`lift ⟶*L′[≤]
                                                                                  ◅◅ β-`↑ WL′ ◅ ⟶*L″
                                                                              , VL″
                                                                              , extractˣ⁻ᶜ⁻¹-~ᴹ [] _ ~L″

Value~ᴹ-normalize : kk′~ ⊢ E ~ᴹ L →
                    DP.Value E →
                    --------------------------------------------------
                    ∃ (λ L′ → L ⟶* L′ × WeakNorm L′ × kk′~ ⊢ E ~ᴹ L′)
Value~ᴹ-normalize ~L VE = Value~ᴹ-normalize-helper ~L VE (ℕ.<-wellFounded _)

`box-~ᴹ-inv-helper : (~L : kk′~ ⊢ DP.`box E ~ᴹ L) →
                     Acc ℕ._<_ (depth~ᴹ ~L) →
                     ------------------------------------
                     ∃ (λ L′ → L ⟶* `return`lift L′
                             × DeferredTerm[ cMode ≤] L′
                             × kk′~ ⊢ E ~ᴹ L′)
`box-~ᴹ-inv-helper (`box ~L)          rec
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L                = -, ξ-of-↝*-⟶* _⟶[ _ ≤]_ `return`lift ξ-`return`lift ⟶*L′[≤]
                                                                         , WL′
                                                                         , extractˣ⁻ᶜ⁻¹-~ᴹ [] _ ~L′
`box-~ᴹ-inv-helper (`unlift-`lift ~L) (acc r)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
    with _ , ⟶*`boxL″ , WL″ , ~L″ ← `box-~ᴹ-inv-helper ~L′ (r (s≤s L′≤)) = -, ξ-of-↝*-⟶* _⟶[ cMode ≤]_ `unlift`lift ξ-`unlift`lift ⟶*L′[≤]
                                                                             ◅◅ β-`↑ WL′ ◅ ⟶*`boxL″
                                                                         , WL″
                                                                         , extractˣ⁻ᶜ⁻¹-~ᴹ [] _ ~L″

`box-~ᴹ-inv : kk′~ ⊢ DP.`box E ~ᴹ L →
              ------------------------------------
              ∃ (λ L′ → L ⟶* `return`lift L′
                      × DeferredTerm[ cMode ≤] L′
                      × kk′~ ⊢ E ~ᴹ L′)
`box-~ᴹ-inv ~L = `box-~ᴹ-inv-helper ~L (ℕ.<-wellFounded _)

`λ⦂-∙-~ᴹ-inv-helper : (~L : kk′~ ⊢ DP.`λ⦂ A ∙ E ~ᴹ L) →
                      Acc ℕ._<_ (depth~ᴹ ~L) →
                      ----------------------------------
                      ∃₂ (λ S′ L′ → L ⟶* `λ⦂ᵖ S′ ∘ L′
                                  × !∷ᵖ kk′~ ⊢ E ~ᴹ L′
                                  × A ~ᵀ S′)
`λ⦂-∙-~ᴹ-inv-helper (`λ⦂ ~S ∙ ~L)      rec                                       = -, -, ε
                                                                                 , ~L
                                                                                 , ~S
`λ⦂-∙-~ᴹ-inv-helper (`unlift-`lift ~L) (acc r)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
    with _ , _ , ⟶*`λ⦂ᵖS″∘L″ , ~L″ , ~S″ ← `λ⦂-∙-~ᴹ-inv-helper ~L′ (r (s≤s L′≤)) = -, -, ξ-of-↝*-⟶* _⟶[ cMode ≤]_ `unlift`lift ξ-`unlift`lift ⟶*L′[≤]
                                                                                     ◅◅ β-`↑ WL′ ◅ ⟶*`λ⦂ᵖS″∘L″
                                                                                 , extractˣ⁻ᶜ⁻¹-~ᴹ (!∷ᵖ []) _ ~L″
                                                                                 , ~S″

`λ⦂-∙-~ᴹ-inv : kk′~ ⊢ DP.`λ⦂ A ∙ E ~ᴹ L →
               ---------------------------------
               ∃₂ (λ S′ L′ → L ⟶* `λ⦂ᵖ S′ ∘ L′
                           × !∷ᵖ kk′~ ⊢ E ~ᴹ L′
                           × A ~ᵀ S′)
`λ⦂-∙-~ᴹ-inv ~L = `λ⦂-∙-~ᴹ-inv-helper ~L (ℕ.<-wellFounded _)

wkidx[↑]-idxˣ⁻ᶜ : (kk′~ : k ⍮ k′ ~ˣ⁻) (0k₀~ : 0 ⍮ k₀ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) →
                  (u< : u ℕ.< k + k″) →
                  -------------------------------------------------------------------------------------------------------------
                  wkidx[ lengthˣ⁻ 0k₀~ ↑ lengthˣ⁻ kk′~ ] (idxˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) u<) ≡ idxˣ⁻ᶜ (kk′~ ++ˣ⁻ 0k₀~ ++ˣ⁻ k″k‴~) u<
wkidx[↑]-idxˣ⁻ᶜ             []         0k₀~ k″k‴~ u<                                               = ≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ 0k₀~ k″k‴~ z≤n u< u<
wkidx[↑]-idxˣ⁻ᶜ             (?∷ᵖ kk′~) 0k₀~ k″k‴~ u<
  rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) u<) = cong suc (wkidx[↑]-idxˣ⁻ᶜ kk′~ 0k₀~ k″k‴~ u<)
wkidx[↑]-idxˣ⁻ᶜ             (!∷ᵖ kk′~) 0k₀~ k″k‴~ u<
  rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) u<) = cong suc (wkidx[↑]-idxˣ⁻ᶜ kk′~ 0k₀~ k″k‴~ u<)
wkidx[↑]-idxˣ⁻ᶜ {u = zero}  (!∷ᶜ kk′~) 0k₀~ k″k‴~ (s≤s u<)                                         = refl
wkidx[↑]-idxˣ⁻ᶜ {u = suc u} (!∷ᶜ kk′~) 0k₀~ k″k‴~ (s≤s u<)
  rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) u<) = cong suc (wkidx[↑]-idxˣ⁻ᶜ kk′~ 0k₀~ k″k‴~ u<)

wkidx[↑]-idxˣ⁻ᵖ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k₀0~ : k₀ ⍮ 0 ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) →
                  (x< : x ℕ.< k′ + k‴) →
                  -------------------------------------------------------------------------------------------------------------
                  wkidx[ lengthˣ⁻ k₀0~ ↑ lengthˣ⁻ kk′~ ] (idxˣ⁻ᵖ (kk′~ ++ˣ⁻ k″k‴~) x<) ≡ idxˣ⁻ᵖ (kk′~ ++ˣ⁻ k₀0~ ++ˣ⁻ k″k‴~) x<
wkidx[↑]-idxˣ⁻ᵖ             []         k₀0~ k″k‴~ x<                                               = ≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ k₀0~ k″k‴~ z≤n x< x<
wkidx[↑]-idxˣ⁻ᵖ             (!∷ᶜ kk′~) k₀0~ k″k‴~ x<
  rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ k₀0~) (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ (kk′~ ++ˣ⁻ k″k‴~) x<) = cong suc (wkidx[↑]-idxˣ⁻ᵖ kk′~ k₀0~ k″k‴~ x<)
wkidx[↑]-idxˣ⁻ᵖ             (?∷ᵖ kk′~) k₀0~ k″k‴~ x<
  rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ k₀0~) (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ (kk′~ ++ˣ⁻ k″k‴~) x<) = cong suc (wkidx[↑]-idxˣ⁻ᵖ kk′~ k₀0~ k″k‴~ x<)
wkidx[↑]-idxˣ⁻ᵖ {x = zero}  (!∷ᵖ kk′~) k₀0~ k″k‴~ (s≤s x<)                                         = refl
wkidx[↑]-idxˣ⁻ᵖ {x = suc x} (!∷ᵖ kk′~) k₀0~ k″k‴~ (s≤s x<)
  rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ k₀0~) (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ (kk′~ ++ˣ⁻ k″k‴~) x<) = cong suc (wkidx[↑]-idxˣ⁻ᵖ kk′~ k₀0~ k″k‴~ x<)

wk[0↑¹]≡ : ∀ u E →
           ----------------------
           DP.wk[ 0 ↑¹ u ] E ≡ E
wk[0↑¹]≡ u DP.`unit = refl
wk[0↑¹]≡ u (DP.`box E) = cong DP.`box (wk[0↑¹]≡ u E)
wk[0↑¹]≡ u (DP.`let-box E `in F) = cong₂ DP.`let-box_`in_ (wk[0↑¹]≡ u E) (wk[0↑¹]≡ (suc u) F)
wk[0↑¹]≡ u (DP.`λ⦂ S ∙ E) = cong (DP.`λ⦂ _ ∙_) (wk[0↑¹]≡ u E)
wk[0↑¹]≡ u (E DP.`$ F) = cong₂ DP._`$_ (wk[0↑¹]≡ u E) (wk[0↑¹]≡ u F)
wk[0↑¹]≡ u (DP.`#¹ v) = cong DP.`#¹_ (wkidx[0↑]≡ u v)
wk[0↑¹]≡ u (DP.`#⁰ y) = refl

wk[0↑⁰]≡ : ∀ x E →
           ----------------------
           DP.wk[ 0 ↑⁰ x ] E ≡ E
wk[0↑⁰]≡ x DP.`unit = refl
wk[0↑⁰]≡ x (DP.`box E) = refl
wk[0↑⁰]≡ x (DP.`let-box E `in F) = cong₂ DP.`let-box_`in_ (wk[0↑⁰]≡ x E) (wk[0↑⁰]≡ x F)
wk[0↑⁰]≡ x (DP.`λ⦂ S ∙ E) = cong (DP.`λ⦂ _ ∙_) (wk[0↑⁰]≡ (suc x) E)
wk[0↑⁰]≡ x (E DP.`$ F) = cong₂ DP._`$_ (wk[0↑⁰]≡ x E) (wk[0↑⁰]≡ x F)
wk[0↑⁰]≡ x (DP.`#¹ v) = refl
wk[0↑⁰]≡ x (DP.`#⁰ y) = cong DP.`#⁰_ (wkidx[0↑]≡ x y)

~ᴹ∧≥⇒wk[↑⁰]≡ : ∀ k₀ →
               {kk′~ : k ⍮ k′ ~ˣ⁻} →
               kk′~ ⊢ E ~ᴹ L →
               x ℕ.≥ k′ →
               -----------------------
               DP.wk[ k₀ ↑⁰ x ] E ≡ E
~ᴹ∧≥⇒wk[↑⁰]≡ _ `unit                x≥                   = refl
~ᴹ∧≥⇒wk[↑⁰]≡ _ (`box ~M)            x≥                   = refl
~ᴹ∧≥⇒wk[↑⁰]≡ _ (`let-box ~M `in ~N) x≥                   = cong₂ DP.`let-box_`in_ (~ᴹ∧≥⇒wk[↑⁰]≡ _ ~M x≥) (~ᴹ∧≥⇒wk[↑⁰]≡ _ ~N x≥)
~ᴹ∧≥⇒wk[↑⁰]≡ _ (`#¹ u<)             x≥                   = refl
~ᴹ∧≥⇒wk[↑⁰]≡ _ (`λ⦂ ~S ∙ ~M)        x≥                   = cong (DP.`λ⦂ _ ∙_) (~ᴹ∧≥⇒wk[↑⁰]≡ _ ~M (s≤s x≥))
~ᴹ∧≥⇒wk[↑⁰]≡ _ (~M `$ ~N)           x≥                   = cong₂ DP._`$_ (~ᴹ∧≥⇒wk[↑⁰]≡ _ ~M x≥) (~ᴹ∧≥⇒wk[↑⁰]≡ _ ~N x≥)
~ᴹ∧≥⇒wk[↑⁰]≡ _ (`#⁰ y<)             x≥
  rewrite dec-no (_ ℕ.≤? _) (ℕ.<⇒≱ (ℕ.<-≤-trans y< x≥))  = refl
~ᴹ∧≥⇒wk[↑⁰]≡ _ (`unlift-`lift ~M)   x≥                   = ~ᴹ∧≥⇒wk[↑⁰]≡ _ ~M z≤n 

wk[↑¹]~ᴹwk[↑]ᶜ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k₀0~ : k₀ ⍮ 0 ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                 kk′~ ++ˣ⁻ k″k‴~ ⊢ E ~ᴹ L →
                 ----------------------------------------------------------------------------------------
                 kk′~ ++ˣ⁻ k₀0~ ++ˣ⁻ k″k‴~ ⊢ DP.wk[ k₀ ↑¹ k ] E ~ᴹ wk[ lengthˣ⁻ k₀0~ ↑ lengthˣ⁻ kk′~ ] L
wk[↑¹]~ᴹwk[↑]ᶜ                    kk′~ k₀0~         `unit                                                = `unit
wk[↑¹]~ᴹwk[↑]ᶜ                    kk′~ k₀0~ {k″k‴~} (`box ~L)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~
    with ~L′ ← wk[↑¹]~ᴹwk[↑]ᶜ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k₀0~) ~L
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ k₀0~ k″k‴~)
            | sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ (k₀0~ ++ˣ⁻ k″k‴~))
            | lengthˣ⁻-extractˣ⁻ᶜ kk′~
            | lengthˣ⁻-extractˣ⁻ᶜ k₀0~                                                                   = `box ~L′
wk[↑¹]~ᴹwk[↑]ᶜ                    kk′~ k₀0~         (`let-box ~L `in ~M)                                 = `let-box wk[↑¹]~ᴹwk[↑]ᶜ kk′~ k₀0~ ~L `in wk[↑¹]~ᴹwk[↑]ᶜ (!∷ᶜ kk′~) k₀0~ ~M
wk[↑¹]~ᴹwk[↑]ᶜ {k} {_}  {k₀} {k″} kk′~ k₀0~ {k″k‴~} (`#¹_ {u = u} u<)
  with u ℕ.≥? k
...  | no  u≱k
    with u<k ← ℕ.≰⇒> u≱k
      rewrite sym (<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u<k u<)
            | dec-no (_ ℕ.≤? _) (ℕ.<⇒≱ (idxˣ⁻ᶜ<lengthˣ⁻ kk′~ u<k))
            | <⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (k₀0~ ++ˣ⁻ k″k‴~) u<k (ℕ.<-≤-trans u<k (ℕ.m≤m+n _ _))            = `#¹ ℕ.<-≤-trans u<k (ℕ.m≤m+n _ _)
...  | yes u≥k
    with u∸k< ← subst (u ∸ k ℕ.<_) (ℕ.m+n∸m≡n k _) (ℕ.∸-monoˡ-< u< u≥k)
       | k₀+u< ← ℕ.+-monoʳ-< k₀ u<
       | k₀+u∸keq ← sym (ℕ.+-∸-assoc k₀ u≥k)
       | k₀+[u∸k]∸k₀eq ← sym (ℕ.m+n∸m≡n k₀ (u ∸ k))
      with k₀+[u∸k]< ← ℕ.+-monoʳ-< k₀ u∸k<
         | k₀+[u∸k]-k₀< ← subst (ℕ._< k″) k₀+[u∸k]∸k₀eq u∸k<
        with k₀+u∸k< ← subst (ℕ._< k₀ + k″) k₀+u∸keq k₀+[u∸k]<
          rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u≥k u< u∸k<)
                | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ k″k‴~ u∸k<)))
                | sym (ℕ.+-assoc (lengthˣ⁻ k₀0~) (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ k″k‴~ u∸k<))
                | sym (ℕ.+-assoc k₀ k k″)
                | ℕ.+-comm (lengthˣ⁻ k₀0~) (lengthˣ⁻ kk′~)
                | ℕ.+-comm k₀ k
                | ℕ.+-assoc (lengthˣ⁻ kk′~) (lengthˣ⁻ k₀0~) (idxˣ⁻ᶜ k″k‴~ u∸k<)
                | ℕ.+-assoc k k₀ k″
                | idxˣ⁻ᶜ-<-irrelevant′ k″k‴~ u∸k< k₀+[u∸k]-k₀< k₀+[u∸k]∸k₀eq
                | ≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ k₀0~ k″k‴~ (ℕ.m≤m+n _ _) k₀+[u∸k]< k₀+[u∸k]-k₀<
                | idxˣ⁻ᶜ-<-irrelevant′ (k₀0~ ++ˣ⁻ k″k‴~) k₀+[u∸k]< k₀+u∸k< k₀+u∸keq
                | ≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (k₀0~ ++ˣ⁻ k″k‴~) (ℕ.m≤n⇒m≤o+n _ u≥k) k₀+u< k₀+u∸k< = `#¹ k₀+u<
wk[↑¹]~ᴹwk[↑]ᶜ {k} {k′}           kk′~ k₀0~         (`λ⦂ ~S ∙ ~L)
  with ~L′ ← wk[↑¹]~ᴹwk[↑]ᶜ (!∷ᵖ kk′~) k₀0~ ~L
    rewrite ℕ.+-suc k k′                                                                                 = `λ⦂ ~S ∙ ~L′
wk[↑¹]~ᴹwk[↑]ᶜ                    kk′~ k₀0~         (~L `$ ~M)                                           = wk[↑¹]~ᴹwk[↑]ᶜ kk′~ k₀0~ ~L `$ wk[↑¹]~ᴹwk[↑]ᶜ kk′~ k₀0~ ~M
wk[↑¹]~ᴹwk[↑]ᶜ                    kk′~ k₀0~ {k″k‴~} (`#⁰ x<)
  rewrite wkidx[↑]-idxˣ⁻ᵖ kk′~ k₀0~ k″k‴~ x<                                                             = `#⁰ x<
wk[↑¹]~ᴹwk[↑]ᶜ                    kk′~ k₀0~ {k″k‴~} (`unlift-`lift ~L)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~
    with ~L′ ← wk[↑¹]~ᴹwk[↑]ᶜ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k₀0~) ~L
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ k₀0~ k″k‴~)
            | sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ (k₀0~ ++ˣ⁻ k″k‴~))
            | lengthˣ⁻-extractˣ⁻ᶜ kk′~
            | lengthˣ⁻-extractˣ⁻ᶜ k₀0~                                                                   = `unlift-`lift ~L′

wk[↑⁰]~ᴹwk[↑]ᵖ : (kk′~ : k ⍮ k′ ~ˣ⁻) (0k₀~ : 0 ⍮ k₀ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                 kk′~ ++ˣ⁻ k″k‴~ ⊢ E ~ᴹ L →
                 -----------------------------------------------------------------------------------------
                 kk′~ ++ˣ⁻ 0k₀~ ++ˣ⁻ k″k‴~ ⊢ DP.wk[ k₀ ↑⁰ k′ ] E ~ᴹ wk[ lengthˣ⁻ 0k₀~ ↑ lengthˣ⁻ kk′~ ] L
wk[↑⁰]~ᴹwk[↑]ᵖ                         kk′~ 0k₀~         `unit                                            = `unit
wk[↑⁰]~ᴹwk[↑]ᵖ {k}                     kk′~ 0k₀~ {k″k‴~} (`box {E = E} ~L)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~
    with ~L′ ← wk[↑¹]~ᴹwk[↑]ᶜ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ 0k₀~) ~L
      rewrite wk[0↑¹]≡ k E
            | sym (extractˣ⁻ᶜ-++ˣ⁻ 0k₀~ k″k‴~)
            | sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ (0k₀~ ++ˣ⁻ k″k‴~))
            | lengthˣ⁻-extractˣ⁻ᶜ kk′~
            | lengthˣ⁻-extractˣ⁻ᶜ 0k₀~                                                                    = `box ~L′
wk[↑⁰]~ᴹwk[↑]ᵖ                         kk′~ 0k₀~         (`let-box ~L `in ~M)                             = `let-box wk[↑⁰]~ᴹwk[↑]ᵖ kk′~ 0k₀~ ~L `in wk[↑⁰]~ᴹwk[↑]ᵖ (!∷ᶜ kk′~) 0k₀~ ~M
wk[↑⁰]~ᴹwk[↑]ᵖ                         kk′~ 0k₀~ {k″k‴~} (`#¹ u<)
  rewrite wkidx[↑]-idxˣ⁻ᶜ kk′~ 0k₀~ k″k‴~ u<                                                              = `#¹ u<
wk[↑⁰]~ᴹwk[↑]ᵖ {k} {k′}                kk′~ 0k₀~         (`λ⦂ ~S ∙ ~L)
  with ~L′ ← wk[↑⁰]~ᴹwk[↑]ᵖ (!∷ᵖ kk′~) 0k₀~ ~L
    rewrite ℕ.+-suc k k′                                                                                  = `λ⦂ ~S ∙ ~L′
wk[↑⁰]~ᴹwk[↑]ᵖ                         kk′~ 0k₀~         (~L `$ ~M)                                       = wk[↑⁰]~ᴹwk[↑]ᵖ kk′~ 0k₀~ ~L `$ wk[↑⁰]~ᴹwk[↑]ᵖ kk′~ 0k₀~ ~M
wk[↑⁰]~ᴹwk[↑]ᵖ {_} {k′} {k₀} {_}  {k‴} kk′~ 0k₀~ {k″k‴~} (`#⁰_ {x = x} x<)
  with x ℕ.≥? k′
...  | no  x≱k′
    with x<k′ ← ℕ.≰⇒> x≱k′
      rewrite sym (<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x<k′ x<)
            | dec-no (_ ℕ.≤? _) (ℕ.<⇒≱ (idxˣ⁻ᵖ<lengthˣ⁻ kk′~ x<k′))
            | <⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ (0k₀~ ++ˣ⁻ k″k‴~) x<k′ (ℕ.<-≤-trans x<k′ (ℕ.m≤m+n _ _))           = `#⁰ ℕ.<-≤-trans x<k′ (ℕ.m≤m+n _ _)
...  | yes x≥k′
    with x∸k′< ← subst (x ∸ k′ ℕ.<_) (ℕ.m+n∸m≡n k′ _) (ℕ.∸-monoˡ-< x< x≥k′)
       | k₀+x< ← ℕ.+-monoʳ-< k₀ x<
       | k₀+x∸k′eq ← sym (ℕ.+-∸-assoc k₀ x≥k′)
       | k₀+[x∸k′]∸k₀eq ← sym (ℕ.m+n∸m≡n k₀ (x ∸ k′))
      with k₀+[x∸k′]< ← ℕ.+-monoʳ-< k₀ x∸k′<
         | k₀+[x∸k′]-k₀< ← subst (ℕ._< k‴) k₀+[x∸k′]∸k₀eq x∸k′<
        with k₀+x∸k′< ← subst (ℕ._< k₀ + k‴) k₀+x∸k′eq k₀+[x∸k′]<
          rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x≥k′ x< x∸k′<)
                | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ k″k‴~ x∸k′<)))
                | sym (ℕ.+-assoc (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ k″k‴~ x∸k′<))
                | sym (ℕ.+-assoc k₀ k′ k‴)
                | ℕ.+-comm (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~)
                | ℕ.+-comm k₀ k′
                | ℕ.+-assoc (lengthˣ⁻ kk′~) (lengthˣ⁻ 0k₀~) (idxˣ⁻ᵖ k″k‴~ x∸k′<)
                | ℕ.+-assoc k′ k₀ k‴
                | idxˣ⁻ᵖ-<-irrelevant′ k″k‴~ x∸k′< k₀+[x∸k′]-k₀< k₀+[x∸k′]∸k₀eq
                | ≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ 0k₀~ k″k‴~ (ℕ.m≤m+n _ _) k₀+[x∸k′]< k₀+[x∸k′]-k₀<
                | idxˣ⁻ᵖ-<-irrelevant′ (0k₀~ ++ˣ⁻ k″k‴~) k₀+[x∸k′]< k₀+x∸k′< k₀+x∸k′eq
                | ≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ (0k₀~ ++ˣ⁻ k″k‴~) (ℕ.m≤n⇒m≤o+n _ x≥k′) k₀+x< k₀+x∸k′< = `#⁰ k₀+x<
wk[↑⁰]~ᴹwk[↑]ᵖ {k} {k′} {k₀}           kk′~ 0k₀~ {k″k‴~} (`unlift-`lift {E = E} ~L)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~
    with ~L′ ← wk[↑¹]~ᴹwk[↑]ᶜ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ 0k₀~) ~L
      rewrite wk[0↑¹]≡ k E
            | sym (extractˣ⁻ᶜ-++ˣ⁻ 0k₀~ k″k‴~)
            | sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ (0k₀~ ++ˣ⁻ k″k‴~))
            | lengthˣ⁻-extractˣ⁻ᶜ kk′~
            | lengthˣ⁻-extractˣ⁻ᶜ 0k₀~
            | ~ᴹ∧≥⇒wk[↑⁰]≡ k₀ ~L (z≤n {k′})                                                                = `unlift-`lift ~L′

~ᴹ∧≥⇒[/⁰]≡ : {kk′~ : k ⍮ k′ ~ˣ⁻} →
             ∀ E →
             kk′~ ⊢ F ~ᴹ M →
             x ℕ.≥ k′ →
             --------------------
             DP.[ E /⁰ x ] F ≡ F
~ᴹ∧≥⇒[/⁰]≡ _ `unit                x≥                    = refl
~ᴹ∧≥⇒[/⁰]≡ _ (`box ~M)            x≥                    = refl
~ᴹ∧≥⇒[/⁰]≡ _ (`let-box ~M `in ~N) x≥                    = cong₂ DP.`let-box_`in_ (~ᴹ∧≥⇒[/⁰]≡ _ ~M x≥) (~ᴹ∧≥⇒[/⁰]≡ _ ~N x≥)
~ᴹ∧≥⇒[/⁰]≡ _ (`#¹ u<)             x≥                    = refl
~ᴹ∧≥⇒[/⁰]≡ _ (`λ⦂ ~S ∙ ~M)        x≥                    = cong (DP.`λ⦂ _ ∙_) (~ᴹ∧≥⇒[/⁰]≡ _ ~M (s≤s x≥))
~ᴹ∧≥⇒[/⁰]≡ _ (~M `$ ~N)           x≥                    = cong₂ DP._`$_ (~ᴹ∧≥⇒[/⁰]≡ _ ~M x≥) (~ᴹ∧≥⇒[/⁰]≡ _ ~N x≥)
~ᴹ∧≥⇒[/⁰]≡ _ (`#⁰ y<)             x≥
  rewrite dec-no (_ ℕ.≤? _) (ℕ.<⇒≱ (ℕ.<-≤-trans y< x≥)) = refl
~ᴹ∧≥⇒[/⁰]≡ _ (`unlift-`lift ~M)   x≥                    = ~ᴹ∧≥⇒[/⁰]≡ _ ~M z≤n 

[/¹]~ᴹ[/]ᶜ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
             extractˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) ⊢ E ~ᴹ L →
             kk′~ ++ˣ⁻ !∷ᶜ k″k‴~ ⊢ F ~ᴹ M →
             ----------------------------------------------------------------------------
             kk′~ ++ˣ⁻ k″k‴~ ⊢ DP.[ E /¹ k ] F ~ᴹ [ `lift L /[ cMode ] lengthˣ⁻ kk′~ ] M
[/¹]~ᴹ[/]ᶜ               kk′~         ~L `unit                                     = `unit
[/¹]~ᴹ[/]ᶜ               kk′~ {k″k‴~} ~L (`box ~M)
  rewrite sym (extractˣ⁻ᶜ-idempotent (kk′~ ++ˣ⁻ k″k‴~))
        | extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~
        | extractˣ⁻ᶜ-++ˣ⁻ kk′~ (!∷ᶜ k″k‴~)
    with ~M′ ← [/¹]~ᴹ[/]ᶜ (extractˣ⁻ᶜ kk′~) ~L ~M
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~)
            | lengthˣ⁻-extractˣ⁻ᶜ kk′~                                             = `box ~M′
[/¹]~ᴹ[/]ᶜ               kk′~         ~L (`let-box ~M `in ~N)                      = `let-box [/¹]~ᴹ[/]ᶜ kk′~ ~L ~M `in [/¹]~ᴹ[/]ᶜ (!∷ᶜ kk′~) (wk[↑¹]~ᴹwk[↑]ᶜ [] (!∷ᶜ []) ~L) ~N
[/¹]~ᴹ[/]ᶜ {k} {_}  {k″} kk′~ {k″k‴~} ~L (`#¹_ {u = u} u<)
  with u ℕ.≥? k
...  | no  u≱k
    with u<k ← ℕ.≰⇒> u≱k
      rewrite sym (<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (!∷ᶜ k″k‴~) u<k u<)
            | dec-no (_ ℕ.≤? _) (ℕ.<⇒≱ (idxˣ⁻ᶜ<lengthˣ⁻ kk′~ u<k))
            | <⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u<k (ℕ.m≤n⇒m≤n+o _ u<k)              = `#¹ ℕ.m≤n⇒m≤n+o _ u<k
...  | yes u≥k
    with u∸k< ← subst (u ∸ k ℕ.<_) (ℕ.m+n∸m≡n k _) (ℕ.∸-monoˡ-< u< u≥k)
      rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (!∷ᶜ k″k‴~) u≥k u< u∸k<)
            | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ (!∷ᶜ k″k‴~) u∸k<)))
        with u ℕ.≟ k
...        | no  u≢k
          with u>k ← ℕ.≤∧≢⇒< u≥k (≢-sym u≢k)
             | s≤s u∸k≤ ← u∸k<
            with suc u′ ← u
              with u′≥k ← ℕ.≤-pred u>k
                rewrite ℕ.+-∸-assoc 1 u′≥k
                      | dec-no (_ ℕ.≟ _) (ℕ.m+1+n≢m (lengthˣ⁻ kk′~) {idxˣ⁻ᶜ k″k‴~ u∸k≤})
                      | ℕ.+-suc (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ k″k‴~ u∸k≤)
                      | ℕ.+-suc k k″
                  with u′< ← ℕ.≤-pred u<
                    rewrite ≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u′≥k u′< u∸k≤ = `#¹ u′<
...        | yes refl
          with s≤s _ ← u∸k<
            rewrite ℕ.n∸n≡0 k
                  | proj₂ (dec-yes (_ ℕ.≟ _) (ℕ.+-identityʳ (lengthˣ⁻ kk′~)))      = `unlift-`lift ~L
[/¹]~ᴹ[/]ᶜ {k} {k′} {_}  {_}  {E} kk′~         ~L (`λ⦂ ~S ∙ ~M)
  with ~L′ ← wk[↑¹]~ᴹwk[↑]ᶜ [] (?∷ᵖ []) ~L
    with ~M′ ← [/¹]~ᴹ[/]ᶜ (!∷ᵖ kk′~) ~L′ ~M
      rewrite wk[0↑¹]≡ 0 E
            | ℕ.+-suc k k′                                                         = `λ⦂ ~S ∙ ~M′
[/¹]~ᴹ[/]ᶜ               kk′~         ~L (~M `$ ~N)                                = [/¹]~ᴹ[/]ᶜ kk′~ ~L ~M `$ [/¹]~ᴹ[/]ᶜ kk′~ ~L ~N
[/¹]~ᴹ[/]ᶜ {_} {k′}      kk′~ {k″k‴~} ~L (`#⁰_ {x = x} x<)
  with x ℕ.≥? k′
...  | no  x≱k′
    with x<k′ ← ℕ.≰⇒> x≱k′
      rewrite sym (<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ (!∷ᶜ k″k‴~) x<k′ x<)
            | dec-no (_ ℕ.≥? _) (ℕ.<⇒≱ (idxˣ⁻ᵖ<lengthˣ⁻ kk′~ x<k′))
            | <⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x<k′ x<                              = `#⁰ x<
...  | yes x≥k′
    with x∸k′< ← subst (x ∸ k′ ℕ.<_) (ℕ.m+n∸m≡n k′ _) (ℕ.∸-monoˡ-< x< x≥k′)
      rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ (!∷ᶜ k″k‴~) x≥k′ x< x∸k′<)
            | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ (!∷ᶜ k″k‴~) x∸k′<)))
            | dec-no (_ ℕ.≟ _) (ℕ.m+1+n≢m (lengthˣ⁻ kk′~) {idxˣ⁻ᵖ k″k‴~ x∸k′<})
            | ℕ.+-suc (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ k″k‴~ x∸k′<)
            | ≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x≥k′ x< x∸k′<               = `#⁰ x<
[/¹]~ᴹ[/]ᶜ               kk′~ {k″k‴~} ~L (`unlift-`lift ~M)
  rewrite sym (extractˣ⁻ᶜ-idempotent (kk′~ ++ˣ⁻ k″k‴~))
        | extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~
        | extractˣ⁻ᶜ-++ˣ⁻ kk′~ (!∷ᶜ k″k‴~)
    with ~M′ ← [/¹]~ᴹ[/]ᶜ (extractˣ⁻ᶜ kk′~) ~L ~M
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~)
            | lengthˣ⁻-extractˣ⁻ᶜ kk′~                                             = `unlift-`lift ~M′

~ᴹ[/]ᵖ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
         ∀ L →
         kk′~ ++ˣ⁻ ?∷ᵖ k″k‴~ ⊢ F ~ᴹ M →
         --------------------------------------------------------
         kk′~ ++ˣ⁻ k″k‴~ ⊢ F ~ᴹ [ L /[ pMode ] lengthˣ⁻ kk′~ ] M
~ᴹ[/]ᵖ          kk′~         _ `unit                                 = `unit
~ᴹ[/]ᵖ          kk′~ {k″k‴~} _ (`box ~M)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ (?∷ᵖ k″k‴~)
    with ~M′ ← ~ᴹ[/]ᵖ (extractˣ⁻ᶜ kk′~) (`unit `$ `unit) ~M
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~)
            | lengthˣ⁻-extractˣ⁻ᶜ kk′~                               = `box ~M′
~ᴹ[/]ᵖ          kk′~         _ (`let-box ~M `in ~N)                  = `let-box ~ᴹ[/]ᵖ kk′~ _ ~M `in ~ᴹ[/]ᵖ (!∷ᶜ kk′~) _ ~N
~ᴹ[/]ᵖ {k}      kk′~ {k″k‴~} _ (`#¹_ {u = u} u<)
  with u ℕ.≥? k
...  | no  u≱k
    rewrite sym (<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (?∷ᵖ k″k‴~) (ℕ.≰⇒> u≱k) u<)
          | dec-no (_ ℕ.≥? _) (ℕ.<⇒≱ (idxˣ⁻ᶜ<lengthˣ⁻ kk′~ (ℕ.≰⇒> u≱k)))
          | <⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ (ℕ.≰⇒> u≱k) u<           = `#¹ u<
...  | yes u≥k
    with u∸k< ← subst (u ∸ k ℕ.<_) (ℕ.m+n∸m≡n k _) (ℕ.∸-monoˡ-< u< u≥k)
      rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (?∷ᵖ k″k‴~) u≥k u< u∸k<)
            | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ (?∷ᵖ k″k‴~) u∸k<)))
            | dec-no (_ ℕ.≟ _) (ℕ.m+1+n≢m (lengthˣ⁻ kk′~) {idxˣ⁻ᶜ k″k‴~ u∸k<})
            | ℕ.+-suc (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ k″k‴~ u∸k<)
            | ≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u≥k u< u∸k<   = `#¹ u<
~ᴹ[/]ᵖ          kk′~         _ (`λ⦂ ~S ∙ ~M)                         = `λ⦂ ~S ∙ (~ᴹ[/]ᵖ (!∷ᵖ kk′~) _ ~M)
~ᴹ[/]ᵖ          kk′~         _ (~M `$ ~N)                            = ~ᴹ[/]ᵖ kk′~ _ ~M `$ ~ᴹ[/]ᵖ kk′~ _ ~N
~ᴹ[/]ᵖ {_} {k′} kk′~ {k″k‴~} _ (`#⁰_ {x = x} x<)
  with x ℕ.≥? k′
...  | no  x≱k′
    with x<k′ ← ℕ.≰⇒> x≱k′
      rewrite sym (<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ (?∷ᵖ k″k‴~) x<k′ x<)
            | dec-no (_ ℕ.≥? _) (ℕ.<⇒≱ (idxˣ⁻ᵖ<lengthˣ⁻ kk′~ x<k′))
            | <⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x<k′ x<                = `#⁰ x<
...  | yes x≥k′
    with x∸k′< ← subst (x ∸ k′ ℕ.<_) (ℕ.m+n∸m≡n k′ _) (ℕ.∸-monoˡ-< x< x≥k′)
      rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ (?∷ᵖ k″k‴~) x≥k′ x< x∸k′<)
            | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ (?∷ᵖ k″k‴~) x∸k′<)))
            | dec-no (_ ℕ.≟ _) (ℕ.m+1+n≢m (lengthˣ⁻ kk′~) {idxˣ⁻ᵖ k″k‴~ x∸k′<})
            | ℕ.+-suc (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ k″k‴~ x∸k′<)
            | ≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x≥k′ x< x∸k′< = `#⁰ x<
~ᴹ[/]ᵖ          kk′~ {k″k‴~} _ (`unlift-`lift ~M)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ (?∷ᵖ k″k‴~)
    with ~M′ ← ~ᴹ[/]ᵖ (extractˣ⁻ᶜ kk′~) (`unit `$ `unit) ~M
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~)
            | lengthˣ⁻-extractˣ⁻ᶜ kk′~                               = `unlift-`lift ~M′

[/⁰]~ᴹ[/]ᵖ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
             kk′~ ++ˣ⁻ k″k‴~ ⊢ E ~ᴹ L →
             kk′~ ++ˣ⁻ !∷ᵖ k″k‴~ ⊢ F ~ᴹ M →
             -----------------------------------------------------------------------
             kk′~ ++ˣ⁻ k″k‴~ ⊢ DP.[ E /⁰ k′ ] F ~ᴹ [ L /[ pMode ] lengthˣ⁻ kk′~ ] M
[/⁰]~ᴹ[/]ᵖ                              kk′~         ~L `unit                        = `unit
[/⁰]~ᴹ[/]ᵖ                              kk′~ {k″k‴~} ~L (`box ~M)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ (!∷ᵖ k″k‴~)
    with ~M′ ← ~ᴹ[/]ᵖ (extractˣ⁻ᶜ kk′~) (`unit `$ `unit) ~M
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~)
            | lengthˣ⁻-extractˣ⁻ᶜ kk′~                                               = `box ~M′
[/⁰]~ᴹ[/]ᵖ                              kk′~         ~L (`let-box ~M `in ~N)         = `let-box [/⁰]~ᴹ[/]ᵖ kk′~ ~L ~M `in [/⁰]~ᴹ[/]ᵖ (!∷ᶜ kk′~) (wk[↑¹]~ᴹwk[↑]ᶜ [] (!∷ᶜ []) ~L) ~N
[/⁰]~ᴹ[/]ᵖ {k} {_}  {_}  {_}  {_}   {L} kk′~ {k″k‴~} ~L (`#¹_ {u = u} u<)
  with u ℕ.≥? k
...  | no  u≱k
    rewrite sym (<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (!∷ᵖ k″k‴~) (ℕ.≰⇒> u≱k) u<)
          | <⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (?∷ᵖ k″k‴~) (ℕ.≰⇒> u≱k) u<                     = ~ᴹ[/]ᵖ kk′~ L (`#¹ u<)
...  | yes u≥k
    with u∸k< ← subst (u ∸ k ℕ.<_) (ℕ.m+n∸m≡n k _) (ℕ.∸-monoˡ-< u< u≥k)
      rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (!∷ᵖ k″k‴~) u≥k u< u∸k<)
            | ≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (?∷ᵖ k″k‴~) u≥k u< u∸k<             = ~ᴹ[/]ᵖ kk′~ L (`#¹ u<) 
[/⁰]~ᴹ[/]ᵖ {k} {k′}                     kk′~         ~L (`λ⦂ ~S ∙ ~M)
  with ~M′ ← [/⁰]~ᴹ[/]ᵖ (!∷ᵖ kk′~) (wk[↑⁰]~ᴹwk[↑]ᵖ [] (!∷ᵖ []) ~L) ~M
    rewrite ℕ.+-suc k k′                                                             = `λ⦂ ~S ∙ ~M′
[/⁰]~ᴹ[/]ᵖ                              kk′~         ~L (~M `$ ~N)                   = [/⁰]~ᴹ[/]ᵖ kk′~ ~L ~M `$ [/⁰]~ᴹ[/]ᵖ kk′~ ~L ~N
[/⁰]~ᴹ[/]ᵖ {_} {k′} {_}  {k‴}           kk′~ {k″k‴~} ~L (`#⁰_ {x = x} x<)
  with x ℕ.≥? k′
...  | no  x≱k′
    with x<k′ ← ℕ.≰⇒> x≱k′
      rewrite sym (<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ (!∷ᵖ k″k‴~) x<k′ x<)
            | dec-no (_ ℕ.≥? _) (ℕ.<⇒≱ (idxˣ⁻ᵖ<lengthˣ⁻ kk′~ x<k′))
            | <⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x<k′ (ℕ.m≤n⇒m≤n+o _ x<k′)              = `#⁰ ℕ.m≤n⇒m≤n+o _ x<k′
...  | yes x≥k′
    with x∸k′< ← subst (x ∸ k′ ℕ.<_) (ℕ.m+n∸m≡n k′ _) (ℕ.∸-monoˡ-< x< x≥k′)
      rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ (!∷ᵖ k″k‴~) x≥k′ x< x∸k′<)
            | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ (!∷ᵖ k″k‴~) x∸k′<)))
        with x ℕ.≟ k′
...        | no  x≢k′
          with x>k′ ← ℕ.≤∧≢⇒< x≥k′ (≢-sym x≢k′)
             | s≤s x∸k′≤ ← x∸k′<
            with suc x′ ← x
              with x′≥k′ ← ℕ.≤-pred x>k′
                rewrite ℕ.+-∸-assoc 1 (ℕ.≤-pred x>k′)
                      | dec-no (_ ℕ.≟ _) (ℕ.m+1+n≢m (lengthˣ⁻ kk′~) {idxˣ⁻ᵖ k″k‴~ x∸k′≤})
                      | ℕ.+-suc (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ k″k‴~ x∸k′≤)
                      | ℕ.+-suc k′ k‴
                  with x′< ← ℕ.≤-pred x<
                    rewrite ≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x′≥k′ x′< x∸k′≤ = `#⁰ x′<
...        | yes refl
          with s≤s _ ← x∸k′<
            rewrite ℕ.n∸n≡0 k′
                  | proj₂ (dec-yes (_ ℕ.≟ _) (ℕ.+-identityʳ (lengthˣ⁻ kk′~)))        = ~L
[/⁰]~ᴹ[/]ᵖ {_} {k′} {_}  {_}  {E}     kk′~ {k″k‴~} ~L (`unlift-`lift ~M)
  rewrite ~ᴹ∧≥⇒[/⁰]≡ E ~M (z≤n {k′})
        | extractˣ⁻ᶜ-++ˣ⁻ kk′~ (!∷ᵖ k″k‴~)
    with ~M′ ← ~ᴹ[/]ᵖ (extractˣ⁻ᶜ kk′~) (`unit `$ `unit) ~M
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~)
            | lengthˣ⁻-extractˣ⁻ᶜ kk′~                                               = `unlift-`lift ~M′


-- Bisimulation Properties of _~ᴹ_ Regarding OpSems
--
~ᴹ-simulation-helper : E DP.⟶ E′ →
                       (~L : [] ⊢ E ~ᴹ L) →
                       Acc ℕ._<_ (depth~ᴹ ~L) →
                       -----------------------------------
                       ∃ (λ L′ → L ⟶* L′ × [] ⊢ E′ ~ᴹ L′)
~ᴹ-simulation-helper E⟶                    (`unlift-`lift ~L)   (acc r)
  with _ , ⟶*L′[≤] , VL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
    with _ , ⟶*L″ , ~L″ ← ~ᴹ-simulation-helper E⟶ ~L′ (r (s≤s L′≤))        = -, ξ-of-↝*-⟶* _⟶[ cMode ≤]_ `unlift`lift ξ-`unlift`lift ⟶*L′[≤]
                                                                                 ◅◅ β-`↑ VL′ ◅ ⟶*L″
                                                                           , ~L″
~ᴹ-simulation-helper DP.ξ-`let-box E⟶ `in- (`let-box ~L `in ~M) (acc r)
  with _ , ⟶*L′ , ~L′ ← ~ᴹ-simulation-helper E⟶ ~L (r (s≤s (ℕ.m≤m⊔n _ _))) = -, ξ-of-⟶* (`let-return_`in _) ξ-`let-return_`in- ⟶*L′
                                                                           , `let-box ~L′ `in ~M
~ᴹ-simulation-helper DP.β-`□               (`let-box ~L `in ~M) rec
  with _ , ⟶*`boxL′ , WL′ , ~L ← `box-~ᴹ-inv ~L                            = -, ξ-of-⟶* (`let-return_`in _) ξ-`let-return_`in- ⟶*`boxL′
                                                                               ◅◅ β-`↓ (`lift WL′) ◅ ε
                                                                           , [/¹]~ᴹ[/]ᶜ [] ~L ~M
~ᴹ-simulation-helper DP.ξ- E⟶ `$?          (~L `$ ~M)           (acc r)
  with _ , ⟶*L′ , ~L′ ← ~ᴹ-simulation-helper E⟶ ~L (r (s≤s (ℕ.m≤m⊔n _ _))) = -, ξ-of-⟶* (_`$ _) ξ-_`$? ⟶*L′
                                                                           , ~L′ `$ ~M
~ᴹ-simulation-helper (DP.ξ-! VE `$ F⟶)     (~L `$ ~M)           (acc r)
  with _ , ⟶*L′ , VL′ , ~L′ ← Value~ᴹ-normalize ~L VE
     | _ , ⟶*M′ , ~M′ ← ~ᴹ-simulation-helper F⟶ ~M (r (s≤s (ℕ.m≤n⊔m _ _))) = -, ξ-of-⟶* (_`$ _) ξ-_`$? ⟶*L′
                                                                               ◅◅ ξ-of-⟶* (_ `$_) (ξ-! VL′ `$_) ⟶*M′
                                                                           , ~L′ `$ ~M′
~ᴹ-simulation-helper (DP.β-`→ VF)          (~L `$ ~M)           rec
  with _ , _ , ⟶*`λ⦂ᵖS′∘L′ , ~L′ , ~S′ ← `λ⦂-∙-~ᴹ-inv ~L
     | _ , ⟶*M′ , VM′ , ~M′ ← Value~ᴹ-normalize ~M VF                      = -, ξ-of-⟶* (_`$ _) ξ-_`$? ⟶*`λ⦂ᵖS′∘L′
                                                                               ◅◅ ξ-of-⟶* (_ `$_) ξ-! `λ⦂ᵖ _ ∘ _ `$_ ⟶*M′
                                                                               ◅◅ β-`⊸ VM′ ◅ ε
                                                                           , [/⁰]~ᴹ[/]ᵖ [] ~M′ ~L′

~ᴹ-simulation : E DP.⟶ E′ →
                [] ⊢ E ~ᴹ L →
                -----------------------------------
                ∃ (λ L′ → L ⟶* L′ × [] ⊢ E′ ~ᴹ L′)
~ᴹ-simulation E⟶ ~L = ~ᴹ-simulation-helper E⟶ ~L (ℕ.<-wellFounded _)

~ᴹ⁻¹-simulation : L ⟶ L′ →
                  [] ⊢ E ~ᴹ L →
                  -----------------------------------------------
                  ∃ (λ E′ → E DP.⟶* E′ × [] ⊢ E′ ~ᴹ L′)
~ᴹ⁻¹-simulation (ξ-`unlift (ξ-`lift L⟶[≤])) (`unlift-`lift ~L)        = -, ε , `unlift-`lift (⟶[≤]-preserves-~ᴹ ~L L⟶[≤])
~ᴹ⁻¹-simulation (β-`↑ WL′)                  (`unlift-`lift ~L)        = -, ε , ~L
~ᴹ⁻¹-simulation (ξ-`return (ξ-`lift L⟶[≤])) (`box ~L)                 = -, ε , `box (⟶[≤]-preserves-~ᴹ ~L L⟶[≤])
~ᴹ⁻¹-simulation ξ-`let-return L⟶ `in-       (`let-box ~L `in ~M)
  with _ , E⟶* , ~L′ ← ~ᴹ⁻¹-simulation L⟶ ~L                          = -, DP.ξ-of-⟶* (DP.`let-box_`in _) DP.ξ-`let-box_`in- E⟶* , `let-box ~L′ `in ~M
~ᴹ⁻¹-simulation (β-`↓ (`lift WL))           (`let-box `box ~L `in ~M) = -, DP.β-`□ ◅ ε , [/¹]~ᴹ[/]ᶜ [] ~L ~M
~ᴹ⁻¹-simulation ξ- L⟶ `$?                   (~L `$ ~M)
  with _ , E⟶* , ~L′ ← ~ᴹ⁻¹-simulation L⟶ ~L                          = -, DP.ξ-of-⟶* (DP._`$ _) DP.ξ-_`$? E⟶* , ~L′ `$ ~M
~ᴹ⁻¹-simulation (ξ-! VL′ `$ M⟶)             (~L `$ ~M)
  with _ , F⟶* , ~M′ ← ~ᴹ⁻¹-simulation M⟶ ~M                          = -, DP.ξ-of-⟶* (_ DP.`$_) (DP.ξ-! []⊢~ᴹ⁻¹-respects-Value ~L VL′ `$_) F⟶* , ~L `$ ~M′
~ᴹ⁻¹-simulation (β-`⊸ VM)                   ((`λ⦂ ~S ∙ ~L) `$ ~M)     = -, DP.β-`→ ([]⊢~ᴹ⁻¹-respects-Value ~M VM) ◅ ε , [/⁰]~ᴹ[/]ᵖ [] ~M ~L

