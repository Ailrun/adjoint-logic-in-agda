------------------------------------------------------------
-- (Declarative) Static Rules for Elevator
------------------------------------------------------------

{-# OPTIONS --safe #-}
open import Calculus.AdjND.ModeSpec

module Calculus.AdjND.Typing {ℓ₁ ℓ₂} (ℳ : ModeSpec ℓ₁ ℓ₂) where
open ModeSpec ℳ

open import Agda.Primitive
open import Data.Bool as Bool using (true; false)
open import Data.List as List using ([]; _∷_)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Nat as ℕ using (ℕ; suc)
open import Data.Product as × using (_×_; _,_)
open import Relation.Nullary using (¬_)

open import Calculus.AdjND.Syntax ℳ

infix   4 ⊢[_]_⦂⋆
infix   4 [_]⊢[_]d_
infix   4 ⊢[_]_
infix   4 _[_]~d_⊞_
infix   4 _~_⊞_
infix   4 _[_]∤[_]d_
infix   4 _∤[_]_
infix   4 _⦂[_]_∈_
infix   4 _⊢[_]_⦂_
infix   4 _⊢[_]_≈[≥_]_⦂_

-- Type Well-modedness
--
data ⊢[_]_⦂⋆ : Mode → Type → Set (ℓ₁ ⊔ ℓ₂) where
  `⊤[_]       : Bool.T (opₘ m ``⊤) →
                ---------------------
                ⊢[ m ] `⊤ ⦂⋆

  _`⊸[_]_     : ⊢[ m ] S ⦂⋆ →
                Bool.T (opₘ m ``⊸) →
                ⊢[ m ] T ⦂⋆ →
                ---------------------
                ⊢[ m ] S `⊸ T ⦂⋆

  `↑[-⇒_][_]_ : m₀ <ₘ m →
                Bool.T (opₘ m ``↑) →
                ⊢[ m₀ ] S ⦂⋆ →
                -------------------------
                ⊢[ m ] `↑[ m₀ ⇒ m ] S ⦂⋆

  `↓[-⇒_][_]_ : m <ₘ m₀ →
                Bool.T (opₘ m ``↓) →
                ⊢[ m₀ ] S ⦂⋆ →
                -------------------------
                ⊢[ m ] `↓[ m₀ ⇒ m ] S ⦂⋆

-- Context Well-modedness
--
data [_]⊢[_]d_ : Mode → Mode → Useable → Set (ℓ₁ ⊔ ℓ₂) where
  valid    : m ≤ₘ m₀ →
             -------------------
             [ m₀ ]⊢[ m ]d true

  unusable : --------------------
             [ m₀ ]⊢[ m ]d false

⊢[_]_ : Mode → Context → Set (ℓ₁ ⊔ ℓ₂)
⊢[ m ] Γ = All (λ (S , m₀ , d) → ⊢[ m₀ ] S ⦂⋆ × [ m₀ ]⊢[ m ]d d) Γ

-- Full Weakening Opeartions
--
data _[_]is-del : Useable → Mode → Set ℓ₁ where
  unusable  : -----------------------------
              false [ m ]is-del

  weakening : Bool.T (stₘ m ``Wk) →
              ----------------------------
              true [ m ]is-del

_is-all-del : Context → Set ℓ₁
_is-all-del = All (λ (_ , m , d) → d [ m ]is-del)

-- Mode-based Weakening Opeartions
--
data _[_]∤[_]d_ : Useable → Mode → Mode → Useable → Set (ℓ₁ ⊔ ℓ₂) where
  delete : ¬ (m ≤ₘ m₀) →
           d [ m₀ ]is-del →
           ------------------------
           d [ m₀ ]∤[ m ]d false

  keep   : m ≤ₘ m₀ →
           --------------------
           d [ m₀ ]∤[ m ]d d

data _∤[_]_ : Context → Mode → Context → Set (ℓ₁ ⊔ ℓ₂) where
  []  : -------------
        [] ∤[ m ] []

  _∷_ : d [ m₀ ]∤[ m ]d d′ →
        Γ ∤[ m ] Γ′ →
        ---------------------------------------------
        (S , m₀ , d) ∷ Γ ∤[ m ] (S , m₀ , d′) ∷ Γ′

-- Splitting Opeartions
--
data _[_]~d_⊞_ : Useable → Mode → Useable → Useable → Set ℓ₁ where
  contraction : Bool.T (stₘ m ``Co) →
                -------------------------
                true [ m ]~d true ⊞ true

  to-left     : --------------------------
                true [ m ]~d true ⊞ false

  to-right    : --------------------------
                true [ m ]~d false ⊞ true

  unusable    : ----------------------------
                false [ m ]~d false ⊞ false

data _~_⊞_ : Context → Context → Context → Set ℓ₁ where
  []  : ------------------
        [] ~ [] ⊞ []

  _∷_ : d [ m ]~d d₀ ⊞ d₁ →
        Γ ~ Γ₀ ⊞ Γ₁ →
        -----------------------------------------------------------
        (S , m , d) ∷ Γ ~ (S , m , d₀) ∷ Γ₀ ⊞ (S , m , d₁) ∷ Γ₁

-- Variable-Context Membership
--
data _⦂[_]_∈_ : ℕ → Mode → Type → Context → Set ℓ₁ where
  here  : Γ is-all-del →
          --------------------------------
          0 ⦂[ m ] S ∈ (S , m , true) ∷ Γ

  there : dT [ m₀ ]is-del →
          x ⦂[ m ] S ∈ Γ →
          -----------------------------------
          suc x ⦂[ m ] S ∈ (T , m₀ , dT) ∷ Γ

-- Term Typing
--
data _⊢[_]_⦂_ : Context → Mode → Term → Type → Set (ℓ₁ ⊔ ℓ₂) where
  `unit                       : Γ is-all-del →
                                ---------------------
                                Γ ⊢[ m ] `unit ⦂ `⊤

  `lift[-⇒-]_                 : Γ ⊢[ m₀ ] L ⦂ S →
                                --------------------------------------------
                                Γ ⊢[ m ] `lift[ m₀ ⇒ m ] L ⦂ `↑[ m₀ ⇒ m ] S

  _⊢`unlift[-⇒-]_⦂_           : Γ ∤[ m₀ ] Γ′ →
                                Γ′ ⊢[ m₀ ] L ⦂ `↑[ m ⇒ m₀ ] S →
                                ⊢[ m₀ ] `↑[ m ⇒ m₀ ] S ⦂⋆ →
                                ---------------------------------
                                Γ ⊢[ m ] `unlift[ m₀ ⇒ m ] L ⦂ S

  _⊢`return[-⇒-]_             : Γ ∤[ m₀ ] Γ′ →
                                Γ′ ⊢[ m₀ ] L ⦂ S →
                                ----------------------------------------------
                                Γ ⊢[ m ] `return[ m₀ ⇒ m ] L ⦂ `↓[ m₀ ⇒ m ] S

  _&_⊢`let-return[_⇒-]_⦂_`in_ : Γ ~ Γ₀ ⊞ Γ₁ →
                                Γ₀ ∤[ m₁ ] Γ₀′ →
                                m ≤ₘ m₁ →
                                Γ₀′ ⊢[ m₁ ] L ⦂ `↓[ m₀ ⇒ m₁ ] T →
                                ⊢[ m₁ ] `↓[ m₀ ⇒ m₁ ] T ⦂⋆ →
                                (T , m₀ , true) ∷ Γ₁ ⊢[ m ] M ⦂ S →
                                --------------------------------------------
                                Γ ⊢[ m ] `let-return[ m₁ ⇒ m₀ ] L `in M ⦂ S

  `λ⦂-∘_                      : (S , m , true) ∷ Γ ⊢[ m ] L ⦂ T →
                                ----------------------------------
                                Γ ⊢[ m ] `λ⦂[ m ] S ∘ L ⦂ S `⊸ T

  _⊢_⦂_`$_                    : Γ ~ Γ₀ ⊞ Γ₁ →
                                Γ₀ ⊢[ m ] L ⦂ T `⊸ S →
                                ⊢[ m ] T `⊸ S ⦂⋆ →
                                Γ₁ ⊢[ m ] M ⦂ T →
                                -----------------------
                                Γ ⊢[ m ] L `$ M ⦂ S

  `#_                         : x ⦂[ m ] S ∈ Γ →
                                ------------------
                                Γ ⊢[ m ] `# x ⦂ S

-- Term Equivalence Modulo Mode
--
data _⊢[_]_≈[≥_]_⦂_ : Context → Mode → Term → Mode → Term → Type → Set (ℓ₁ ⊔ ℓ₂) where
  `unit                       : Γ is-all-del →
                                -----------------------------------
                                Γ ⊢[ m ] `unit ≈[≥ m′ ] `unit ⦂ `⊤

  `lift[≤_⇒-]                 : m′ ≤ₘ m₀ →
                                Γ ⊢[ m₀ ] L ≈[≥ m′ ] L′ ⦂ S →
                                ------------------------------------------------------------------------
                                Γ ⊢[ m ] `lift[ m₀ ⇒ m ] L ≈[≥ m′ ] `lift[ m₀ ⇒ m ] L′ ⦂ `↑[ m₀ ⇒ m ] S

  `lift[≰_⇒-]                 : ¬ (m′ ≤ₘ m₀) →
                                Γ ⊢[ m₀ ] L ⦂ S →
                                Γ ⊢[ m₀ ] L′ ⦂ S →
                                ------------------------------------------------------------------------
                                Γ ⊢[ m ] `lift[ m₀ ⇒ m ] L ≈[≥ m′ ] `lift[ m₀ ⇒ m ] L′ ⦂ `↑[ m₀ ⇒ m ] S

  _⊢`unlift[-⇒-]_⦂_           : Γ ∤[ m₀ ] Γ′ →
                                Γ′ ⊢[ m₀ ] L ≈[≥ m′ ] L′ ⦂ `↑[ m ⇒ m₀ ] S →
                                ⊢[ m₀ ] `↑[ m ⇒ m₀ ] S ⦂⋆ →
                                ---------------------------------------------------------------
                                Γ ⊢[ m ] `unlift[ m₀ ⇒ m ] L ≈[≥ m′ ] `unlift[ m₀ ⇒ m ] L′ ⦂ S

  _⊢`return[-⇒-]_             : Γ ∤[ m₀ ] Γ′ →
                                Γ′ ⊢[ m₀ ] L ≈[≥ m′ ] L′ ⦂ S →
                                ----------------------------------------------------------------------------
                                Γ ⊢[ m ] `return[ m₀ ⇒ m ] L ≈[≥ m′ ] `return[ m₀ ⇒ m ] L′ ⦂ `↓[ m₀ ⇒ m ] S

  _&_⊢`let-return[_⇒-]_⦂_`in_ : Γ ~ Γ₀ ⊞ Γ₁ →
                                Γ₀ ∤[ m₁ ] Γ₀′ →
                                m ≤ₘ m₁ →
                                Γ₀′ ⊢[ m₁ ] L ≈[≥ m′ ] L′ ⦂ `↓[ m₀ ⇒ m₁ ] T →
                                ⊢[ m₁ ] `↓[ m₀ ⇒ m₁ ] T ⦂⋆ →
                                (T , m₀ , true) ∷ Γ₁ ⊢[ m ] M ≈[≥ m′ ] M′ ⦂ S →
                                --------------------------------------------------------------------------------------
                                Γ ⊢[ m ] `let-return[ m₁ ⇒ m₀ ] L `in M ≈[≥ m′ ] `let-return[ m₁ ⇒ m₀ ] L′ `in M′ ⦂ S

  `λ⦂-∘_                      : (S , m , true) ∷ Γ ⊢[ m ] L ≈[≥ m′ ] L′ ⦂ T →
                                ----------------------------------------------------------
                                Γ ⊢[ m ] `λ⦂[ m ] S ∘ L ≈[≥ m′ ] `λ⦂[ m ] S ∘ L′ ⦂ S `⊸ T

  _⊢_⦂_`$_                    : Γ ~ Γ₀ ⊞ Γ₁ →
                                Γ₀ ⊢[ m ] L ≈[≥ m′ ] L′ ⦂ T `⊸ S →
                                ⊢[ m ] T `⊸ S ⦂⋆ →
                                Γ₁ ⊢[ m ] M ≈[≥ m′ ] M′ ⦂ T →
                                --------------------------------------
                                Γ ⊢[ m ] L `$ M ≈[≥ m′ ] L′ `$ M′ ⦂ S

  `#_                         : x ⦂[ m ] S ∈ Γ →
                                --------------------------------
                                Γ ⊢[ m ] `# x ≈[≥ m′ ] `# x ⦂ S
