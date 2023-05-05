------------------------------------------------------------
-- Dynamic Rules for λ□
------------------------------------------------------------

{-# OPTIONS --safe #-}
module Calculus.LambdaBox.OpSem where

open import Data.Nat using (ℕ; suc)

open import Calculus.GeneralOpSem
open import Calculus.LambdaBox.Syntax

data Value : Term → Set where
  `unit  : ------------
           Value `unit

  `box   : ∀ E →
           ---------------
           Value (`box E)

  `λ⦂_∙_ : ∀ A E →
           ------------------
           Value (`λ⦂ A ∙ E)

infix  25 wk[_↑¹_]_
infix  25 wk[_↑⁰_]_
infix  25 wk¹_
infix  25 wk⁰_
infix  25 [_/¹_]_
infix  25 [_/⁰_]_

wk[_↑¹_]_ : ℕ → ℕ → Term → Term
wk[ n ↑¹ u ] `unit              = `unit
wk[ n ↑¹ u ] `box E             = `box (wk[ n ↑¹ u ] E)
wk[ n ↑¹ u ] (`let-box E `in F) = `let-box wk[ n ↑¹ u ] E `in wk[ n ↑¹ suc u ] F
wk[ n ↑¹ u ] (`λ⦂ A ∙ E)        = `λ⦂ A ∙ wk[ n ↑¹ u ] E
wk[ n ↑¹ u ] (E `$ F)           = wk[ n ↑¹ u ] E `$ wk[ n ↑¹ u ] F
wk[ n ↑¹ u ] (`#¹ v)            = `#¹ wkidx[ n ↑ u ] v
wk[ n ↑¹ u ] (`#⁰ y)            = `#⁰ y

wk¹_ : Term → Term
wk¹_ = wk[ 1 ↑¹ 0 ]_

wk[_↑⁰_]_ : ℕ → ℕ → Term → Term
wk[ n ↑⁰ x ] `unit              = `unit
wk[ n ↑⁰ x ] `box E             = `box E
wk[ n ↑⁰ x ] (`let-box E `in F) = `let-box wk[ n ↑⁰ x ] E `in wk[ n ↑⁰ x ] F
wk[ n ↑⁰ x ] (`λ⦂ A ∙ E)        = `λ⦂ A ∙ wk[ n ↑⁰ suc x ] E
wk[ n ↑⁰ x ] (E `$ F)           = wk[ n ↑⁰ x ] E `$ wk[ n ↑⁰ x ] F
wk[ n ↑⁰ x ] (`#¹ v)            = `#¹ v
wk[ n ↑⁰ x ] (`#⁰ y)            = `#⁰ wkidx[ n ↑ x ] y

wk⁰_ : Term → Term
wk⁰_ = wk[ 1 ↑⁰ 0 ]_

[_/¹_]_ : Term → ℕ → Term → Term
[ E /¹ u ] `unit              = `unit
[ E /¹ u ] (`box F)           = `box ([ E /¹ u ] F)
[ E /¹ u ] (`let-box F `in G) = `let-box [ E /¹ u ] F `in [ wk¹ E /¹ suc u ] G
[ E /¹ u ] (`#¹ v)            = idx[ E / u ] v along `#¹_
[ E /¹ u ] (`#⁰ x)            = `#⁰ x
[ E /¹ u ] (`λ⦂ A ∙ F)        = `λ⦂ A ∙ [ E /¹ u ] F
[ E /¹ u ] (F `$ G)           = [ E /¹ u ] F `$ [ E /¹ u ] G

[_/⁰_]_ : Term → ℕ → Term → Term
[ E /⁰ x ] `unit              = `unit
[ E /⁰ x ] (`box F)           = `box F
[ E /⁰ x ] (`let-box F `in G) = `let-box [ E /⁰ x ] F `in [ wk¹ E /⁰ x ] G
[ E /⁰ x ] (`#¹ u)            = `#¹ u
[ E /⁰ x ] (`#⁰ y)            = idx[ E / x ] y along `#⁰_
[ E /⁰ x ] (`λ⦂ A ∙ F)        = `λ⦂ A ∙ [ wk⁰ E /⁰ suc x ] F
[ E /⁰ x ] (F `$ G)           = [ E /⁰ x ] F `$ [ E /⁰ x ] G

infix  4 _⟶_

data _⟶_ : Term → Term → Set where
  ξ-`let-box_`in- : E ⟶ E′ →
                    -------------------------------------
                    `let-box E `in F ⟶ `let-box E′ `in F

  β-`□            : -------------------------------------
                    `let-box `box E `in F ⟶ [ E /¹ 0 ] F

  ξ-_`$?          : E ⟶ E′ →
                    -----------------
                    E `$ F ⟶ E′ `$ F

  ξ-!_`$_         : Value E →
                    F ⟶ F′ →
                    -----------------
                    E `$ F ⟶ E `$ F′

  β-`→            : Value F →
                    --------------------------------
                    (`λ⦂ A ∙ E) `$ F ⟶ [ F /⁰ 0 ] E

open ⟶* _⟶_ public
