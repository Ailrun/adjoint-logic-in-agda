------------------------------------------------------------
-- Dynamic Rules for DP Modal Calculus
------------------------------------------------------------

{-# OPTIONS --safe #-}
module Calculus.LinearLambda.OpSem where

open import Data.Nat using (ℕ; suc)

open import Calculus.GeneralOpSem
open import Calculus.LinearLambda.Syntax

data Value : Term → Set where
  `unit  : ------------
           Value `unit

  `bang  : ∀ I →
           ---------------
           Value (`bang I)

  `λ⦂_∘_ : ∀ P I →
           ------------------
           Value (`λ⦂ P ∘ I)

infix  25 wk[_↑¹_]_
infix  25 wk[_↑⁰_]_
infix  25 wk¹_
infix  25 wk⁰_
infix  25 [_/¹_]_
infix  25 [_/⁰_]_

wk[_↑¹_]_ : ℕ → ℕ → Term → Term
wk[ n ↑¹ u ] `unit               = `unit
wk[ n ↑¹ u ] `bang I             = `bang (wk[ n ↑¹ u ] I)
wk[ n ↑¹ u ] (`let-bang I `in F) = `let-bang wk[ n ↑¹ u ] I `in wk[ n ↑¹ suc u ] F
wk[ n ↑¹ u ] (`λ⦂ P ∘ I)         = `λ⦂ P ∘ wk[ n ↑¹ u ] I
wk[ n ↑¹ u ] (I `$ J)            = wk[ n ↑¹ u ] I `$ wk[ n ↑¹ u ] J
wk[ n ↑¹ u ] (`#¹ v)             = `#¹ wkidx[ n ↑ u ] v
wk[ n ↑¹ u ] (`#⁰ y)             = `#⁰ y

wk¹_ : Term → Term
wk¹_ = wk[ 1 ↑¹ 0 ]_

wk[_↑⁰_]_ : ℕ → ℕ → Term → Term
wk[ n ↑⁰ x ] `unit               = `unit
wk[ n ↑⁰ x ] `bang I             = `bang I
wk[ n ↑⁰ x ] (`let-bang I `in J) = `let-bang wk[ n ↑⁰ x ] I `in wk[ n ↑⁰ x ] J
wk[ n ↑⁰ x ] (`λ⦂ P ∘ I)         = `λ⦂ P ∘ wk[ n ↑⁰ suc x ] I
wk[ n ↑⁰ x ] (I `$ J)            = wk[ n ↑⁰ x ] I `$ wk[ n ↑⁰ x ] J
wk[ n ↑⁰ x ] (`#¹ v)             = `#¹ v
wk[ n ↑⁰ x ] (`#⁰ y)             = `#⁰ wkidx[ n ↑ x ] y

wk⁰_ : Term → Term
wk⁰_ = wk[ 1 ↑⁰ 0 ]_

[_/¹_]_ : Term → ℕ → Term → Term
[ I /¹ u ] `unit               = `unit
[ I /¹ u ] (`bang J)           = `bang ([ I /¹ u ] J)
[ I /¹ u ] (`let-bang J `in K) = `let-bang [ I /¹ u ] J `in [ wk¹ I /¹ suc u ] K
[ I /¹ u ] (`#¹ v)             = idx[ I / u ] v along `#¹_
[ I /¹ u ] (`#⁰ x)             = `#⁰ x
[ I /¹ u ] (`λ⦂ P ∘ J)         = `λ⦂ P ∘ [ I /¹ u ] J
[ I /¹ u ] (J `$ K)            = [ I /¹ u ] J `$ [ I /¹ u ] K

[_/⁰_]_ : Term → ℕ → Term → Term
[ I /⁰ x ] `unit               = `unit
[ I /⁰ x ] (`bang J)           = `bang J
[ I /⁰ x ] (`let-bang J `in K) = `let-bang [ I /⁰ x ] J `in [ wk¹ I /⁰ x ] K
[ I /⁰ x ] (`#¹ u)             = `#¹ u
[ I /⁰ x ] (`#⁰ y)             = idx[ I / x ] y along `#⁰_
[ I /⁰ x ] (`λ⦂ P ∘ J)         = `λ⦂ P ∘ [ wk⁰ I /⁰ suc x ] J
[ I /⁰ x ] (J `$ K)            = [ I /⁰ x ] J `$ [ I /⁰ x ] K

infix  4 _⟶_

data _⟶_ : Term → Term → Set where
  ξ-`let-bang_`in- : I ⟶ I′ →
                     -------------------------------------
                     `let-bang I `in J ⟶ `let-bang I′ `in J

  β-`!             : -------------------------------------
                     `let-bang `bang I `in J ⟶ [ I /¹ 0 ] J

  ξ-_`$?           : I ⟶ I′ →
                     -----------------
                     I `$ J ⟶ I′ `$ J

  ξ-!_`$_          : Value I →
                     J ⟶ J′ →
                     -----------------
                     I `$ J ⟶ I `$ J′

  β-`⊸             : Value J →
                     --------------------------------
                     (`λ⦂ P ∘ I) `$ J ⟶ [ J /⁰ 0 ] I

open ⟶* _⟶_ public
