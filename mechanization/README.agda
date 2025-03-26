-- This mechanization uses
-- * Agda v2.6.3
-- * agda-stdlib of commit e0879db86

{-# OPTIONS --safe #-}
module README where

-- Definition of Mode Specification in Elevator
import Calculus.AdjND.ModeSpec

-- Declartive Typing and Equivalence of Elevator
import Calculus.AdjND.Typing
import Calculus.AdjND.Typing.Properties

-- Operational Semantics of Elevator
import Calculus.AdjND.OpSem
import Calculus.AdjND.OpSem.Properties

-- Type Safety and Mode Safety of Elevator
import Calculus.AdjND.Properties

-- ModeSpec for Adjoint λ□
import Calculus.AdjND.Embedding.LambdaBox.ModeSpec

-- Definition of Original λ□
import Calculus.LambdaBox.Syntax
import Calculus.LambdaBox.Typing
import Calculus.LambdaBox.OpSem

-- Translation, its Soundness and Completeness, and Bisimulation from Original λ□ into Adjoint λ□
import Calculus.AdjND.Embedding.LambdaBox

-- ModeSpec for Adjoint DILL
import Calculus.AdjND.Embedding.DILL.ModeSpec

-- Definition of Original DILL
import Calculus.DILL.Syntax
import Calculus.DILL.Typing
import Calculus.DILL.OpSem

-- Translation, its Soundness and Completeness, and Bisimulation from Original DILL into Adjoint DILL
import Calculus.AdjND.Embedding.DILL

-- Algorithmic Typing of Elevator
import Calculus.AdjND.Algorithmic

-- Soundness/Completeness of Algorithmic Typing of Elevator
import Calculus.AdjND.Algorithmic.Properties

-- Completeness of Elevator with regard to Adjoint sequent calculus
import Calculus.AdjSC.Sequent
