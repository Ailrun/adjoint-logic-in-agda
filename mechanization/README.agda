-- This mechanization uses
-- * Agda v2.6.3
-- * agda-stdlib of commit e0879db86

{-# OPTIONS --safe #-}
module README where

-- Definition of Mode Specification in Elevator
import Calculus.Elevator.ModeSpec

-- Declartive Typing and Equivalence of Elevator
import Calculus.Elevator.Typing
import Calculus.Elevator.Typing.Properties

-- Operational Semantics of Elevator
import Calculus.Elevator.OpSem
import Calculus.Elevator.OpSem.Properties

-- Type Safety and Mode Safety of Elevator
import Calculus.Elevator.Properties

-- ModeSpec for Adjoint λ□
import Calculus.Elevator.Embedding.LambdaBox.ModeSpec

-- Definition of Original λ□
import Calculus.LambdaBox.Syntax
import Calculus.LambdaBox.Typing
import Calculus.LambdaBox.OpSem

-- Translation, its Soundness and Completeness, and Bisimulation from Original λ□ into Adjoint λ□
import Calculus.Elevator.Embedding.LambdaBox

-- ModeSpec for Adjoint DILL
import Calculus.Elevator.Embedding.LinearLambda.ModeSpec

-- Definition of Original DILL
import Calculus.LinearLambda.Syntax
import Calculus.LinearLambda.Typing
import Calculus.LinearLambda.OpSem

-- Translation, its Soundness and Completeness, and Bisimulation from Original DILL into Adjoint DILL
import Calculus.Elevator.Embedding.LinearLambda

-- Algorithmic Typing of Elevator
import Calculus.Elevator.Algorithmic

-- Soundness/Completeness of Algorithmic Typing of Elevator
import Calculus.Elevator.Algorithmic.Properties

-- Completeness of Elevator with regard to Adjoint sequent calculus
import Calculus.Adjoint.Sequent
