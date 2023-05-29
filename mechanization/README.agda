-- This mechanization uses
-- * Agda v2.6.3
-- * agda-stdlib of commit 2839cec94

{-# OPTIONS --safe #-}
module README where

-- Declartive typing of Elevator
import Calculus.Elevator.Typing
import Calculus.Elevator.Typing.Properties

-- Operational semantics of Elevator
import Calculus.Elevator.OpSem

-- Type safety of Elevator
import Calculus.Elevator.Properties

-- Non-interference of Elevator
import Calculus.Elevator.OpSem.Properties

-- ModeSpec for Adjoint λ□
import Calculus.Elevator.Embedding.LambdaBox.ModeSpec

-- Definition of Original λ□
import Calculus.LambdaBox.Syntax
import Calculus.LambdaBox.Typing
import Calculus.LambdaBox.OpSem

-- Translation, its soundness and completeness, and bisimulation from Original λ□ into Adjoint λ□
import Calculus.Elevator.Embedding.LambdaBox

-- ModeSpec for Adjoint DILL
import Calculus.Elevator.Embedding.LinearLambda.ModeSpec

-- Definition of Original DILL
import Calculus.LinearLambda.Syntax
import Calculus.LinearLambda.Typing
import Calculus.LinearLambda.OpSem

-- Translation, its soundness and completeness, and bisimulation from Original DILL into Adjoint DILL
import Calculus.Elevator.Embedding.LinearLambda

-- Algorithmic typing of Elevator
import Calculus.Elevator.Algorithmic

-- Soundness/completeness of algorithmic typing of Elevator
import Calculus.Elevator.Algorithmic.Properties
