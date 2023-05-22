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

-- Main properties of Elevator
import Calculus.Elevator.Properties

-- Algorithmic typing of Elevator
import Calculus.Elevator.Algorithmic

-- Soundness/completeness of algorithmic typing of Elevator
import Calculus.Elevator.Algorithmic.Properties

-- ModeSpec for λ↓↑₂
import Calculus.Elevator.Embedding.LambdaBox.ModeSpec

-- Definition of λ□
import Calculus.LambdaBox.Syntax
import Calculus.LambdaBox.Typing
import Calculus.LambdaBox.OpSem

-- Embedding, its soundness and completeness, and bisimulation from λ□ into λ↓↑₂
import Calculus.Elevator.Embedding.LambdaBox

-- ModeSpec for
import Calculus.Elevator.Embedding.LinearLambda.ModeSpec

-- Definition of DILL
import Calculus.LinearLambda.Syntax
import Calculus.LinearLambda.Typing
import Calculus.LinearLambda.OpSem

-- Embedding, its soundness and completeness, and bisimulation from DILL into
import Calculus.Elevator.Embedding.LinearLambda
