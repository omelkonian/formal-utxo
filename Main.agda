{-# OPTIONS --rewriting #-}
module Main where

-- ** Basic UTxO definitions
open import UTxO.Hashing.Base
open import UTxO.Value
open import UTxO.Types
open import UTxO.Hashing.Types
open import UTxO.TxUtilities
open import UTxO.Validity

-- ** An example of a (correct-by-construction) ledger
open import UTxO.ExampleLedger

-- ** UTxO meta-theory
open import UTxO.Uniqueness
open import UTxO.GlobalPreservation

-- ** Provenance
open import UTxO.TokenProvenance
open import UTxO.TokenProvenanceNF

-- ** Constraint-emitting Machines
open import StateMachine.Base
open import StateMachine.Properties

-- ** Bisimulation between CEMs and UTxO ledgers
open import Bisimulation.Base
open import Bisimulation.Soundness
open import Bisimulation.Completeness
open import Bisimulation

-- ** StateMachine examples
open import StateMachine.Examples.GuessingGame
open import StateMachine.Examples.MultiSig
open import StateMachine.Examples.Counter
-- open import StateMachine.Examples.TeaCoffee
-- open import StateMachine.Examples.Timer

-- ** Transfering CEM properties
open import StateMachine.Inductive
open import StateMachine.Initiality
open import StateMachine.Extract
