module Main where

-- ** Hashing
open import UTxO.Hashing.Base
open import UTxO.Hashing.Types

-- ** Basic UTxO definitions
open import UTxO.Value
open import UTxO.Types
open import UTxO.TxUtilities
open import UTxO.Validity

-- ** UTxO example
open import UTxO.ExampleLedger

-- ** UTxO meta-theory
open import UTxO.Uniqueness
open import UTxO.GlobalPreservation

-- ** Provenance
open import UTxO.Provenance
open import UTxO.FocusedProvenance
open import UTxO.FocusedProvenanceNF

-- ** Constraint-emitting Machines
open import StateMachine.Base
open import StateMachine.GuessingGame
-- *** takes around 1 hour to type-check... T0D0: profile to debug performance
-- open import StateMachine.ExamplePlay
open import StateMachine.Properties
open import StateMachine.ReplayProtection

-- ** Bisimulation between CEMs and UTxO ledgers
open import Bisimulation.Base
open import Bisimulation.Soundness
open import Bisimulation.Completeness
open import Bisimulation
