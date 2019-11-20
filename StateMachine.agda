module StateMachine where

open import Data.Maybe using (Maybe)
open import Data.Bool using (Bool)

open import UTxO.Types using (PendingTx)

-- A State Machine library for smart contracts, based on very similar
-- library for Plutus Smart contracts

-- Specification of a state machine, consisting of a transition
-- function that determines the next state from the current state and
-- an input, and a checking function that checks the validity of the
-- transition in the context of the current transaction.

record StateMachine (S I : Set) : Set where
  field

    smTransition : S → I → Maybe S
    -- ^ The transition function of the state machine. 'nothing'
    -- indicates an invalid transition from the current state.
    
    smCheck : S → I → PendingTx → Bool
    -- ^ The condition checking function. Checks whether a given state
    -- transition is allowed given the 'PendingTx'.
    
    smFinal : S → Bool
    -- ^ The final state predicate. Indicates whether a given state is
    -- final (the machine halts in that state).
