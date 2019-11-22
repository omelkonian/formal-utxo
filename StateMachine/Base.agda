module StateMachine.Base where

open import Function using (_∘_)

open import Data.Product using (proj₁; proj₂)
open import Data.Bool    using (Bool; true; false; _∧_)
open import Data.Maybe   using (Maybe; nothing; just; ap; fromMaybe)
open import Data.List    using (List; null; []; _∷_; filter; map)
open import Data.Nat     using ()
  renaming (_≟_ to _≟ℕ_)

open import UTxO.Types using ( HashId; Value
                             ; DATA; IsData; toData; fromData; _==_
                             ; PendingTx; PendingTxOutput; findData; getContinuingOutputs )

-- A State Machine library for smart contracts, based on very similar
-- library for Plutus Smart contracts

-- Specification of a state machine, consisting of a transition
-- function that determines the next state from the current state and
-- an input, and a checking function that checks the validity of the
-- transition in the context of the current transaction.

record StateMachine (S I : Set) : Set where
  constructor SM[_,_,_]
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

Validator : Set
Validator = Value → PendingTx → DATA → DATA → Bool

pure  : ∀ {A : Set} → A → Maybe A
pure = just
_<*>_ = ap

mkValidator : ∀ {S I : Set}
  → IsData S
  → IsData I
  → StateMachine S I → Validator
mkValidator {S} {I} ds di (SM[ step , check , final ]) _ ptx currentState′ input′
    = fromMaybe false ⦇ checkOK ∧ stateAndOutputsOK ⦈
  where
    currentState : Maybe S
    currentState = fromData ds currentState′

    input : Maybe I
    input = fromData di currentState′

    checkOK : Maybe Bool
    checkOK = ⦇ check currentState input (pure ptx) ⦈

    checkFinal : S → Maybe Bool
    checkFinal newState with final newState | getContinuingOutputs ptx
    ... | true  | outs     = pure (null outs)
    ... | false | (o ∷ []) = ⦇ (findData (PendingTxOutput.dataHash o) ptx) == pure (toData ds newState) ⦈
    ... | false | _        = pure false

    stateAndOutputsOK : Maybe Bool
    stateAndOutputsOK with ⦇ step currentState input ⦈
    ... | just (just s) = checkFinal s
    ... | _             = nothing
