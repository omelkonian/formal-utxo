{-# OPTIONS --allow-unsolved-metas #-}
module StateMachine.Base where

open import Function using (_∘_)

open import Data.Product using (proj₁; proj₂)
open import Data.Bool    using (Bool; true; false; _∧_)
open import Data.Maybe   using (Maybe; nothing; fromMaybe)
  renaming (map to _<$>_; just to pure; ap to _<*>_) -- for idiom brackets
open import Data.List    using (List; null; []; _∷_; filter; map)
open import Data.Nat     using ()
  renaming (_≟_ to _≟ℕ_)

open import UTxO.Types

data S : Set where
  -- ADD type of state, e.g. recording values owned by certain hashes?

data Move : Set where
  -- ADD possible moves

instance
  IsDataⁱ : IsData Move
  toData   {{IsDataⁱ}} = {!!}
  fromData {{IsDataⁱ}} = {!!}

record StateMachine : Set where
  constructor SM[_,_,_]
  field

    smTransition : S → Move → Maybe S
    -- ^ The transition function of the state machine. 'nothing'
    -- indicates an invalid transition from the current state.

    smCheck : S → Move → Bool
    -- ^ The condition checking function. Checks whether a given state is allowed.

    smFinal : S → Bool
    -- ^ The final state predicate. Indicates whether a given state is
    -- final (the machine halts in that state).

Validator : Set
Validator = State → DATA → Bool

mkValidator : StateMachine → Validator
mkValidator (SM[ step , check , final ]) st input′
    = fromMaybe false ⦇ checkOK ∧ stateAndOutputsOK ⦈
  where
    currentState : S
    currentState = {!!} -- extract this from the current state of the ledger, etc...

    input : Maybe Move
    input = fromData input′

    checkOK : Maybe Bool
    checkOK = check currentState <$> input

    checkFinal : S → Maybe Bool
    checkFinal newState = {!!}
    --   with final newState
    -- ... | true  | outs     = pure (null outs)
    -- ... | false | (o ∷ []) = ⦇ findData (PendingTxOutput.dataHash o) ptx == pure (toData newState) ⦈
    -- ... | false | _        = pure false

    stateAndOutputsOK : Maybe Bool
    stateAndOutputsOK with step currentState <$> input
    ... | pure (pure s) = checkFinal s
    ... | _             = nothing
