module StateMachine.Base where

open import Function using (_∘_; case_of_)

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_)
open import Data.Maybe   using (Maybe; nothing; fromMaybe; _>>=_)
  renaming (map to mapₘ; just to pure; ap to _<*>_) -- for idiom brackets
open import Data.List    using (List; null; []; _∷_; filter; map)
open import Data.Nat     using ()
  renaming (_≟_ to _≟ℕ_)

open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import UTxO.Types hiding (I)

-- A State Machine library for smart contracts, based on very similar
-- library for Plutus Smart contracts

-- Specification of a state machine, consisting of a transition
-- function that determines the next state from the current state and
-- an input, and a checking function that checks the validity of the
-- transition in the context of the current transaction.

record StateMachine (S I : Set) {{_ : IsData S}} {{_ : IsData I}} : Set where
  constructor SM[_,_,_]
  field
    isInitial : S → Bool
    isFinal   : S → Bool
    step      : S → I → Maybe S

open StateMachine public

Validator : Set
Validator = PendingTx → DATA → DATA → Bool

mkValidator : ∀ {S I : Set} {{_ : IsData S}} {{_ : IsData I}}
  → StateMachine S I → Validator
mkValidator {S} {I} SM[ _ , final , step ] ptx input state
    = fromMaybe false (state′ >>= outputsOK)
  where
    state′ : Maybe S
    state′ with ⦇ step (fromData state) (fromData input) ⦈
    ... | pure r = r
    ... | _      = nothing

    outs : List PendingTxOutput
    outs = getContinuingOutputs ptx

    outputsOK : S → Maybe Bool
    outputsOK st =
      if final st then
        pure (null outs)
      else
        case outs of λ{ (o ∷ []) → ⦇ findData (PendingTxOutput.dataHash o) ptx == pure (toData st) ⦈
                      ; _        → pure false }

    -- The following forms break the `liveness` proof, as we can rewrite with the value of `final st`
    -- Possibly an Agda bug?

    -- (1) using case_of_
    -- case (final st , getContinuingOutputs ptx) of
    -- λ { (true  , outs  ) → pure (null outs)
    --   ; (false , o ∷ []) → ⦇ findData (PendingTxOutput.dataHash o) ptx == pure (toData st) ⦈
    --   ; (false , _     ) → pure false }

    -- (2) using with pattern-matching
    --   with final st | getContinuingOutputs ptx
    -- ... | true  | outs   = pure (null outs)
    -- ... | false | o ∷ [] = ⦇ findData (PendingTxOutput.dataHash o) ptx == pure (toData st) ⦈
    -- ... | false | _      = pure false
