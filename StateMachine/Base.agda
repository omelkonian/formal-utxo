module StateMachine.Base where

open import Function using (_∘_; case_of_)

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_)
open import Data.Maybe   using (Maybe; nothing; fromMaybe; _>>=_)
  renaming (map to mapₘ; just to pure; ap to _<*>_) -- for idiom brackets
open import Data.List    using (List; null; []; _∷_; filter; map)
open import Data.Nat     using (ℕ)
  renaming (_≟_ to _≟ℕ_)

open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import UTxO.Hashing.MetaHash
open import UTxO.Types hiding (I)

-- For the sake of simplicity, we assume addresses to be just hashes.
Address = HashId
open import UTxO.Ledger            Address (λ x → x) _≟ℕ_ public
open import UTxO.TxUtilities       Address (λ x → x) _≟ℕ_ public
open import UTxO.Hashing.Tx        Address (λ x → x) _≟ℕ_ public
open import UTxO.Validity          Address (λ x → x) _≟ℕ_ public
open import UTxO.DecisionProcedure Address (λ x → x) _≟ℕ_ public

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

    -- The following forms break the `liveness` proof, as we cannot rewrite with the value of `final st`
    -- Possibly an Agda bug?

    -- (1) using case_of_
    -- case (final st , getContinuingOutputs ptx) of
    -- λ { (true  , outs  ) → pure (null outs)
    --   ; (false , o ∷ []) → ⦇ findData (PendingTxOutput.dataHash o) ptx == pure (toData st) ⦈
    --   ; (false , _     ) → pure false }

    -- (2) using `with`
    --   with final st | getContinuingOutputs ptx
    -- ... | true  | outs   = pure (null outs)
    -- ... | false | o ∷ [] = ⦇ findData (PendingTxOutput.dataHash o) ptx == pure (toData st) ⦈
    -- ... | false | _      = pure false

-- Create a transaction input.
infix 5 _←—_,_
_←—_,_ : ∀ {S I : Set} {{_ : IsData S}} {{_ : IsData I}}
       → TxOutputRef → I → StateMachine S I → TxInput
outputRef (r ←— _ , _ ) = r
redeemer  (_ ←— d , _ ) = toData d
validator (_ ←— _ , sm) = mkValidator sm

-- Create a transaction output.
infix 5 _—→_at_
_—→_at_ : ∀ {S I : Set} {{_ : IsData S}} {{_ : IsData I}}
        → S → Value → StateMachine S I → TxOutput
value   (_ —→ v at _ ) = v
address (_ —→ _ at sm) = (mkValidator sm) ♯
dataVal (d —→ _ at _ ) = toData d
