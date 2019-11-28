module StateMachine.Base where

open import Function using (_∘_; case_of_)

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool    using (Bool; true; false; _∧_)
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

data TxConstraints : Set where

  forge≡          : Value → TxConstraints
  valueSpent≡     : Value → TxConstraints
  thisValueSpent≡ : Value → TxConstraints
  valueToOwnHash≡ : Value → TxConstraints
  _&&_            : TxConstraints → TxConstraints → TxConstraints

infixr 5 _&&_

verifyConstraints : PendingTx → TxConstraints → Bool
verifyConstraints ptx (forge≡ v)          = ⌊ PendingTx.forge ptx ≟ᶜ v ⌋
verifyConstraints ptx (valueSpent≡ v)     = ⌊ valueSpent ptx ≟ᶜ v ⌋
verifyConstraints ptx (thisValueSpent≡ v) = ⌊ thisValueSpent ptx ≟ᶜ v ⌋
verifyConstraints ptx (valueToOwnHash≡ v) = ⌊ valueLockedBy ptx (ownHash ptx) ≟ᶜ v ⌋
verifyConstraints ptx (c && c′)           = verifyConstraints ptx c ∧ verifyConstraints ptx c′

-- [_,_]-satisfies-_ : Tx → TxConstraints → Set
-- [tx , l] -satisfies- constraints =
--   ∃[ i ] ∃[ i∈ ] T (verifyConstraints (mkPendingTx l tx i i∈ validTxRefs validOutputIndices) constraints)

record StateMachine (S I : Set) {{_ : IsData S}} {{_ : IsData I}} : Set where
  constructor SM[_,_,_]
  field
    isInitial : S → Bool
    isFinal   : S → Bool
    step      : S → I → Maybe (S × TxConstraints)

Validator : Set
Validator = PendingTx → DATA → DATA → Bool

mkValidator : ∀ {S I : Set} {{_ : IsData S}} {{_ : IsData I}}
  → StateMachine S I → Validator
mkValidator {S} {I} (SM[ init , final , step ]) ptx input′ currentState′
    = fromMaybe false ⦇ constraintsOK ∧ outputsOK ⦈
  where
    next : Maybe (S × TxConstraints)
    next with ⦇ step (fromData currentState′) (fromData input′) ⦈
    ... | pure r = r
    ... | _      = nothing

    constraintsOK : Maybe Bool
    constraintsOK = ⦇ verifyConstraints (pure ptx) ⦇ proj₂ next ⦈ ⦈

    outputsOK : Maybe Bool
    outputsOK = ⦇ proj₁ next ⦈ >>= λ st → case (final st , getContinuingOutputs ptx) of
      λ { (true  , outs)   → pure (null outs)
        ; (false , o ∷ []) → ⦇ findData (PendingTxOutput.dataHash o) ptx == pure (toData st) ⦈
        ; (false , _     ) → pure false }
