{-
A State Machine library for smart contracts, based on very similar
library for Plutus Smart contracts

Specification of a state machine, consisting of a transition
function that determines the next state from the current state and
an input, and a checking function that checks the validity of the
transition in the context of the current transaction.
-}
module StateMachine.Base where

open import Function using (_∘_; case_of_)

open import Data.Unit    using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_; T)
open import Data.Maybe   using (Maybe; nothing; fromMaybe; _>>=_)
  renaming (map to mapₘ; just to pure; ap to _<*>_) -- for idiom brackets
open import Data.List    using (List; null; []; _∷_; [_]; filter; map; length; and)
open import Data.Nat     using (ℕ)
  renaming (_≟_ to _≟ℕ_)

open import Data.Maybe.Properties using (just-injective)

open import Data.List.Membership.Propositional using (_∈_)

open import Relation.Nullary                      using (yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; inspect; trans; sym; cong)
  renaming ([_] to ≡[_])

open import Prelude.General
open import Prelude.Lists using (enumerate)

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities
open import UTxO.Validity

--------------------------
-- Transaction constraints

record TxConstraints : Set where
  field
    forge≡ : Maybe Value
    range≡ : Maybe SlotRange
    spent≥ : Maybe Value

open TxConstraints public

defConstraints : TxConstraints
defConstraints = record {forge≡ = nothing; range≡ = nothing; spent≥ = nothing}

_>>=ₜ_ : ∀ {a : Set} → Maybe a → (a → Bool) → Bool
ma >>=ₜ f = fromMaybe true (ma >>= pure ∘ f)

verifyTxInfo : TxInfo → TxConstraints → Bool
verifyTxInfo tx tx≡ =
  (forge≡ tx≡ >>=ₜ λ v → ⌊ TxInfo.forge tx ≟ᶜ v ⌋) ∧
  (range≡ tx≡ >>=ₜ λ r → ⌊ TxInfo.range tx ≟ˢ r ⌋) ∧
  (spent≥ tx≡ >>=ₜ λ v → valueSpent tx ≥ᶜ v)

verifyTx : Ledger → Tx → TxConstraints → Bool
verifyTx l tx = verifyTxInfo (mkTxInfo l tx)

-------------------------------------
-- Constraint Emitting Machines (CEM)

record StateMachine (S I : Set) {{_ : IsData S}} {{_ : IsData I}} : Set where
  constructor SM[_,_,_]
  field
    isInitial : S → Bool
    isFinal   : S → Bool
    step      : S → I → Maybe (S × TxConstraints)

open StateMachine public

mkValidator : ∀ {S I : Set} {{_ : IsData S}} {{_ : IsData I}}
  → StateMachine S I → Validator
mkValidator {S} {I} SM[ _ , final , step ] ptx input state
    = fromMaybe false do (state′ , tx≡) ← runStep
                         pure (outputsOK state′ ∧ verifyTxInfo (txInfo ptx) tx≡)
  where
    runStep : Maybe (S × TxConstraints)
    runStep with ⦇ step (fromData state) (fromData input) ⦈
    ... | pure r = r
    ... | _      = nothing

    outs : List OutputInfo
    outs = getContinuingOutputs ptx

    outputsOK : S → Bool
    outputsOK st =
      if final st then
        null outs
      else
        case outs of λ{ (o ∷ []) → ⌊ (OutputInfo.dataHash o) ≟ℕ (toData st) ♯ᵈ ⌋
                      ; _        → false }

-- Create a transaction input.
infix 5 _←—_,_
_←—_,_ : ∀ {S I : Set} {{_ : IsData S}} {{_ : IsData I}}
       → TxOutputRef → I × S → StateMachine S I → TxInput
outputRef (r ←— _       , _ ) = r
redeemer  (_ ←— (i , _) , _ ) = toData i
validator (_ ←— _       , sm) = mkValidator sm
dataVal   (_ ←— (_ , d) , _ ) = toData d

-- Create a transaction output.
infix 5 _—→_at_
_—→_at_ : ∀ {S I : Set} {{_ : IsData S}} {{_ : IsData I}}
        → S → Value → StateMachine S I → TxOutput
value    (_ —→ v at _ ) = v
address  (_ —→ _ at sm) = (mkValidator sm) ♯
dataHash (d —→ _ at _ ) = (toData d) ♯ᵈ
