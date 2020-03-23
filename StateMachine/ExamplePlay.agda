{-# OPTIONS --rewriting #-}
{- NB: We use REWRITE rules to help normalization of calls to the postulated hash function _♯. -}

module StateMachine.ExamplePlay where

open import Agda.Builtin.Equality.Rewrite

open import Data.Product  using (_,_)
open import Data.List     using ([]; [_]; _∷_)

open import Relation.Binary.PropositionalEquality using (_≡_)

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types
open import UTxO.Validity

open import Prelude.Default
open import UTxO.Defaults

open import StateMachine.Base
open import StateMachine.GuessingGame

open CEM {sm = GameStateMachine}

-----------------------------------------------------------------------
-- dummy concrete hashes, for decision procedure to compute

postulate ℂ≡ : policyₛₘ ♯ ≡ 0
{-# REWRITE ℂ≡ #-}

postulate 𝕍≡ : validatorₛₘ ♯ ≡ 1
{-# REWRITE 𝕍≡ #-}

-----------------------------------------------------------------------
-- game states

st₁ = Locked ("0" ♯ₛₜᵣ)
  --> Guess "0" "1"
st₂ = Locked ("1" ♯ₛₜᵣ)

-- transactions
t₁ : Tx
t₁ = record (withOutputs [ st₁ ])
  { forge    = threadₛₘ
  ; policies = [ policyₛₘ ] }

t₂ : Tx
t₂ = record (withOutputs [ st₂ ])
  { inputs  = [ (t₁ ♯ₜₓ) indexed-at 0 ←— (Guess "0" ("1" ♯ₛₜᵣ) , st₁) ] }

ex-play : ValidLedger (t₂ ∷ t₁ ∷ [])
ex-play = ∙ ⊕ t₁ ⊕ t₂
