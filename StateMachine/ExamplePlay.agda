{-# OPTIONS --rewriting #-}
{- NB: We use REWRITE rules to help normalization of calls to the postulated hash function _♯. -}

module StateMachine.ExamplePlay where

open import Data.Product  using (_×_; _,_; proj₁)
open import Data.Bool     using (Bool; true; _∧_)
open import Data.Nat      using (ℕ)
  renaming (_≟_ to _≟ℕ_)
open import Data.List     using (List; []; [_]; _∷_; reverse)
open import Data.Integer  using (ℤ)

open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite

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

postulate ℂ≡ : policyₛₘ ♯ ≡ 1
{-# REWRITE ℂ≡ #-}

postulate 𝕍≡ : validatorₛₘ ♯ ≡ 2
{-# REWRITE 𝕍≡ #-}

-- smart constructors
withState : GameState → Tx
withState st = record def
  { outputs        = [ st —→ threadₛₘ ]
  ; datumWitnesses = [ toData st ♯ᵈ , toData st ] }

-----------------------------------------------------------------------
-- game states

st₁ = Locked ("0" ♯ₛₜᵣ)
  --> Guess "0" "1"
st₂ = Locked ("1" ♯ₛₜᵣ)

-- transactions
t₁ : Tx
t₁ = record (withState st₁)
  { forge    = threadₛₘ
  ; policies = [ policyₛₘ ] }

t₂ : Tx
t₂ = record (withState st₂)
  { inputs  = [ (t₁ ♯ₜₓ) indexed-at 0 ←— (Guess "0" ("1" ♯ₛₜᵣ) , st₁) ] }

ex-play : ValidLedger (t₂ ∷ t₁ ∷ [])
ex-play = ∙ ⊕ t₁ ⊕ t₂
