{-# OPTIONS --rewriting #-}
{- NB: We use REWRITE rules to help normalization of calls to the postulated hash function _♯. -}

module StateMachine.ExamplePlay where

open import Data.Product  using (_×_; _,_; proj₁)
open import Data.Bool     using (Bool; true; _∧_)
open import Data.Nat      using (ℕ)
  renaming (_≟_ to _≟ℕ_)
open import Data.List     using (List; []; [_]; _∷_; reverse)
open import Data.Integer  using (ℤ)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Hashing.MetaHash
open import UTxO.Types

open import StateMachine.Base
open import StateMachine.GuessingGame

-- dummy currency address, need a concrete number for decision procedure to compute
𝕍 = 3
postulate
  eq : gameValidator ♯ ≡ 𝕍
{-# REWRITE eq #-}

infix 4 _←—_
_←—_ : Tx → GameInput → TxInput
t ←— d = ((t ♯ₜₓ) indexed-at 0) ←— d , GameStateMachine

infix 4 _—→_
_—→_ : GameState → Value → TxOutput
s —→ v = s —→ v at GameStateMachine

-----------------------------------------------------------------------

-- define transactions
t₀ : Tx
inputs  t₀ = []
outputs t₀ = [ Initialised —→ $ 0 ]
forge   t₀ = $ 0
fee     t₀ = $ 0
range   t₀ = -∞ ⋯ +∞

t₁ : Tx
inputs  t₁ = [ t₀ ←— StartGame ("zero" ♯ₛₜᵣ) ]
outputs t₁ = [ Locked ("zero" ♯ₛₜᵣ) —→ $ 1 ]
forge   t₁ = $ 1
fee     t₁ = $ 0
range   t₁ = -∞ ⋯ +∞

t₂ : Tx
inputs  t₂ = [ t₁ ←— Guess "zero" ("one" ♯ₛₜᵣ) ]
outputs t₂ = [ Locked ("one" ♯ₛₜᵣ) —→ $ 1 ]
forge   t₂ = $ 0
fee     t₂ = $ 0
range   t₂ = -∞ ⋯ +∞

t₃ : Tx
inputs  t₃ = [ t₂ ←— Guess "one" ("two" ♯ₛₜᵣ) ]
outputs t₃ = [ Locked ("two" ♯ₛₜᵣ) —→ $ 1 ]
forge   t₃ = $ 0
fee     t₃ = $ 0
range   t₃ = -∞ ⋯ +∞

ex-ledger : ValidLedger (t₃ ∷ t₂ ∷ t₁ ∷ t₀ ∷ [])
ex-ledger = ∙ ⊕ t₀ ⊕ t₁ ⊕ t₂ ⊕ t₃
