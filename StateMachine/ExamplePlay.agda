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

open import StateMachine.Base hiding (mkValidator)
open import StateMachine.GuessingGame

-- available addresses
Address = ℕ

open import UTxO.Ledger            Address (λ x → x) _≟ℕ_
open import UTxO.TxUtilities       Address (λ x → x) _≟ℕ_
open import UTxO.Hashing.Tx        Address (λ x → x) _≟ℕ_
open import UTxO.Validity          Address (λ x → x) _≟ℕ_
open import UTxO.DecisionProcedure Address (λ x → x) _≟ℕ_

_at_←—_ : Tx → ℕ → GameInput → TxInput
outputRef (t at i ←— _) = (t ♯ₜₓ) indexed-at i
redeemer  (_ at _ ←— d) = toData d
validator (_ at _ ←— _) = mkValidator

_—→_at_ : GameState → Value → Address → TxOutput
value   (_ —→ v at _) = v
address (_ —→ _ at a) = a
dataVal (d —→ _ at _) = toData d

-----------------------------------------------------------------------

-- dummy currency address, need a concrete number for decision procedure to compute
𝕍 = 3
postulate
  eq : mkValidator ♯ ≡ 𝕍
{-# REWRITE eq #-}

-----------------------------------------------------------------------

-- define transactions
t₀ : Tx
inputs  t₀ = []
outputs t₀ = [ Initialised —→ $0 at 𝕍 ]
forge   t₀ = $0
fee     t₀ = $0

t₁ : Tx
inputs  t₁ = t₀ at 0 ←— StartGame ("zero" ♯ₛₜᵣ)
           ∷ []
outputs t₁ = [ Locked ("zero" ♯ₛₜᵣ) —→ $ 1 at 𝕍 ]
forge   t₁ = $ 1
fee     t₁ = $0

t₂ : Tx
inputs  t₂ =  [ t₁ at 0 ←— Guess "zero" ("one" ♯ₛₜᵣ) ]
outputs t₂ =  [ Locked ("one" ♯ₛₜᵣ) —→ $ 1 at 𝕍 ]
forge   t₂ = $0
fee     t₂ = $0

t₃ : Tx
inputs  t₃ =  [ t₂ at 0 ←— Guess "one" ("two" ♯ₛₜᵣ) ]
outputs t₃ =  [ Locked ("two" ♯ₛₜᵣ) —→ $ 1 at 𝕍 ]
forge   t₃ = $0
fee     t₃ = $0

ex-ledger : ValidLedger (t₃ ∷ t₂ ∷ t₁ ∷ t₀ ∷ [])
ex-ledger = ∙ ⊕ t₀ ⊕ t₁ ⊕ t₂ ⊕ t₃
