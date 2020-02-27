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
open import UTxO.Value
open import UTxO.Types
open import UTxO.Validity

open import StateMachine.Base
open import StateMachine.GuessingGame

-- dummy currency address, need a concrete number for decision procedure to compute
𝕍 = 1
postulate
  eq : gameValidator ♯ ≡ 𝕍
{-# REWRITE eq #-}

infix 4 _←—_
_←—_ : Tx → (GameInput × GameState) → TxInput
t ←— d = ((t ♯ₜₓ) indexed-at 0) ←— d , GameStateMachine

infix 4 _—→_
_—→_ : GameState → Value → TxOutput
s —→ v = s —→ v at GameStateMachine

-----------------------------------------------------------------------

𝔸 : CurrencySymbol
𝔸 = 𝕍

𝕋 : TokenName
𝕋 = 0

$_ : Quantity → Value
$_ v = [ 𝔸 , [ 𝕋 , v ] ]

-----------------------------------------------------------------------

-- game states

st₀ = Initialised 𝔸 𝕋 ("0" ♯ₛₜᵣ)
  --> ForgeToken
st₁ = Locked 𝔸 𝕋 ("0" ♯ₛₜᵣ)
  --> Guess "0" "1"
st₂ = Locked 𝔸 𝕋 ("1" ♯ₛₜᵣ)

-- define transactions
t₀ : Tx
inputs  t₀ = []
outputs t₀ = [ st₀ —→ $0 ]
forge   t₀ = $0
fee     t₀ = $0
range   t₀ = -∞ ⋯ +∞

t₁ : Tx
inputs  t₁ = [ t₀ ←— (ForgeToken , st₀) ]
outputs t₁ = [ st₁ —→ $ 1 ]
forge   t₁ = $ 1
fee     t₁ = $0
range   t₁ = -∞ ⋯ +∞

t₂ : Tx
inputs  t₂ = [ t₁ ←— (Guess "0" ("1" ♯ₛₜᵣ) , st₁) ]
outputs t₂ = [ st₂ —→ $ 1 ]
forge   t₂ = $ 0
fee     t₂ = $0
range   t₂ = -∞ ⋯ +∞

ex-play : ValidLedger (t₂ ∷ t₁ ∷ t₀ ∷ [])
ex-play = ∙ ⊕ t₀ ⊕ t₁ ⊕ t₂
