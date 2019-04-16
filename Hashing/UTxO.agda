------------------------------------------------------------------------
-- Naive hashing functions for UTxO types.
------------------------------------------------------------------------
open import Data.Fin      using (toℕ)

open import UTxO.Types
open import Hashing.Base
open import Hashing.Types

module Hashing.UTxO (addresses : List Address) where

open import UTxO.Ledger addresses

_♯ₒ : Hash TxOutput
o ♯ₒ = merge♯ ((value o) ♯ᵥ ∷ toℕ (address o) ∷ [])
postulate injective♯ₒ : Injective _♯ₒ

_♯ₜₓ : Hash Tx
tx ♯ₜₓ = merge♯ ( (hashList _♯ᵢ) (inputs tx)
                ∷ (hashList _♯ₒ) (outputs tx)
                ∷ (forge tx) ♯ᵥ
                ∷ (fee tx) ♯ᵥ
                ∷ []
                )
postulate injective♯ₜₓ : Injective _♯ₜₓ

infix 9 _♯ₒ
infix 9 _♯ₜₓ
