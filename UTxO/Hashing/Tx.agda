------------------------------------------------------------------------
-- Naive hashing functions for UTxO types.
------------------------------------------------------------------------
open import Data.List using ([]; _∷_)

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import UTxO.Types
open import UTxO.Hashing.Base
open import UTxO.Hashing.Types

module UTxO.Hashing.Tx
  (Address : Set)
  (_♯ₐ : Hash Address)
  (_≟ₐ_ : Decidable {A = Address} _≡_)
  where

open import UTxO.Ledger Address _♯ₐ _≟ₐ_

_♯ₒ : Hash TxOutput
o ♯ₒ = merge♯ ((value o) ♯ᵥ ∷ (address o) ♯ₐ ∷ [])
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
