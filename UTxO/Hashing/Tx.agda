------------------------------------------------------------------------
-- Naive hashing functions for UTxO types.

-- NOTE these hash functions can create collisions and are only for
-- testing/readability of examples
------------------------------------------------------------------------
open import Data.List using ([]; _∷_)

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import UTxO.Types
open import UTxO.Hashing.Base
open import UTxO.Hashing.Types

module UTxO.Hashing.Tx
  (Address : Set)
  (_♯ᵃ : Hash Address)
  (_≟ᵃ_ : Decidable {A = Address} _≡_)
  where

open import UTxO.Ledger Address _♯ᵃ _≟ᵃ_

_♯ᵒ : Hash TxOutput
o ♯ᵒ = merge♯ ((value o) ♯ᵛ ∷ (address o) ♯ᵃ ∷ [])
postulate injective♯ₒ : Injective _♯ᵒ

_♯ᵗˣ : Hash Tx
tx ♯ᵗˣ = merge♯ ( (hashList _♯ⁱ) (inputs tx)
                ∷ (hashList _♯ᵒ) (outputs tx)
                ∷ (forge tx) ♯ᵛ
                ∷ (fee tx) ♯ᵛ
                ∷ []
                )
postulate injective♯ᵗˣ : Injective _♯ᵗˣ

infix 9 _♯ᵒ
infix 9 _♯ᵗˣ
