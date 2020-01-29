------------------------------------------------------------------------
-- Naive hashing functions for UTxO types.
------------------------------------------------------------------------
open import Function.Definitions using (Injective)

open import Data.List using ([]; _∷_)

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import UTxO.Hashing.Base

module UTxO.Hashing.Tx
  (Address : Set)
  (_♯ₐ : Hash Address)
  (_≟ₐ_ : Decidable {A = Address} _≡_)
  where

open import UTxO.Hashing.Types Address _♯ₐ _≟ₐ_
open import UTxO.Value Address _♯ₐ _≟ₐ_
open import UTxO.Types Address _♯ₐ _≟ₐ_
open import UTxO.Ledger Address _♯ₐ _≟ₐ_

_♯Q : Hash Quantities
q ♯Q = hashList (hashPair _♯ₐ _♯ᵥ) q

_♯ₒ : Hash TxOutput
o ♯ₒ = merge♯ ((value o) ♯Q ∷ (address o) ♯ₐ ∷ [])
postulate injective♯ₒ : Injective _≡_ _≡_ _♯ₒ

_♯ₜₓ : Hash Tx
tx ♯ₜₓ = merge♯ ( (hashList _♯ᵢ) (inputs tx)
                ∷ (hashList _♯ₒ) (outputs tx)
                ∷ (forge tx) ♯Q
                ∷ (fee tx) ♯Q
                ∷ (range tx) ♯ˢ
                ∷ []
                )
postulate injective♯ₜₓ : Injective _≡_ _≡_ _♯ₜₓ

infix 9 _♯ₒ
infix 9 _♯ₜₓ
