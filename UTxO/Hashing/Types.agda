------------------------------------------------------------------------
-- Naive hashing functions for basic types.
------------------------------------------------------------------------
module UTxO.Hashing.Types where

open import Data.Product using (_,_)
open import Data.List    using ([]; _∷_)

open import UTxO.Hashing.Base
open import UTxO.Types

_♯ₛₜ : Hash State
st ♯ₛₜ = height st
postulate injective♯ₛₜ : Injective _♯ₛₜ

_♯ₒᵣ : Hash TxOutputRef
o ♯ₒᵣ = merge♯ (id o ∷ index o ∷ [])
postulate injective♯ₒᵣ : Injective _♯ₒᵣ

_♯ᵢ : Hash TxInput
i ♯ᵢ = (outputRef i) ♯ₒᵣ
postulate injective♯ᵢ : Injective _♯ᵢ

_♯ᵥ : Hash Value
_♯ᵥ = hashList (hashPair (λ x → x) (hashList (hashPair (λ x → x) (λ x → x))))
postulate injective♯ᵥ : Injective _♯ᵥ

infix 9 _♯ₛₜ
infix 9 _♯ₒᵣ
infix 9 _♯ᵢ
infix 9 _♯ᵥ
