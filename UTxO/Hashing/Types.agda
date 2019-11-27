------------------------------------------------------------------------
-- Naive hashing functions for basic types.

-- NOTE these hash functions can create collisions and are only for
-- testing/readability of examples
------------------------------------------------------------------------

module UTxO.Hashing.Types where

open import Data.Product using (_×_; _,_)
open import Data.List    using (List; []; _∷_)
open import Data.Integer using (ℤ; ∣_∣)

open import UTxO.Hashing.Base
open import UTxO.Types

_♯ᵒʳ : Hash TxOutputRef
o ♯ᵒʳ = merge♯ (id o ∷ index o ∷ [])
postulate injective♯ᵒʳ : Injective _♯ᵒʳ

_♯ⁱ : Hash TxInput
i ♯ⁱ = (outputRef i) ♯ᵒʳ
postulate injective♯ⁱ : Injective _♯ⁱ

_♯ᵛ : Hash Value
_♯ᵛ = λ x → x
postulate injective♯ᵥ : Injective _♯ᵛ

_♯ℤ : Hash ℤ
_♯ℤ = ∣_∣

_♯ᵈ : Hash DATA
_♯ᵈˢ : Hash (List DATA)
_♯ᵈᵈˢ : Hash (List (DATA × DATA))

I z ♯ᵈ         = z ♯ℤ
H n ♯ᵈ         = n
LIST ds ♯ᵈ     = ds ♯ᵈˢ
CONSTR n ds ♯ᵈ = merge♯ (n ∷ (ds ♯ᵈˢ) ∷ [])
MAP ds′ ♯ᵈ     = ds′ ♯ᵈᵈˢ

[] ♯ᵈˢ       = 0
(d ∷ ds) ♯ᵈˢ = merge♯ ((d ♯ᵈ) ∷ (ds ♯ᵈˢ) ∷ [])

[] ♯ᵈᵈˢ              = 0
((d , d′) ∷ ds) ♯ᵈᵈˢ = merge♯ ((d ♯ᵈ) ∷ (d′ ♯ᵈ) ∷ (ds ♯ᵈᵈˢ) ∷ [])

infix 9 _♯ᵒʳ
infix 9 _♯ⁱ
infix 9 _♯ᵛ
infix 9 _♯ᵈ
