------------------------------------------------------------------------
-- Naive hashing functions for basic types.
------------------------------------------------------------------------
module UTxO.Hashing.Types where

open import Data.Product using (_×_; _,_)
open import Data.List    using (List; []; _∷_)
open import Data.Integer using (ℤ; ∣_∣)

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
_♯ᵥ = λ x → x
postulate injective♯ᵥ : Injective _♯ᵥ

_♯ℤ : Hash ℤ
_♯ℤ = ∣_∣

_♯ᵈ : Hash DATA
_♯ᵈˢ : Hash (List DATA)
_♯ᵈˢ′ : Hash (List (DATA × DATA))

I z ♯ᵈ         = z ♯ℤ
H n ♯ᵈ         = n
LIST ds ♯ᵈ     = ds ♯ᵈˢ
CONSTR n ds ♯ᵈ = merge♯ (n ∷ (ds ♯ᵈˢ) ∷ [])
MAP ds′ ♯ᵈ     = ds′ ♯ᵈˢ′

[] ♯ᵈˢ       = 0
(d ∷ ds) ♯ᵈˢ = merge♯ ((d ♯ᵈ) ∷ (ds ♯ᵈˢ) ∷ [])

[] ♯ᵈˢ′              = 0
((d , d′) ∷ ds) ♯ᵈˢ′ = merge♯ ((d ♯ᵈ) ∷ (d′ ♯ᵈ) ∷ (ds ♯ᵈˢ′) ∷ [])

infix 9 _♯ₛₜ
infix 9 _♯ₒᵣ
infix 9 _♯ᵢ
infix 9 _♯ᵥ
infix 9 _♯ᵈ
