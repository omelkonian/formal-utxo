------------------------------------------------------------------------
-- Naive hashing functions for UTxO types.
------------------------------------------------------------------------
module UTxO.Hashing.Types where

open import Prelude.Init

open import UTxO.Hashing.Base
open import UTxO.Value
open import UTxO.Types

_♯ₒᵣ : Hash TxOutputRef
o ♯ₒᵣ = merge♯ (hid o ∷ index o ∷ [])

_♯ᵢ : Hash TxInput
i ♯ᵢ = (outputRef i) ♯ₒᵣ

_♯ℤ : Hash ℤ
_♯ℤ = Integer.∣_∣

_♯ᵇ : Hash Bound
-∞     ♯ᵇ = 0
+∞     ♯ᵇ = 1
(t= n) ♯ᵇ = n + 2

_♯ˢ : Hash SlotRange
(b ⋯ b′) ♯ˢ = merge♯ (b ♯ᵇ ∷ b′ ♯ᵇ ∷ [])

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

_♯ᵥ : Hash Value
_♯ᵥ = hashList (hashPair (λ x → x) (hashList (hashPair (λ x → x) (λ x → x))))

_♯ₒ : Hash TxOutput
o ♯ₒ = merge♯ ((value o) ♯ᵥ ∷ address o ∷ [])
postulate injective♯ₒ : Injective _≡_ _≡_ _♯ₒ

_♯ₜₓ : Hash Tx
tx ♯ₜₓ = merge♯ ( (hashList _♯ᵢ) (inputs tx)
                ∷ (hashList _♯ₒ) (outputs tx)
                ∷ (forge tx) ♯ᵥ
                ∷ (range tx) ♯ˢ
                ∷ []
                )

infix 9 _♯ᵇ
infix 9 _♯ˢ
infix 9 _♯ℤ
infix 9 _♯ₒᵣ
infix 9 _♯ᵢ
infix 9 _♯ᵥ
infix 9 _♯ᵈ
infix 9 _♯ₒ
infix 9 _♯ₜₓ

postulate injective♯ₒᵣ : Injective _≡_ _≡_ _♯ₒᵣ
postulate injective♯ᵢ  : Injective _≡_ _≡_ _♯ᵢ
postulate injective♯ᵥ  : Injective _≡_ _≡_ _♯ᵥ
postulate injective♯ᵈ  : Injective _≡_ _≡_ _♯ᵈ
postulate injective♯ₜₓ : Injective _≡_ _≡_ _♯ₜₓ
