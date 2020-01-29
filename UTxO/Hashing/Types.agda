------------------------------------------------------------------------
-- Naive hashing functions for basic types.
------------------------------------------------------------------------
open import UTxO.Hashing.Base

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module UTxO.Hashing.Types
  (Address : Set)
  (_♯ₐ : Hash Address)
  (_≟ₐ_ : Decidable {A = Address} _≡_)
  where
open import Function.Definitions using (Injective)

open import Data.Product using (_×_; _,_)
open import Data.List    using (List; []; _∷_)
open import Data.Integer using (ℤ; ∣_∣)
open import Data.Nat     using (_+_)

open import Relation.Binary.PropositionalEquality using (_≡_)

open import UTxO.Value Address _♯ₐ _≟ₐ_ hiding (_+_)
open import UTxO.Types Address _♯ₐ _≟ₐ_

_♯ₒᵣ : Hash TxOutputRef
o ♯ₒᵣ = merge♯ (id o ∷ index o ∷ [])

_♯ᵢ : Hash TxInput
i ♯ᵢ = (outputRef i) ♯ₒᵣ

_♯ᵥ : Hash Value
_♯ᵥ = λ x → x

_♯ℤ : Hash ℤ
_♯ℤ = ∣_∣

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

infix 9 _♯ᵇ
infix 9 _♯ˢ
infix 9 _♯ℤ
infix 9 _♯ₒᵣ
infix 9 _♯ᵢ
infix 9 _♯ᵥ
infix 9 _♯ᵈ

postulate injective♯ₒᵣ : Injective _≡_ _≡_ _♯ₒᵣ
postulate injective♯ᵢ  : Injective _≡_ _≡_ _♯ᵢ
postulate injective♯ᵥ  : Injective _≡_ _≡_ _♯ᵥ
postulate injective♯ᵈ  : Injective _≡_ _≡_ _♯ᵈ
