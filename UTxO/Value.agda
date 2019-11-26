------------------------------------------------------------------------
-- No multi-currency support.
------------------------------------------------------------------------
module UTxO.Value where

open import Data.Bool using (Bool)
open import Data.List using (List; sum)
open import Data.Nat  using (ℕ; _+_)
  renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (_≥?_)

open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

Value = ℕ

$0 : Value
$0 = 0

$ : ℕ → Value
$ v = v

_+ᶜ_ : Value → Value → Value
_+ᶜ_ = _+_

sumᶜ : List Value → Value
sumᶜ = sum

infix 4 _≟ᶜ_
_≟ᶜ_ : Decidable {A = Value} _≡_
_≟ᶜ_ = _≟ℕ_

_≥ᶜ_ : Value → Value → Bool
v ≥ᶜ v′ = ⌊ v ≥? v′ ⌋
