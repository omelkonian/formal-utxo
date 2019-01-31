------------------------------------------------------------------------
-- Basic UTxO types.
------------------------------------------------------------------------
module Types where

open import Level       using (Level; 0ℓ)
open import Data.Bool   using (Bool)

open import Data.Nat using (ℕ; _≟_)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Basic types.

Address : Set
Address = ℕ

Id : Set
Id = ℕ

Value : Set
Value = ℕ

$ : ℕ → Value
$ v = v

record State : Set where
  field
    height : ℕ
open State

infix 9 _♯
postulate
  _♯ : ∀ {ℓ} {A : Set ℓ} → A → Address
  ♯-injective : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ♯ ≡ y ♯ → x ≡ y

record TxOutputRef : Set where
  constructor _indexed-at_
  field
    id    : Id
    index : ℕ
open TxOutputRef public

record TxInput : Set₁ where
  field
    outputRef : TxOutputRef

    R         : Set
    redeemer  : State → R
    validator : State → R → Bool
open TxInput public

------------------------------------------------------------------------
-- Set modules/types.

import Data.Set' as SET

-- Sets of output references
_≟ₒ_ : Decidable {A = TxOutputRef} _≡_
x ≟ₒ y with id x ≟ id y | index x ≟ index y
... | no ¬p    | _        = no λ{refl → ¬p refl}
... | _        | no ¬p′   = no λ{refl → ¬p′ refl}
... | yes refl | yes refl = yes refl

module SETₒ = SET {A = TxOutputRef} _≟ₒ_

Set⟨TxOutputRef⟩ : Set
Set⟨TxOutputRef⟩ = Set'
  where open SETₒ

{- T0D0
-- Sets of transaction inputs
_≟ᵢ_ : Decidable {A = TxInput} _≡_
x ≟ᵢ y with outputRef x ≟ₒ outputRef y
          | redeemer  x ≟ₛ redeemer  y
          | validator x ≟ₛ validator y
... | no ¬p    | _        | _        = no λ{refl → ¬p refl}
... | _        | no ¬p    | _        = no λ{refl → ¬p refl}
... | _        | _        | no ¬p    = no λ{refl → ¬p refl}
... | yes refl | yes refl | yes refl = yes refl

module SETᵢ = SET {A = TxInput} _≟ᵢ_

Set⟨TxInput⟩ : Set
Set⟨TxInput⟩ = Set'
  where open SETᵢ
-}
