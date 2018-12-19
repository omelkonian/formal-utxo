------------------------------------------------------------------------
-- Basic UTxO datatypes
------------------------------------------------------------------------

open import Data.Nat    using (ℕ; _≟_)
open import Data.Bool   using (Bool)
open import Data.String using (String)
open import Data.List   using (List)
open import Level       using (Level)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.String.Unsafe using () renaming (_≟_ to _≟ₛ_)

open import Utilities.Lists
open import Basic

module Types (addresses : List Address) where

------------------------------------------------------------------------
-- Basic types.

infix 9 _♯
postulate
  _♯ : ∀ {ℓ : Level} {A : Set ℓ} → A → Address

Script : Set
Script = String

postulate
  ⟦_⟧ᵥ : Script → (∀ {R : Set} → State → R → Bool)
  ⟦_⟧ᵣ : Script → (∀ {R : Set} → State → R)

record TxOutput : Set where
  constructor $_at_
  field
    value   : Value
    address : Index addresses
open TxOutput public

record TxOutputRef : Set where
  constructor _indexed-at_
  field
    id    : Id
    index : ℕ
open TxOutputRef public

record TxInput : Set where
  field
    outputRef : TxOutputRef
    validator : Script
    redeemer  : Script
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
