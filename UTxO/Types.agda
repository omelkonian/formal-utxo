------------------------------------------------------------------------
-- Basic UTxO types.
------------------------------------------------------------------------
module UTxO.Types where

open import Level     using (Level; 0ℓ)
open import Data.Bool using (Bool)
open import Data.Nat  using (ℕ; _≟_)
open import Data.List using (List; map; length)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Re-export list utilities.
open import Prelude.Lists public

-- Re-export type universe 𝕌.
open import UTxO.Data.TYPE public

-- Re-export currency maps.
open import UTxO.Data.Currency public
  using ( Value; $; $0; _≟ᶜ_; _+ᶜ_; sumᶜ; keys; values; mapValues )

------------------------------------------------------------------------
-- Basic types.

HashId : Set
HashId = ℕ

record State : Set where
  field
    height : ℕ
open State public

getState : ∀ {A : Set} → List A → State
getState l = record { height = length l }

--------------------------------------------------------------------------------------
-- Pending transactions (i.e. parts of the transaction being passed to a validator).

record PendingTxInput : Set where
  field
    value         : Value
    validatorHash : HashId
    redeemerHash  : HashId
    -- dataHash      : HashId

record PendingTxOutput : Set where
  field
    value         : Value
    dataHash      : HashId
    -- validatorHash : HashId

record PendingTx : Set where
  field
    txHash : HashId   -- ^ hash of the current validated transaction

    inputs  : List PendingTxInput
    outputs : List PendingTxOutput
    forge   : Value
    fee     : Value

--------------------------------------------------------------------------
-- Output references and inputs.

data DATA : Set where
 I      : ℤ → DATA
 LIST   : List DATA → DATA
 CONSTR : ℕ → List DATA → DATA
 MAP    : List (DATA × DATA) → DATA
 
record TxOutputRef : Set where
  constructor _indexed-at_
  field
    id    : HashId
    index : ℕ
open TxOutputRef public

record TxInput : Set where
  field
    outputRef : TxOutputRef
    validator : Value     -- ^ output value
              → PendingTx -- ^ parts of the currently validated transaction
              → DATA      -- ^ result value of the redeemer script
              → DATA      -- ^ result value of the data script
              → Bool
    redeemer  : DATA

open TxInput public



------------------------------------------------------------------------
-- Set modules/types.

import Prelude.Set' as SET

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
