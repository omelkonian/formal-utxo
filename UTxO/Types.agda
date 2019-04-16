------------------------------------------------------------------------
-- Basic UTxO types.
------------------------------------------------------------------------
module UTxO.Types where

open import Level     using (Level; 0ℓ)
open import Data.Bool using (Bool)
open import Data.Nat  using (ℕ; _≟_)
open import Data.List using (List)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Re-export list utilities.
open import Utilities.Lists public

-- Re-export type universe 𝕌.
open import Data.TYPE public

-- Re-export currency maps.
open import Utilities.Currency public
  using ( Value; $; _+ᶜ_; sumᶜ; values )

------------------------------------------------------------------------
-- Basic types.

Address : Set
Address = ℕ

Id : Set
Id = ℕ

record State : Set where
  field
    height : ℕ
open State public

--------------------------------------------------------------------------------------
-- Pending transactions (i.e. parts of the transaction being passed to a validator).

record PendingTxInput : Set where
  field
    value         : Value
    validatorHash : Id
    redeemerHash  : Id
    -- dataHash      : Id

record PendingTxOutput : Set where
  field
    value         : Value
    dataHash      : Id
    -- validatorHash : Id

record PendingTx : Set where
  field
    txHash : Id   -- ^ hash of the current validated transaction

    inputs  : List PendingTxInput
    outputs : List PendingTxOutput
    forge   : Value
    fee     : Value

--------------------------------------------------------------------------------------
-- Output references and inputs.

record TxOutputRef : Set where
  constructor _indexed-at_
  field
    id    : Id
    index : ℕ
open TxOutputRef public

record TxInput : Set where
  field
    outputRef : TxOutputRef

    R         : 𝕌 -- ^ intermediate type used by the redeemer script
    D         : 𝕌 -- ^ intermediate type used by the data script

    redeemer  : State → el R
    validator : State     -- ^ current blockchain state
              → Value     -- ^ output value
              → PendingTx -- ^ parts of the currently validated transaction
              → el R      -- ^ result value of the redeemer script
              → el D      -- ^ result value of the data script
              → Bool

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
