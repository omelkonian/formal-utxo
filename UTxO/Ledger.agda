------------------------------------------------------------------------
-- Transactions and ledgers.
------------------------------------------------------------------------

open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Product using (_×_)

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import UTxO.Hashing.Base
open import UTxO.Types

module UTxO.Ledger
  (Address : Set)
  (_♯ₐ : Hash Address)
  (_≟ₐ_ : Decidable {A = Address} _≡_)
  where

record TxOutput : Set where
  field
    address  : Address -- this is the hash of the validator
    value    : Quantity
    dataHash : ℍ

open TxOutput public

record Tx : Set where
  field
    inputs  : List TxInput -- T0D0: Set⟨TxInput⟩
    outputs : List TxOutput
    -- validityInterval : SlotRange
    dataWitnesses : List (DataHash × DATA)
    fee     : Quantity
    forge   : Quantity

open Tx public

Ledger : Set
Ledger = List Tx

-- this doesn't use the output anymore
runValidation : PendingTx → (i : TxInput) → (o : TxOutput) → Bool
runValidation ptx i o = validator i ptx (redeemer i) (dataVal i)
