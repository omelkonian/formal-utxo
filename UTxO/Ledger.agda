------------------------------------------------------------------------
-- Transactions and ledgers.
------------------------------------------------------------------------

open import Data.Bool using (Bool)
open import Data.List using (List)

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import UTxO.Types
open import UTxO.Hashing.Base

module UTxO.Ledger
  (Address : Set)
  (_♯ₐ : Hash Address)
  (_≟ₐ_ : Decidable {A = Address} _≡_)
  where

record TxOutput : Set where
  field
    address : Address
    value   : Value
    dataVal : DATA

open TxOutput public

record Tx : Set where
  field
    inputs  : List TxInput -- T0D0: Set⟨TxInput⟩
    outputs : List TxOutput
    fee     : Value
    forge   : Value

open Tx public

Ledger : Set
Ledger = List Tx

runValidation : PendingTx → (i : TxInput) → (o : TxOutput) → Bool
runValidation ptx i o = validator i ptx (redeemer i) (dataVal o)
