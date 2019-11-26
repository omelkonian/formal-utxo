------------------------------------------------------------------------
-- Transactions and ledgers.
------------------------------------------------------------------------

open import Data.Bool using (Bool)
open import Data.List using (List)

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
    address : Address
    value   : Value

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

runValidation : State → TxInput → Bool
runValidation state i = validator i state (redeemer i)
