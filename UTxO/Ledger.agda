------------------------------------------------------------------------
-- Transactions and ledgers.
------------------------------------------------------------------------

open import Data.Bool using (Bool)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import UTxO.Types

module UTxO.Ledger (addresses : List Address) where

record TxOutput : Set where
  field
    value   : Value
    address : Index addresses

    Data       : 𝕌
    dataScript : State → el Data

open TxOutput public

record Tx : Set where
  field
    inputs  : List TxInput -- T0D0: Set⟨TxInput⟩
    outputs : List TxOutput
    forge   : Value
    fee     : Value

open Tx public

Ledger : Set
Ledger = List Tx

getState : Ledger → State
getState l = record { height = length l }

runValidation : PendingTx → (i : TxInput) → (o : TxOutput) → D i ≡ Data o → State → Bool
runValidation ptx i o refl st = validator i st (value o) ptx (redeemer i st) (dataScript o st)
