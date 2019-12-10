------------------------------------------------------------------------
-- Transactions and ledgers.
------------------------------------------------------------------------

open import Data.Bool using (Bool)
open import Data.List using (List)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Prelude.Set' as SET

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
    dataVal : DATA

open TxOutput public

record Tx : Set where
  field
    inputs  : List TxInput -- T0D0: Set⟨TxInput⟩
    outputs : List TxOutput
    fee     : Value
    forge   : Value
    range   : SlotRange

open Tx public

Ledger : Set
Ledger = List Tx

runValidation : PendingTx → (i : TxInput) → (o : TxOutput) → Bool
runValidation ptx i o = validator i ptx (redeemer i) (dataVal o)

-- Sets of outputs
_≟ᵒ_ : Decidable {A = TxOutput} _≡_
o ≟ᵒ o′
  with address o ≟ₐ address o′ | value o ≟ᶜ value o′ | dataVal o ≟ᵈ dataVal o′
... | no ¬p    | _        | _        = no λ{ refl → ¬p refl }
... | _        | no ¬p    | _        = no λ{ refl → ¬p refl }
... | _        | _        | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl | yes refl | yes refl = yes refl

module SETᵒ = SET {A = TxOutput} _≟ᵒ_
Set⟨TxOutput⟩ = Set' where open SETᵒ
