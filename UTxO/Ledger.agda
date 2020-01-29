------------------------------------------------------------------------
-- Transactions and ledgers.
------------------------------------------------------------------------

open import Data.Bool using (Bool)
open import Data.List using (List;[];_∷_)
open import Data.Product using (_×_;_,_)
open import Data.Nat using (ℕ;zero;suc) renaming (_≟_ to _≟ℕ_) 
open import Data.Maybe using (Maybe;nothing;just)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Prelude.Set' as SET

open import UTxO.Hashing.Base

module UTxO.Ledger
  (Address : Set)
  (_♯ₐ : Hash Address)
  (_≟ₐ_ : Decidable {A = Address} _≡_)
  where

open import UTxO.Value Address _♯ₐ _≟ₐ_
open import UTxO.Types Address _♯ₐ _≟ₐ_



record TxOutput : Set where
  field
    address : Address
    value   : Quantities
    dataHash : HashId -- is this the right kind of hash?

open TxOutput public

record Tx : Set where
  field
    inputs  : List TxInput -- T0D0: Set⟨TxInput⟩
    outputs : List TxOutput
    fee     : Quantities
    forge   : Quantities
    range   : SlotRange

open Tx public

Ledger : Set
Ledger = List Tx

runValidation : PendingTx → (i : TxInput) → Bool
runValidation ptx i = validator i ptx (redeemer i) (dataVal i)

-- Sets of outputs
_≟ᵒ_ : Decidable {A = TxOutput} _≡_
o ≟ᵒ o′
  with address o ≟ₐ address o′ | value o ≟ value o′ | dataHash o ≟ℕ dataHash o′
... | no ¬p    | _        | _        = no λ{ refl → ¬p refl }
... | _        | no ¬p    | _        = no λ{ refl → ¬p refl }
... | _        | _        | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl | yes refl | yes refl = yes refl

module SETᵒ = SET {A = TxOutput} _≟ᵒ_
Set⟨TxOutput⟩ = Set' where open SETᵒ

-- -}
