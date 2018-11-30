------------------------------------------------------------------------
-- Basic UTxO datatypes
------------------------------------------------------------------------

module Types where

open import Data.Nat    using (ℕ)
open import Data.Bool   using (Bool)
open import Data.String using (String)
open import Level       using (Level)

Address : Set
Address = ℕ

infix 9 _♯
postulate
  _♯ : ∀ {ℓ : Level} {A : Set ℓ} → A → Address

Value : Set
Value = ℕ

Id : Set
Id = ℕ

record State : Set where
  field
    height : ℕ

Script : Set
Script = String

postulate
  ⟦_⟧ᵥ : Script → (∀ {R : Set} → State → R → Bool)
  ⟦_⟧ᵣ : Script → (∀ {R : Set} → State → R)

record TxOutput : Set where
  field
    address : Address
    value   : Value
open TxOutput public

record TxOutputRef : Set where
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

