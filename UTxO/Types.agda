------------------------------------------------------------------------
-- Basic UTxO types.
------------------------------------------------------------------------
module UTxO.Types where

open import Function using (_∘_)

open import Data.Bool    using (Bool)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.List    using (List; map; length; []; _∷_; filter)
open import Data.Nat     using (ℕ)
  renaming (_≟_ to _≟ℕ_)
open import Data.Integer using (ℤ)
  renaming (_≟_ to _≟ℤ_)

open import Relation.Nullary                      using (yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋)
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

-----------------------------------------
-- First-order data values.

data DATA : Set where
 I      : ℤ → DATA
 H      : HashId → DATA
 LIST   : List DATA → DATA
 CONSTR : ℕ → List DATA → DATA
 MAP    : List (DATA × DATA) → DATA

record IsData (A : Set) : Set where
  field
    toData   : A → DATA
    fromData : DATA → Maybe A
open IsData public

--------------------------------------------------------------------------------------
-- Pending transactions (i.e. parts of the transaction being passed to a validator).

record PendingTxInput : Set where
  field
    -- outputRef     : OutputRef
    validatorHash : HashId
    dataHash      : HashId
    redeemerHash  : HashId
    value         : Value

record PendingTxOutput : Set where
  field
    value         : Value
    validatorHash : HashId
    dataHash      : HashId

record PendingTx : Set where
  field
    inputInfo     : List PendingTxInput
    thisInput     : PendingTxInput
    outputInfo    : List PendingTxOutput
    -- validityInterval : SlotRange
    dataWitnesses : List (HashId × DATA)
    txHash        : HashId
    fee           : Value
    forge         : Value

--------------------------------------------------------------------------
-- Output references and inputs.

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
x ≟ₒ y with id x ≟ℕ id y | index x ≟ℕ index y
... | no ¬p    | _        = no λ{refl → ¬p refl}
... | _        | no ¬p′   = no λ{refl → ¬p′ refl}
... | yes refl | yes refl = yes refl

module SETₒ = SET {A = TxOutputRef} _≟ₒ_

Set⟨TxOutputRef⟩ : Set
Set⟨TxOutputRef⟩ = Set'
  where open SETₒ

-- Sets of DATA.
_≟ᵈ_ : Decidable {A = DATA} _≡_
_≟ᵈₗ_ : Decidable {A = List DATA} _≡_
_≟ᵈ×ₗ_ : Decidable {A = List (DATA × DATA)} _≡_

I x ≟ᵈ I x₁
  with x ≟ℤ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
I x ≟ᵈ H x₁ = no (λ ())
I x ≟ᵈ LIST x₁ = no (λ ())
I x ≟ᵈ CONSTR x₁ x₂ = no (λ ())
I x ≟ᵈ MAP x₁ = no (λ ())

H x ≟ᵈ I x₁ = no (λ ())
H x ≟ᵈ H x₁
  with x ≟ℕ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
H x ≟ᵈ LIST x₁ = no (λ ())
H x ≟ᵈ CONSTR x₁ x₂ = no (λ ())
H x ≟ᵈ MAP x₁ = no (λ ())

LIST x ≟ᵈ I x₁ = no (λ ())
LIST x ≟ᵈ H x₁ = no (λ ())
LIST x ≟ᵈ LIST x₁
  with x ≟ᵈₗ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
LIST x ≟ᵈ CONSTR x₁ x₂ = no (λ ())
LIST x ≟ᵈ MAP x₁ = no (λ ())

CONSTR x x₁ ≟ᵈ I x₂ = no (λ ())
CONSTR x x₁ ≟ᵈ H x₂ = no (λ ())
CONSTR x x₁ ≟ᵈ LIST x₂ = no (λ ())
CONSTR x x₁ ≟ᵈ CONSTR x₂ x₃
  with x ≟ℕ x₂ | x₁ ≟ᵈₗ x₃
... | no ¬p    | _        = no λ{ refl → ¬p refl }
... | _        | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl | yes refl = yes refl
CONSTR x x₁ ≟ᵈ MAP x₂ = no (λ ())

MAP x ≟ᵈ I x₁ = no (λ ())
MAP x ≟ᵈ H x₁ = no (λ ())
MAP x ≟ᵈ LIST x₁ = no (λ ())
MAP x ≟ᵈ CONSTR x₁ x₂ = no (λ ())
MAP x ≟ᵈ MAP x₁
  with x ≟ᵈ×ₗ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl

[]       ≟ᵈₗ []      = yes refl
[]       ≟ᵈₗ (_ ∷ _) = no λ()
(_ ∷ _)  ≟ᵈₗ []      = no λ()
(x ∷ xs) ≟ᵈₗ (y ∷ ys)
  with x ≟ᵈ y | xs ≟ᵈₗ ys
... | no ¬p    | _        = no λ{ refl → ¬p refl }
... | _        | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl | yes refl = yes refl

[]       ≟ᵈ×ₗ []      = yes refl
[]       ≟ᵈ×ₗ (_ ∷ _) = no λ()
(_ ∷ _)  ≟ᵈ×ₗ []      = no λ()
((x , y) ∷ xs) ≟ᵈ×ₗ ((x′ , y′) ∷ ys)
  with x ≟ᵈ x′ | y ≟ᵈ y′ | xs ≟ᵈ×ₗ ys
... | no ¬p    | _        | _        = no λ{ refl → ¬p refl }
... | _        | no ¬p    | _        = no λ{ refl → ¬p refl }
... | _        | _        | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl | yes refl | yes refl = yes refl

module SETᵈ = SET {A = DATA} _≟ᵈ_
Set⟨DATA⟩ : Set
Set⟨DATA⟩ = Set' where open SETᵈ

_==_ : DATA → DATA → Bool
x == y = ⌊ x ≟ᵈ y ⌋

-- Utilities for pending transactions.

findData : HashId → PendingTx → Maybe DATA
findData dsh (record {dataWitnesses = ws}) = toMaybe (map proj₂ (filter ((_≟ℕ dsh) ∘ proj₁) ws))
  where
    toMaybe : ∀ {A : Set} → List A → Maybe A
    toMaybe []      = nothing
    toMaybe (x ∷ _) = just x

getContinuingOutputs : PendingTx → List PendingTxOutput
getContinuingOutputs record { thisInput = record { validatorHash = in♯ } ; outputInfo = outs }
  = filter ((_≟ℕ in♯) ∘ PendingTxOutput.validatorHash) outs
