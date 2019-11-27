------------------------------------------------------------------------
-- Basic UTxO types.
------------------------------------------------------------------------
module UTxO.Types where

open import Function using (_∘_)

open import Data.Bool    using (Bool)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List    using (List; map; length; []; _∷_; filter; foldr; sum)
open import Data.Char    using (Char; toℕ; fromℕ)
open import Data.String  using (String; toList; fromList)
open import Data.Nat     using (ℕ)
  renaming (_≟_ to _≟ℕ_)
open import Data.Integer using (ℤ; +_; ∣_∣)
  renaming (_≟_ to _≟ℤ_)
open import Data.Maybe   using (Maybe; nothing)
  renaming (map to mapₘ; just to pure; ap to _<*>_) -- for idiom brackets

open import Relation.Nullary                      using (yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Basic types.

-- TODO Quantity should be ℤ

ℍ        = ℕ

Quantity = ℕ
Address  = ℍ
DataHash = ℍ

-----------------------------------------
-- First-order data values.

data DATA : Set where
 I      : ℤ → DATA
 H      : ℍ → DATA
 LIST   : List DATA → DATA
 CONSTR : ℕ → List DATA → DATA
 MAP    : List (DATA × DATA) → DATA

record IsData (A : Set) : Set where
  field
    toData   : A → DATA
    fromData : DATA → Maybe A
open IsData {{...}} public

instance
  IsDataˡ : ∀ {A : Set} → {{_ : IsData A}} → IsData (List A)
  toData   {{IsDataˡ}} = LIST ∘ map toData
  fromData {{IsDataˡ}} = λ{ (LIST xs) → sequence (map fromData xs) ; _ → nothing }
    where sequence = foldr (λ c cs → ⦇ c ∷ cs ⦈) (pure [])

  IsDataᶜ : IsData Char
  toData   {{IsDataᶜ}}       = I ∘ +_ ∘ toℕ
  fromData {{IsDataᶜ}} (I z) = pure (fromℕ ∣ z ∣)
  fromData {{IsDataᶜ}} _     = nothing

  IsDataˢ : IsData String
  toData   {{IsDataˢ}} = toData ∘ toList
  fromData {{IsDataˢ}} = mapₘ fromList ∘ fromData

--------------------------------------------------------------------------------------
-- Pending transactions (i.e. parts of the transaction being passed to a validator).

record PendingTxOutput : Set where
  field
    value         : Quantity
    validatorHash : Address
    dataHash      : DataHash

record PendingTxInput : Set where
  field
    -- outputRef     : OutputRef
    validatorHash : Address
    dataHash      : DataHash
    redeemerHash  : DataHash
    value         : Quantity

record PendingTx : Set where
  field
    inputInfo     : List PendingTxInput
    thisInput     : PendingTxInput
    outputInfo    : List PendingTxOutput
    -- validityInterval : SlotRange
    dataWitnesses : List (DataHash × DATA)
    --txHash        : ℍ
    fee           : Quantity
    forge         : Quantity

--------------------------------------------------------------------------
-- Output references and inputs.

record TxOutputRef : Set where
  constructor _indexed-at_
  field
    id    : ℍ
    index : ℕ
open TxOutputRef public

record TxInput : Set where
  field
    outputRef : TxOutputRef
    validator : PendingTx -- ^ parts of the currently validated transaction
              → DATA      -- ^ result value of the redeemer script
              → DATA      -- ^ result value of the data script
              → Bool
    dataVal   : DATA
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

findData : ℍ → PendingTx → Maybe DATA
findData dsh (record {dataWitnesses = ws}) = toMaybe (map proj₂ (filter ((_≟ℕ dsh) ∘ proj₁) ws))
  where
    toMaybe : ∀ {A : Set} → List A → Maybe A
    toMaybe []      = nothing
    toMaybe (x ∷ _) = pure x

getContinuingOutputs : PendingTx → List PendingTxOutput
getContinuingOutputs record { thisInput = record { validatorHash = in♯ } ; outputInfo = outs }
  = filter ((_≟ℕ in♯) ∘ PendingTxOutput.validatorHash) outs

ownCurrencySymbol : PendingTx → ℍ
ownCurrencySymbol = PendingTxInput.validatorHash ∘ PendingTx.thisInput

valueSpent : PendingTx → Quantity
valueSpent = sum ∘ map PendingTxInput.value ∘ PendingTx.inputInfo
