------------------------------------------------------------------------
-- Basic UTxO types.
------------------------------------------------------------------------
module UTxO.Types where

open import Prelude.Init hiding (_∋_)
open import Prelude.General
open import Prelude.Lists
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.DecEq
open import Prelude.Unsafe using (fromℕ∘toℕ; toℕ∘fromℕ; fromList∘toList; toList∘fromList)

open import UTxO.Hashing.Base
open import UTxO.Value

------------------------------------------------------------------------
-- Basic types.

Time : Set
Time = ℕ

Address : Set
Address = HashId

-----------------------------------------
-- First-order data values.

data DATA : Set where
 I      : ℤ → DATA
 H      : HashId → DATA
 LIST   : List DATA → DATA
 CONSTR : ℕ → List DATA → DATA
 MAP    : List (DATA × DATA) → DATA
{-# TERMINATING #-}
unquoteDecl DecEq-Data = DERIVE DecEq [ quote DATA , DecEq-Data ]

record IsData (A : Set) : Set where
  field
    toData   : A → DATA
    fromData : DATA → Maybe A
    from∘to  : ∀ x → fromData (toData x) ≡ just x
    from-inj : ∀ dx x → fromData dx ≡ just x → dx ≡ toData x
open IsData {{...}} public

from-injs : ∀ {A : Set} {{_ : IsData A}} ds xs
          → sequence (map (fromData {A}) ds) ≡ just xs → ds ≡ map (toData {A}) xs
from-injs {_} []       .[] refl = refl
from-injs {A} (d ∷ ds) xs₀ eq
  with fromData {A} d | inspect (fromData {A}) d
... | nothing | _ = case eq of λ()
... | just y  | ≡[ from≡ ]
  with sequence (map (fromData {A}) ds) | inspect sequence (map (fromData {A}) ds)
... | nothing  | _         = case eq of λ()
... | just xs′ | ≡[ seq≡ ]
  rewrite sym (M.just-injective eq)
        | from-injs ds xs′ seq≡
        | from-inj d y from≡
        = refl

instance
  IsDataˡ : ∀ {A : Set} → {{_ : IsData A}} → IsData (List A)
  toData   {{IsDataˡ}} = LIST ∘ map toData

  fromData {{IsDataˡ}} = λ{ (LIST xs) → sequence (map fromData xs) ; _ → nothing }

  from∘to  {{IsDataˡ}} []       = refl
  from∘to  {{IsDataˡ}} (x ∷ xs) rewrite from∘to x | from∘to xs = refl

  from-inj {{IsDataˡ {A}}} (LIST ds) ys p rewrite from-injs ds ys p = refl
  IsDataᶜ : IsData Char
  toData   {{IsDataᶜ}}           = I ∘ +_ ∘ Ch.toℕ

  fromData {{IsDataᶜ}} (I (+ z)) = just (Ch.fromℕ z)
  fromData {{IsDataᶜ}} _         = nothing

  from∘to  {{IsDataᶜ}} c rewrite fromℕ∘toℕ c = refl

  from-inj {{IsDataᶜ}} (I (+ z))      x from≡ = cong (I ∘ +_) (trans (sym (toℕ∘fromℕ z))
                                                              (cong Ch.toℕ (M.just-injective from≡)))

  IsDataˢ : IsData String
  toData   {{IsDataˢ}} = toData ∘ Str.toList

  fromData {{IsDataˢ}} = (Str.fromList <$>_) ∘ fromData

  from∘to  {{IsDataˢ}} xs rewrite from∘to (Str.toList xs) | fromList∘toList xs = refl

  from-inj {{IsDataˢ}} (LIST ds) xs p
    with sequence (map (fromData {Char}) ds) | inspect sequence (map (fromData {Char}) ds)
  ... | nothing  | _         = case p of λ()
  ... | just xs′ | ≡[ seq≡ ]
    with cong Str.toList (M.just-injective p)
  ... | p′
    rewrite from-injs ds xs′ seq≡
          | toList∘fromList xs′
          | p′
          = refl

--------------------------------------------------------------------------------------
-- Valid intervals (slot ranges).

data Bound : Set where
  -∞ +∞ : Bound
  t=_   : Time → Bound
unquoteDecl DecEq-Bound = DERIVE DecEq [ quote Bound , DecEq-Bound ]

data SlotRange : Set where
  _⋯_ : Bound → Bound → SlotRange
unquoteDecl DecEq-SlotRange = DERIVE DecEq [ quote SlotRange , DecEq-SlotRange ]

-- NB: Bounds are inclusive and refer to the length of the existing ledger, before submitting a new transaction.
_∋_ : SlotRange → ℕ → Bool
+∞   ⋯ _    ∋ _ = false
_    ⋯ -∞   ∋ _ = false
-∞   ⋯ +∞   ∋ _ = true
-∞   ⋯ t= r ∋ n = ⌊ n ≤? r ⌋
t= l ⋯ +∞   ∋ n = ⌊ l ≤? n ⌋
t= l ⋯ t= r ∋ n = ⌊ l ≤? n ⌋ ∧ ⌊ n ≤? r ⌋

infix 4 _∋_
infix 5 _⋯_
infix 6 t=_

--------------------------------------------------------------------------------------
-- Output references.

record TxOutputRef : Set where
  constructor _indexed-at_
  field
    id    : HashId -- hash of the referenced transaction
    index : ℕ      -- index into its outputs
unquoteDecl DecEqᵒʳ = DERIVE DecEq [ quote TxOutputRef , DecEqᵒʳ ]
open TxOutputRef public

--------------------------------------------------------------------------------------
-- Pending transactions (i.e. parts of the transaction being passed to a validator).

record InputInfo : Set where
  field
    outputRef     : TxOutputRef
    validatorHash : HashId
    datumHash     : HashId
    redeemerHash  : HashId
    value         : Value

record TxOutput : Set where
  field
    address   : Address -- ≡ hash of the input's validator
    value     : Value
    datumHash : HashId  -- ≡ hash of the input's datum
unquoteDecl DecEqᵒ = DERIVE DecEq [ quote TxOutput , DecEqᵒ ]
open TxOutput public

record TxInfo : Set where
  field
    inputInfo      : List InputInfo
    outputInfo     : List TxOutput
    forge          : Value
    policies       : List CurrencySymbol
    range          : SlotRange
    datumWitnesses : List (HashId × DATA)

record Pending (I : TxInfo → Set) : Set where
  field
    txInfo : TxInfo
    this   : I txInfo

open Pending public

PendingTx  = Pending (Index ∘ TxInfo.inputInfo)
PendingMPS = Pending (const HashId)

lookupDatum : HashId → List (HashId × DATA) → Maybe DATA
lookupDatum h = toMaybe ∘ map proj₂ ∘ filter ((h ≟_)∘ proj₁)

lookupDatumPtx : ∀ {I} → HashId → Pending I → Maybe DATA
lookupDatumPtx h = lookupDatum h ∘ TxInfo.datumWitnesses ∘ txInfo

thisValidator : PendingTx → HashId
thisValidator record {this = i; txInfo = record {inputInfo = is}} = InputInfo.validatorHash (is ‼ i)

valueSpent : TxInfo → Value
valueSpent = sumᶜ ∘ map InputInfo.value ∘ TxInfo.inputInfo

inputsAt : HashId → TxInfo → List InputInfo
inputsAt ℍ = filter ((ℍ ≟_) ∘ InputInfo.validatorHash) ∘ TxInfo.inputInfo

outputsAt : HashId → TxInfo → List TxOutput
outputsAt ℍ = filter ((ℍ ≟_) ∘ address) ∘ TxInfo.outputInfo

getContinuingOutputs : PendingTx → List TxOutput
getContinuingOutputs ptx = outputsAt (thisValidator ptx) (txInfo ptx)

valueAtⁱ : HashId → TxInfo → Value
valueAtⁱ ℍ = sumᶜ ∘ map InputInfo.value ∘ inputsAt ℍ

valueAtᵒ : HashId → TxInfo → Value
valueAtᵒ ℍ = sumᶜ ∘ map value ∘ outputsAt ℍ

propagates : Value → PendingTx → Bool
propagates v ptx@(record {txInfo = txi})
  = (valueAtⁱ ℍ txi ≥ᶜ v)
  ∧ (valueAtᵒ ℍ txi ≥ᶜ v)
  where ℍ = thisValidator ptx

outputsOf : ∀ {I} → (CurrencySymbol × TokenName) → Pending I → List TxOutput
outputsOf (c , t) = filter (◆∈?_ ∘ value) ∘ TxInfo.outputInfo ∘ txInfo
  where open FocusTokenClass (c , t)

--------------------------------------------------------------------------
-- Inputs, outputs and ledgers.

Validator : Set
Validator = PendingTx -- ^ parts of the currently validated transaction
          → DATA      -- ^ result value of the redeemer script
          → DATA      -- ^ result value of the data script
          → Bool

MonetaryPolicy : Set
MonetaryPolicy = PendingMPS → Bool

-- Values that hold the full monetary policies, rather than just their hashes.
ValueS = List (MonetaryPolicy × SubValue)

toValue : ValueS → Value
toValue = map (map₁ _♯)

record TxInput : Set where
  field
    outputRef : TxOutputRef
    validator : Validator
    redeemer  : DATA
    datum     : DATA
open TxInput public

record Tx : Set where
  field
    inputs         : List TxInput -- Set⟨ TxInput ⟩, but this is ensured by condition `noDoubleSpending`
    outputs        : List TxOutput
    forge          : Value
    policies       : List MonetaryPolicy
    range          : SlotRange
    datumWitnesses : List (HashId × DATA)
open Tx public

Ledger : Set
Ledger = List Tx

runValidation : PendingTx → TxInput → Bool
runValidation ptx i = validator i ptx (redeemer i) (datum i)

outputRefs : Tx → List TxOutputRef
outputRefs = map outputRef ∘ inputs

lookupDatumTx : HashId → Tx → Maybe DATA
lookupDatumTx h = lookupDatum h ∘ datumWitnesses
