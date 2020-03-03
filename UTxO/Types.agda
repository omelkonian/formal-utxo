------------------------------------------------------------------------
-- Basic UTxO types.
------------------------------------------------------------------------
module UTxO.Types where

open import Function using (_∘_; case_of_)

open import Data.Empty   using (⊥-elim)
open import Data.Bool    using (Bool; true; false; _∧_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List    using (List; map; length; []; _∷_; filter; foldr)
open import Data.Char    using (Char; toℕ; fromℕ)
open import Data.String  using (String; toList; fromList)
open import Data.Nat     using (ℕ; _≤?_)
  renaming (_≟_ to _≟ℕ_)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
  renaming (_≟_ to _≟ℤ_)
open import Data.Maybe   using (Maybe; nothing)
  renaming (map to mapₘ; just to pure; ap to _<*>_) -- for idiom brackets

open import Data.Maybe.Properties using (just-injective)

open import Relation.Nullary                      using (yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; inspect)
  renaming ([_] to ≡[_])

open import Prelude.General
open import Prelude.Lists
open import Prelude.Unsafe  using (fromℕ∘toℕ; toℕ∘fromℕ; fromList∘toList; toList∘fromList)

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

record IsData (A : Set) : Set where
  field
    toData   : A → DATA
    fromData : DATA → Maybe A
    from∘to  : ∀ x → fromData (toData x) ≡ pure x
    from-inj : ∀ dx x → fromData dx ≡ pure x → dx ≡ toData x
open IsData {{...}} public

from-injs : ∀ {A : Set} {{_ : IsData A}} ds xs
          → sequence (map (fromData {A}) ds) ≡ pure xs → ds ≡ map (toData {A}) xs
from-injs {_} []       .[] refl = refl
from-injs {A} (d ∷ ds) xs₀ eq
  with fromData {A} d | inspect (fromData {A}) d
... | nothing | _ = case eq of λ()
... | pure y  | ≡[ from≡ ]
  with sequence (map (fromData {A}) ds) | inspect sequence (map (fromData {A}) ds)
... | nothing  | _         = case eq of λ()
... | pure xs′ | ≡[ seq≡ ]
  rewrite sym (just-injective eq)
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
  toData   {{IsDataᶜ}}           = I ∘ +_ ∘ toℕ

  fromData {{IsDataᶜ}} (I (+ z)) = pure (fromℕ z)
  fromData {{IsDataᶜ}} _         = nothing

  from∘to  {{IsDataᶜ}} c rewrite fromℕ∘toℕ c = refl

  from-inj {{IsDataᶜ}} (I (+ z))      x from≡ = cong (I ∘ +_) (trans (sym (toℕ∘fromℕ z))
                                                              (cong toℕ (just-injective from≡)))

  IsDataˢ : IsData String
  toData   {{IsDataˢ}} = toData ∘ toList

  fromData {{IsDataˢ}} = mapₘ fromList ∘ fromData

  from∘to  {{IsDataˢ}} xs rewrite from∘to (toList xs) | fromList∘toList xs = refl

  from-inj {{IsDataˢ}} (LIST ds) xs p
    with sequence (map (fromData {Char}) ds) | inspect sequence (map (fromData {Char}) ds)
  ... | nothing  | _         = case p of λ()
  ... | pure xs′ | ≡[ seq≡ ]
    with cong toList (just-injective p)
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

data SlotRange : Set where
  _⋯_ : Bound → Bound → SlotRange

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

--------------------------------------------------------------------------------------
-- Pending transactions (i.e. parts of the transaction being passed to a validator).

-- not needed anymore?
record InputInfo : Set where
  field
    outputRef     : TxOutputRef
    validatorHash : HashId
    dataHash      : HashId
    redeemerHash  : HashId
    value         : Value

record OutputInfo : Set where
  field
    value         : Value
    validatorHash : HashId
    dataHash      : HashId

record TxInfo : Set where
  field
    inputInfo     : List InputInfo
    outputInfo    : List OutputInfo
    -- dataWitnesses : List (HashId × DATA)
    fee           : Value
    forge         : Value
    range         : SlotRange

record PendingTx : Set where
  field
    txInfo    : TxInfo
    thisInput : Index (TxInfo.inputInfo txInfo)

open PendingTx public

valueSpent : TxInfo → Value
valueSpent = sumᶜ ∘ map InputInfo.value ∘ TxInfo.inputInfo

getContinuingOutputs : PendingTx → List OutputInfo
getContinuingOutputs record { txInfo = record {inputInfo = is; outputInfo = outs}; thisInput = i }
  = filter ((_≟ℕ InputInfo.validatorHash (is ‼ i)) ∘ OutputInfo.validatorHash) outs

--------------------------------------------------------------------------
-- Inputs, outputs and ledgers.

open TxOutputRef public

Validator : Set
Validator = PendingTx -- ^ parts of the currently validated transaction
          → DATA      -- ^ result value of the redeemer script
          → DATA      -- ^ result value of the data script
          → Bool

record TxInput : Set where
  field
    outputRef : TxOutputRef
    validator : Validator
    redeemer  : DATA
    dataVal   : DATA

open TxInput public

record TxOutput : Set where
  field
    address  : Address -- ≡ hash of the input's validator
    value    : Value
    dataHash : HashId  -- ≡ hash of the input's data value

open TxOutput public

record Tx : Set where
  field
    inputs        : List TxInput -- Set⟨TxInput⟩, but this is ensured by condition `noDoubleSpending`
    outputs       : List TxOutput
    -- dataWitnesses : List (HashId × DATA)
    fee           : Value
    forge         : Value
    range         : SlotRange

open Tx public

Ledger : Set
Ledger = List Tx

runValidation : PendingTx → (i : TxInput) → Bool
runValidation ptx i = validator i ptx (redeemer i) (dataVal i)

outputRefs : Tx → List TxOutputRef
outputRefs = map outputRef ∘ inputs

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
Set⟨TxOutputRef⟩ = Set' where open SETₒ

-- Sets of DATA
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
Set⟨DATA⟩ = Set' where open SETᵈ

_==_ : DATA → DATA → Bool
x == y = ⌊ x ≟ᵈ y ⌋

-- Sets of slot ranges
_≟ᵇ_ : Decidable {A = Bound} _≡_
-∞ ≟ᵇ -∞     = yes refl
-∞ ≟ᵇ +∞     = no λ()
-∞ ≟ᵇ (t= _) = no λ()

+∞ ≟ᵇ -∞     = no λ()
+∞ ≟ᵇ +∞     = yes refl
+∞ ≟ᵇ (t= _) = no λ()

(t= _) ≟ᵇ -∞ = no λ()
(t= _) ≟ᵇ +∞ = no λ()
(t= n) ≟ᵇ (t= n′)
  with n ≟ℕ n′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl

_≟ˢ_ : Decidable {A = SlotRange} _≡_
(l ⋯ r) ≟ˢ (l′ ⋯ r′)
  with l ≟ᵇ l′ | r ≟ᵇ r′
... | no ¬p    | _        = no λ{ refl → ¬p refl }
... | _        | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl | yes refl = yes refl

-- Sets of inputs
_≟ᵢ_ : Decidable {A = TxInput} _≡_
i ≟ᵢ i′
  with outputRef i ≟ₒ outputRef i′ | ((validator i) ♯) ≟ℕ ((validator i′) ♯) | redeemer i ≟ᵈ redeemer i′ | dataVal i ≟ᵈ dataVal i′
... | no ¬p    | _     | _        | _ = no λ{ refl → ¬p refl }
... | _        | no ¬p | _        | _ = no λ{ refl → ¬p refl }
... | _        | _     | no ¬p    | _ = no λ{ refl → ¬p refl }
... | _        | _     | _        | no ¬p = no λ{ refl → ¬p refl }
... | yes refl | yes p | yes refl | yes refl
  with ♯-injective p
... | refl = yes refl

-- Sets of outputs
_≟ᵒ_ : Decidable {A = TxOutput} _≡_
o ≟ᵒ o′
  with address o ≟ℕ address o′ | value o ≟ᶜ value o′ | dataHash o ≟ℕ dataHash o′
... | no ¬p    | _        | _        = no λ{ refl → ¬p refl }
... | _        | no ¬p    | _        = no λ{ refl → ¬p refl }
... | _        | _        | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl | yes refl | yes refl = yes refl

module SETᵒ = SET {A = TxOutput} _≟ᵒ_
Set⟨TxOutput⟩ = Set' where open SETᵒ

-- Properties
≟-refl : ∀ {A : Set} (_≟_ : Decidable {A = A} _≡_) (x : A)
  → x ≟ x ≡ yes refl
≟-refl _≟_ x with x ≟ x
... | no ¬p    = ⊥-elim (¬p refl)
... | yes refl = refl
