------------------------------------------------------------------------
-- Basic UTxO types.
------------------------------------------------------------------------

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import UTxO.Hashing.Base

module UTxO.Types
  (Address : Set)
  (_♯ₐ : Hash Address)
  (_≟ₐ_ : Decidable {A = Address} _≡_)
  where

open import Function             using (_∘_; case_of_)

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
open import Prelude.Unsafe  using (fromℕ∘toℕ; toℕ∘fromℕ; fromList∘toList; toList∘fromList)

open import UTxO.Hashing.Base
open import UTxO.Hashing.MetaHash

-- Re-export multi-currency values.
open import UTxO.Value Address _♯ₐ _≟ₐ_ --public
--  using (Quantities; Value; $0; $; _+ᶜ_; sumᶜ; _≟ᶜ_; _≥ᶜ_)

------------------------------------------------------------------------
-- Basic types.

HashId : Set
HashId = ℕ

Time : Set
Time = ℕ

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
-- Pending transactions (i.e. parts of the transaction being passed to a validator).

-- not needed anymore?
record PendingTxInput : Set where
  field
    -- outputRef     : OutputRef -- present in spec
    validatorHash : HashId
    dataHash      : HashId
    redeemerHash  : HashId
    value         : Quantities

record PendingTxOutput : Set where
  field
    value         : Quantities
    validatorHash : HashId
    dataHash      : HashId

record PendingTx : Set where
  field
    inputInfo     : List PendingTxInput
    thisInput     : ℕ
    outputInfo    : List PendingTxOutput
    range         : SlotRange
    dataWitnesses : List (HashId × DATA)
    txHash        : HashId -- not present in spec
    fee           : Quantities
    forge         : Quantities

findData : HashId → PendingTx → Maybe DATA
findData dsh (record {dataWitnesses = ws}) = toMaybe (map proj₂ (filter ((_≟ℕ dsh) ∘ proj₁) ws))

{-
getContinuingOutputs : PendingTx → List PendingTxOutput
getContinuingOutputs record { thisInput = record { validatorHash = in♯ } ; outputInfo = outs }
  = filter ((_≟ℕ in♯) ∘ PendingTxOutput.validatorHash) outs

ownHashes : PendingTx → (HashId × HashId × HashId)
ownHashes record {thisInput = record {validatorHash = h₁; redeemerHash = h₂; dataHash = h₃}} = h₁ , h₂ , h₃

ownHash : PendingTx → HashId
ownHash = proj₁ ∘ ownHashes
-}
{-
valueSpent : PendingTx → Value
valueSpent = sumᶜ ∘ map PendingTxInput.value ∘ PendingTx.inputInfo

thisValueSpent : PendingTx → Value
thisValueSpent = PendingTxInput.value ∘ PendingTx.thisInput
-}
outputsAt : HashId → PendingTx → List PendingTxOutput
outputsAt h = filter ((_≟ℕ h) ∘ PendingTxOutput.validatorHash) ∘ PendingTx.outputInfo
{-
valueLockedBy : PendingTx → HashId → Value
valueLockedBy ptx h = sumᶜ (map PendingTxOutput.value (outputsAt h ptx))
-}
--------------------------------------------------------------------------
-- Output references and inputs.

record TxOutputRef : Set where
  constructor _indexed-at_
  field
    id    : HashId
    index : ℕ

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

-- Properties
≟-refl : ∀ {A : Set} (_≟_ : Decidable {A = A} _≡_) (x : A)
  → x ≟ x ≡ yes refl
≟-refl _≟_ x with x ≟ x
... | no ¬p    = ⊥-elim (¬p refl)
... | yes refl = refl
