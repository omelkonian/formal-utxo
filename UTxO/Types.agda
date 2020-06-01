------------------------------------------------------------------------
-- Basic UTxO types.
------------------------------------------------------------------------
module UTxO.Types where

open import Level          using (0ℓ)
open import Function       using (_∘_; case_of_; const)
open import Category.Monad using (RawMonad)

open import Data.Empty   using (⊥-elim)
open import Data.Bool    using (Bool; true; false; _∧_; T; not)
open import Data.Product using (_×_; _,_; proj₁; proj₂; map₁)
open import Data.List    using (List; map; length; []; _∷_; [_]; filter; foldr)
open import Data.Char    using (Char; toℕ; fromℕ)
open import Data.String  using (String; toList; fromList)
open import Data.Nat     using (ℕ; _≤?_)
  renaming (_≟_ to _≟ℕ_)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
  renaming (_≟_ to _≟ℤ_)
open import Data.Maybe   using (Maybe; just; nothing)

open import Data.Bool.Properties using (T?)
open import Data.Maybe.Properties using (just-injective)
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

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

Time Address Signature : Set
Time      = ℕ
Address   = HashId
Signature = HashId

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

  fromData {{IsDataᶜ}} (I (+ z)) = just (fromℕ z)
  fromData {{IsDataᶜ}} _         = nothing

  from∘to  {{IsDataᶜ}} c rewrite fromℕ∘toℕ c = refl

  from-inj {{IsDataᶜ}} (I (+ z))      x from≡ = cong (I ∘ +_) (trans (sym (toℕ∘fromℕ z))
                                                              (cong toℕ (just-injective from≡)))

  IsDataˢ : IsData String
  toData   {{IsDataˢ}} = toData ∘ toList

  fromData {{IsDataˢ}} = (fromList <$>_) ∘ fromData

  from∘to  {{IsDataˢ}} xs rewrite from∘to (toList xs) | fromList∘toList xs = refl

  from-inj {{IsDataˢ}} (LIST ds) xs p
    with sequence (map (fromData {Char}) ds) | inspect sequence (map (fromData {Char}) ds)
  ... | nothing  | _         = case p of λ()
  ... | just xs′ | ≡[ seq≡ ]
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

minˢ maxˢ : SlotRange → Bound
minˢ (b ⋯ _) = b
maxˢ (_ ⋯ b) = b

_≤ˢ_ : Bound → Bound → Bool
-∞     ≤ˢ _       = true
+∞     ≤ˢ +∞      = true
+∞     ≤ˢ _       = false
(t= _) ≤ˢ -∞      = false
(t= _) ≤ˢ +∞      = true
(t= n) ≤ˢ (t= n′) = ⌊ n ≤? n′ ⌋

-- NB: Bounds are inclusive and refer to the length of the existing ledger, before submitting a new transaction.
_∋_ _∌_ : SlotRange → ℕ → Bool
+∞   ⋯ _    ∋ _ = false
_    ⋯ -∞   ∋ _ = false
-∞   ⋯ +∞   ∋ _ = true
-∞   ⋯ t= r ∋ n = ⌊ n ≤? r ⌋
t= l ⋯ +∞   ∋ n = ⌊ l ≤? n ⌋
t= l ⋯ t= r ∋ n = ⌊ l ≤? n ⌋ ∧ ⌊ n ≤? r ⌋

sl ∌ n = not (sl ∋ n)

infix 4 _∋_ _∌_
infix 5 _⋯_
infix 6 t=_

--------------------------------------------------------------------------
-- Crypto.

postulate
  -- verify signature
  isSignedBy : ∀ {A : Set} → A → Signature → HashId → Bool

  -- m-of-n signature
  MultiSignature : Set
  checkMultiSig : MultiSignature → List Signature → Bool

--------------------------------------------------------------------------
-- Transactions, scripts and ledgers.

record TxOutputRef : Set where
  constructor _indexed-at_
  field
    id    : HashId -- hash of the referenced transaction
    index : ℕ      -- index into its outputs

open TxOutputRef public

data Clause : Set where
  JustMSig⟨_⟩         : MultiSignature → Clause
  SpendsOutput⟨_⟩     : TxOutputRef → Clause
  TickAfter⟨_⟩        : Bound → Clause
  SignedByPIDToken⟨_⟩ : HashId → Clause
  AssetToAddress⟨_⟩   : Maybe Address → Clause
  SpendsCur⟨_⟩        : Maybe HashId → Clause
  Forges⟨_⟩ {-Burns⟨_⟩-}  : SubValue → Clause
  FreshTokens DoForge : Clause

data Script : Set where
  _&&_ _||_ : Script → Script → Script
  `_        : Clause → Script

record TxOutput : Set where
  field
    address   : Address -- ≡ hash of the input's validator
    value     : Value
open TxOutput public

record TxInput : Set where
  field
    outputRef : TxOutputRef
    validator : Script

open TxInput public

record Tx : Set where
  field
    inputs         : List TxInput -- Set⟨TxInput⟩, but this is ensured by condition `Validity.noDoubleSpending`
    outputs        : List TxOutput
    forge          : Value
    policies       : List Script
    range          : SlotRange
    sigs           : List Signature

open Tx public

checkMultiSigTx : MultiSignature → Tx → Bool
checkMultiSigTx msig tx = checkMultiSig msig (sigs tx)

Ledger : Set
Ledger = List Tx

outputRefs : Tx → List TxOutputRef
outputRefs = map outputRef ∘ inputs

------------------------------------------------------------------------
-- Set modules/types.

import Prelude.Set' as SET

-- Sets of natural numbers.
module SETℕ = SET {A = ℕ} _≟ℕ_
Set⟨ℕ⟩ = Set' where open SETℕ

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

-- Sets of output references
_≟ₒ_ : Decidable {A = TxOutputRef} _≡_
x ≟ₒ y with id x ≟ℕ id y | index x ≟ℕ index y
... | no ¬p    | _        = no λ{refl → ¬p refl}
... | _        | no ¬p′   = no λ{refl → ¬p′ refl}
... | yes refl | yes refl = yes refl

module SETₒ = SET {A = TxOutputRef} _≟ₒ_
Set⟨TxOutputRef⟩ = Set' where open SETₒ

-- Sets of inputs
_≟ⁱ_ : Decidable {A = TxInput} _≡_
i ≟ⁱ i′
  with outputRef i ≟ₒ outputRef i′ | ((validator i) ♯) ≟ℕ ((validator i′) ♯)
... | no ¬p    | _     = no λ{ refl → ¬p refl }
... | _        | no ¬p = no λ{ refl → ¬p refl }
... | yes refl | yes p
  with ♯-injective p
... | refl = yes refl

module SETⁱ = SET {A = TxInput} _≟ⁱ_
Set⟨TxInput⟩ = Set' where open SETⁱ

-- Sets of outputs
_≟ᵒ_ : Decidable {A = TxOutput} _≡_
o ≟ᵒ o′
  with address o ≟ℕ address o′ | value o ≟ᶜ value o′
... | no ¬p    | _        = no λ{ refl → ¬p refl }
... | _        | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl | yes refl = yes refl

module SETᵒ = SET {A = TxOutput} _≟ᵒ_
Set⟨TxOutput⟩ = Set' where open SETᵒ
