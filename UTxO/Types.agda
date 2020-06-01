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

open import UTxO.Crypto
open import UTxO.Value

------------------------------------------------------------------------
-- Basic types.

Time Address : Set
Time      = ℕ
Address   = HashId

-----------------------------------------
-- First-order data values.

data DATA : Set where
 I      : ℤ → DATA
 H      : HashId → DATA
 LIST   : List DATA → DATA
 CONSTR : ℕ → List DATA → DATA
 MAP    : List (DATA × DATA) → DATA

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
-- Transactions, scripts and ledgers.

record TxOutputRef : Set where
  constructor _indexed-at_
  field
    id    : HashId -- hash of the referenced transaction
    index : ℕ      -- index into its outputs

open TxOutputRef public

infixr 6 _&&_
infixr 5 _||_
data Script : Set where
  _&&_ _||_ : Script → Script → Script
  Not       : Script → Script

  JustMSig⟨_⟩         : MultiSignature → Script
  SpendsOutput⟨_⟩     : TxOutputRef → Script
  TickAfter⟨_⟩        : Bound → Script
  SignedByPIDToken⟨_⟩ : Maybe HashId → Script
  AssetToAddress⟨_⟩   : Maybe Address → Script
  SpendsCur⟨_⟩        : Maybe HashId → Script
  Forges⟨_⟩ Burns⟨_⟩  : SubValue → Script
  FreshTokens DoForge : Script

pattern SignedByPIDToken⟨⟩ = SignedByPIDToken⟨ nothing ⟩
pattern AssetToAddress⟨⟩   = AssetToAddress⟨ nothing ⟩
pattern SpendsCur⟨⟩        = SpendsCur⟨ nothing ⟩

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
