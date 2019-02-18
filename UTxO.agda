open import Level    using (0ℓ)
open import Function using (_∘_; _∋_; flip)

open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (⊤; tt)
open import Data.Bool     using (Bool; T)
open import Data.Product  using (proj₁)
open import Data.Nat      using (ℕ; zero; suc; _+_; _<_; _≟_)
open import Data.Fin      using (Fin; toℕ; fromℕ≤)
open import Data.List     using (List; []; _∷_; _∷ʳ_; [_]; length; sum; map)
open import Data.List.Any using (Any)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Rel; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; setoid)

open import Category.Functor       using (RawFunctor)
open import Data.List.Categorical  renaming (functor to listFunctor)

open import Utilities.Lists
open import Types

module UTxO (addresses : List Address) where

------------------------------------------------------------------------
-- Transactions.

record TxOutput : Set₁ where
  field
    value   : Value
    address : Index addresses

    Data       : Set
    dataScript : State → Data

open TxOutput public

runValidation : (i : TxInput) → (o : TxOutput) → D i ≡ Data o → State → Bool
runValidation i o refl st = validator i st (value o) (redeemer i st) (dataScript o st)

record Tx : Set₁ where

  field
    inputs  : List TxInput -- T0D0: Set⟨TxInput⟩
    outputs : List TxOutput
    forge   : Value
    fee     : Value

open Tx public

Ledger : Set₁
Ledger = List Tx

module _ where
  open SETₒ

  unspentOutputsTx : Tx → Set⟨TxOutputRef⟩
  unspentOutputsTx tx = fromList (map ((tx ♯) indexed-at_) (indices (outputs tx)))

  spentOutputsTx : Tx → Set⟨TxOutputRef⟩
  spentOutputsTx tx = fromList (map outputRef (inputs tx))

  unspentOutputs : Ledger → Set⟨TxOutputRef⟩
  unspentOutputs []         = ∅
  unspentOutputs (tx ∷ txs) = unspentOutputs txs ─ spentOutputsTx tx
                            ∪ unspentOutputsTx tx

------------------------------------------------------------------------
-- Tx utilities.

open import Data.List.Membership.Setoid (setoid Tx) using (find)

lookupTx : (l : Ledger)
         → (out : TxOutputRef)
         → Any (λ tx → tx ♯ ≡ id out) l
         → Tx
lookupTx l out ∃tx≡id = proj₁ (find ∃tx≡id)

lookupOutput : (l : Ledger)
             → (out : TxOutputRef)
             → (∃tx≡id : Any (λ tx → tx ♯ ≡ id out) l)
             → index out < length (outputs (lookupTx l out ∃tx≡id))
             → TxOutput
lookupOutput l out ∃tx≡id index≤len =
  outputs (lookupTx l out ∃tx≡id) ‼ (fromℕ≤ {index out} index≤len)

lookupValue : (l : Ledger)
            → (input : TxInput)
            → (∃tx≡id : Any (λ tx → tx ♯ ≡ id (outputRef input)) l)
            → index (outputRef input) <
                length (outputs (lookupTx l (outputRef input) ∃tx≡id))
            → Value
lookupValue l input ∃tx≡id index≤len =
  value (lookupOutput l (outputRef input) ∃tx≡id index≤len)

------------------------------------------------------------------------
-- Properties.

module _ where

  open import Data.List.Membership.Setoid (setoid TxInput) using (_∈_; mapWith∈)

  record IsValidTx (tx : Tx) (l : Ledger) : Set₁ where

    field

      validTxRefs :
        ∀ i → i ∈ inputs tx →
          Any (λ t → t ♯ ≡ id (outputRef i)) l

      validOutputIndices :
        ∀ i → (i∈ : i ∈ inputs tx) →
          index (outputRef i) <
            length (outputs (lookupTx l (outputRef i) (validTxRefs i i∈)))

      validOutputRefs :
        ∀ i → i ∈ inputs tx →
          outputRef i SETₒ.∈′ unspentOutputs l

      validDataScriptTypes :
        ∀ i → (i∈ : i ∈ inputs tx) →
          D i ≡ Data (lookupOutput l (outputRef i) (validTxRefs i i∈) (validOutputIndices i i∈))

      -------------------------------------------------------------------------------

      preservesValues :
        forge tx + sum (mapWith∈ (inputs tx) λ {i} i∈ →
                         lookupValue l i (validTxRefs i i∈) (validOutputIndices i i∈))
          ≡
        fee tx + Σ[ value ∈ outputs tx ]

      noDoubleSpending :
        SETₒ.noDuplicates (map outputRef (inputs tx))

      allInputsValidate : -- {_≈_ : Rel State 0ℓ} →
        ∀ i → (i∈ : i ∈ inputs tx) →
          let
            out : TxOutput
            out = lookupOutput l (outputRef i) (validTxRefs i i∈) (validOutputIndices i i∈)
          in
            ∀ (st : State) →
              T (runValidation i out (validDataScriptTypes i i∈) st)

      validateValidHashes :
        ∀ i → (i∈ : i ∈ inputs tx) →
          let
            out : TxOutput
            out = lookupOutput l (outputRef i) (validTxRefs i i∈) (validOutputIndices i i∈)
          in
            toℕ (address out) ≡ (validator i) ♯

  open IsValidTx public

-- List notation for constructing valid ledgers.
∙_∶-_ : (t : Tx)
      → .(IsValidTx t [])
      → Ledger
∙ t ∶- _ = [ t ]

infixl 5 _⊕_∶-_
_⊕_∶-_ : (l : Ledger)
       → (t : Tx)
       → .(IsValidTx t l)
       → Ledger
l ⊕ t ∶- _ = t ∷ l


-- Decidable procedure for IsValidTx.
{-

open import Data.List.All using (all)
open import Data.List.Any using (any)

isValidTx? : ∀ (tx : Tx) (l : Ledger) → Set
isValidTx? tx l
  with all (λ i → any (λ t → t ♯  ≟ id (outputRef i)) l)
           (inputs tx)
... | no _ = ⊥
... | yes v₁
  with all (λ i → {!!}) (inputs tx)
... | no _ = ⊥
... | yes v₂
  with all (λ i → outputRef i SETₒ.∈? SETₒ.list (unspentOutputs l)) (inputs tx)
... | no _ = ⊥
... | yes v₃
  with ?
... | no _ = ⊥
... | yes v₄
  with ???
... | no _ = ⊥
... | yes v₅
  with all (λ i → impossible?) (inputs tx)
... | no _ = ⊥
... | yes v₆
  with ???
... | no _ = ⊥
... | yes v₇ = ⊤


-- sound-isValidTx : ∀ {l t} {p : isValidTx? t l} → IsValidTx t l
-}
