open import Level    using (0ℓ)
open import Function using (_∘_; _∋_; flip; _$_)

open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (⊤; tt)
open import Data.Bool     using (Bool; T)
open import Data.Product  using (_×_; proj₁; ∃; ∃-syntax; Σ; Σ-syntax)
open import Data.Nat      using (ℕ; zero; suc; _+_; _<_; _≟_)
open import Data.Fin      using (Fin; toℕ; fromℕ≤)
open import Data.List     using (List; []; _∷_; _∷ʳ_; [_]; length; sum; map)
open import Data.List.Any using (Any)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Rel; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; setoid)

open import Category.Functor       using (RawFunctor)
open import Data.List.Categorical  renaming (functor to listFunctor)
open import Data.List.Membership.Propositional using (_∈_; mapWith∈)

open import Utilities.Lists
open import Data.TYPE using (𝕌; el; _≟ᵤ_)
open import Types

module UTxO (addresses : List Address) where

------------------------------------------------------------------------
-- Transactions.

record TxOutput : Set where
  field
    value   : Value
    address : Index addresses

    Data       : 𝕌
    dataScript : State → el Data

open TxOutput public

runValidation : PendingTx → (i : TxInput) → (o : TxOutput) → D i ≡ Data o → State → Bool
runValidation ptx i o refl st =
  validator i st (value o) ptx (redeemer i st) (dataScript o st)

record Tx : Set where
  field
    inputs  : List TxInput -- T0D0: Set⟨TxInput⟩
    outputs : List TxOutput
    forge   : Value
    fee     : Value

open Tx public

--------------------------------------------------------------------------------------
-- Ledgers and unspent outputs.

Ledger : Set
Ledger = List Tx

module _ where
  open SETₒ renaming (fromList to fromListₒ)

  unspentOutputsTx : Tx → Set⟨TxOutputRef⟩
  unspentOutputsTx tx = fromListₒ (map ((tx ♯) indexed-at_) (indices (outputs tx)))

  spentOutputsTx : Tx → Set⟨TxOutputRef⟩
  spentOutputsTx tx = fromListₒ (map outputRef (inputs tx))

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

--------------------------------------------------------------------------------------
-- Pending transactions (i.e. parts of the transaction being passed to a validator).

mkPendingTxOut : TxOutput → PendingTxOutput
mkPendingTxOut txOut = record
                         { value         = value txOut
                         ; dataHash      = (dataScript txOut) ♯
                         }

mkPendingTxIn : (l : Ledger)
              → (input : TxInput)
              → (∃tx≡id : Any (λ tx → tx ♯ ≡ id (outputRef input)) l)
              → index (outputRef input) < length (outputs (lookupTx l (outputRef input) ∃tx≡id))
              → PendingTxInput
mkPendingTxIn l txIn ∃tx index< = record
                       { value         = lookupValue l txIn ∃tx index<
                       ; validatorHash = (validator txIn) ♯
                       ; redeemerHash  = (redeemer txIn) ♯
                       }

mkPendingTx : (l : Ledger)
            → (tx : Tx)
            → (v₁ : ∀ i → i ∈ inputs tx → Any (λ t → t ♯ ≡ id (outputRef i)) l)
            → (∀ i → (i∈ : i ∈ inputs tx) →
                 index (outputRef i) < length (outputs (lookupTx l (outputRef i) (v₁ i i∈))))
            → PendingTx
mkPendingTx l tx v₁ v₂ =
  record { txHash  = tx ♯
         ; inputs  = mapWith∈ (inputs tx) λ {i} i∈ → mkPendingTxIn l i (v₁ i i∈) (v₂ i i∈)
         ; outputs = map mkPendingTxOut (outputs tx)
         ; forge   = forge tx
         ; fee     = fee tx
         }

------------------------------------------------------------------------
-- Properties.

record IsValidTx (tx : Tx) (l : Ledger) : Set where

  field

    validTxRefs :
      ∀ i → i ∈ inputs tx →
        Any (λ t → t ♯ ≡ id (outputRef i)) l

    validOutputIndices :
      ∀ i → (i∈ : i ∈ inputs tx) →
          index (outputRef i) < length (outputs (lookupTx l (outputRef i) (validTxRefs i i∈)))

    validOutputRefs :
      ∀ i → i ∈ inputs tx →
        outputRef i SETₒ.∈′ unspentOutputs l

    validDataScriptTypes :
      ∀ i → (i∈ : i ∈ inputs tx) →
        D i ≡ Data (lookupOutput l (outputRef i) (validTxRefs i i∈) (validOutputIndices i i∈))

    -----------------------------------------------------------------------------------------

    preservesValues :
      forge tx +ᶜ sumᶜ (mapWith∈ (inputs tx) λ {i} i∈ →
                          lookupValue l i (validTxRefs i i∈) (validOutputIndices i i∈))
        ≡
      fee tx +ᶜ sumᶜ (map value (outputs tx))

    noDoubleSpending :
      SETₒ.noDuplicates (map outputRef (inputs tx))

    allInputsValidate :
      ∀ i → (i∈ : i ∈ inputs tx) →
        let
          out = lookupOutput l (outputRef i) (validTxRefs i i∈) (validOutputIndices i i∈)
          ptx = mkPendingTx l tx validTxRefs validOutputIndices
        in
          ∀ (st : State) →
            T (runValidation ptx i out (validDataScriptTypes i i∈) st)

    validateValidHashes :
      ∀ i → (i∈ : i ∈ inputs tx) →
        let
          out = lookupOutput l (outputRef i) (validTxRefs i i∈) (validOutputIndices i i∈)
        in
          toℕ (address out) ≡ (validator i) ♯

    -- enforce monetary policies
    forging :
      ∀ c → c ∈ values (forge tx) →
        ∃[ i ] ( (i ∈ inputs tx)
               × (id (outputRef i) ≡ c)
               )


open IsValidTx public

-- List notation for constructing valid ledgers.
data ValidLedger : Ledger → Set where

  ∙_∶-_ : (t : Tx)
       → .(IsValidTx t [])
       → ValidLedger [ t ]

  _⊕_∶-_ : ∀ {l}
         → ValidLedger l
         → (t : Tx)
         → .(IsValidTx t l)
         → ValidLedger (t ∷ l)

infixl 5 _⊕_∶-_
