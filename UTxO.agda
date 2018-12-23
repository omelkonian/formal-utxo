open import Level    using (0ℓ)
open import Function using (_∘_; _∋_; flip)

open import Data.Empty    using (⊥)
open import Data.Bool     using (T)
open import Data.Product  using (proj₁)
open import Data.Nat      using (ℕ; zero; suc; _+_; _<_; _≟_)
open import Data.Fin      using (Fin; toℕ; fromℕ≤)
open import Data.List     using (List; []; _∷_; _∷ʳ_; [_]; length; upTo; sum)
open import Data.List.Any using (Any)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Rel; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; setoid)

open import Category.Functor       using (RawFunctor)
open import Data.List.Categorical  renaming (functor to listFunctor)
open RawFunctor {0ℓ} listFunctor  using (_<$>_)

open import Utilities.Lists
open import Basic

module UTxO (addresses : List Address) where

open import Types addresses public

------------------------------------------------------------------------
-- Transactions.

record Tx : Set where

  field
    inputs  : Set⟨TxInput⟩
    outputs : List TxOutput
    forge   : Value
    fee     : Value

open Tx public

Ledger : Set
Ledger = List Tx

txInputs : Tx → List TxInput
txInputs = proj₁ ∘ inputs

module _ where
  open SETₒ

  unspentOutputsTx : Tx → Set⟨TxOutputRef⟩
  unspentOutputsTx tx = fromList (mkOutputRef <$> indices (outputs tx))
    where
      mkOutputRef : ℕ → TxOutputRef
      mkOutputRef index = record { id = tx ♯; index = index }

      indices : ∀ {A : Set} → List A → List ℕ
      indices xs = upTo (length xs)

  spentOutputsTx : Tx → Set⟨TxOutputRef⟩
  spentOutputsTx tx = fromList (outputRef <$> txInputs tx)

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

  open SETᵢ hiding (mapWith∈)
  open SETₒ using () renaming (_∈_ to _∈ₒ_)
  open import Data.List.Membership.Setoid (setoid TxInput) using (mapWith∈)

  record IsValidTx (tx : Tx) (l : Ledger) : Set₁ where

    field

      validTxRefs :
        ∀ i → i ∈ inputs tx →
          Any (λ tx → tx ♯ ≡ id (outputRef i)) l

      validOutputIndices :
        ∀ i → (i∈inputs : i ∈ inputs tx) →
          index (outputRef i) <
            length (outputs (lookupTx l (outputRef i) (validTxRefs i i∈inputs)))

      validOutputRefs :
        ∀ i → i ∈ inputs tx →
          outputRef i ∈ₒ unspentOutputs l

      preservesValues :
        forge tx + sum (mapWith∈ (txInputs tx) λ {i} i∈inputs →
                         lookupValue l i (validTxRefs i i∈inputs)
                                         (validOutputIndices i i∈inputs))
          ≡
        fee tx + Σ[ value ∈ outputs tx ]

      noDoubleSpending :
        ∣ inputs tx ∣ ≡ length (outputRef <$> txInputs tx)

      allInputsValidate : {R : Set} {_≈_ : Rel State 0ℓ} →
        ∀ i → i ∈ inputs tx →
          ∀ (stᵣ stᵥ : State) →
            stᵣ ≈ stᵥ →
              let redeemed  = ⟦ redeemer i ⟧ᵣ stᵣ
                  validated = ⟦ validator i ⟧ᵥ stᵥ (R ∋ redeemed)
              in  T validated

      validateValidHashes :
        ∀ i → (i∈inputs : i ∈ inputs tx) →
          toℕ (address (lookupOutput l (outputRef i)
                                     (validTxRefs i i∈inputs)
                                     (validOutputIndices i i∈inputs)))
            ≡
          (validator i) ♯

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
l ⊕ t ∶- _ = l ∷ʳ t
