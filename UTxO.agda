module UTxO where

open import Level    using (0ℓ)
open import Function using (_∘_; _∋_; flip)

open import Data.Empty   using (⊥)
open import Data.Bool    using (T)
open import Data.Product using (proj₁)
open import Data.Nat     using (ℕ; zero; suc; _+_; _<_; _≟_)
open import Data.List    using (List; []; _∷_; length; upTo)
open import Data.Maybe   using (Maybe; just; nothing; fromMaybe; is-just)
  renaming (map to mapMaybe)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Category.Functor       using (RawFunctor)
open import Data.Maybe.Categorical renaming (functor to maybeFunctor)
open import Data.List.Categorical  renaming (functor to listFunctor)
open RawFunctor {0ℓ} maybeFunctor renaming (_<$>_ to _<$>ₘ_)
open RawFunctor {0ℓ} listFunctor  renaming (_<$>_ to _<$>ₗ_)

open import Utilities.Lists using (Σ-sum-syntax)
open import Types

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
  unspentOutputsTx tx = fromList (mkOutputRef <$>ₗ indices (outputs tx))
    where
      mkOutputRef : ℕ → TxOutputRef
      mkOutputRef index = record { id = tx ♯; index = index }

      indices : ∀ {A : Set} → List A → List ℕ
      indices xs = upTo (length xs)

  spentOutputsTx : Tx → Set⟨TxOutputRef⟩
  spentOutputsTx tx = fromList (outputRef <$>ₗ txInputs tx)

  unspentOutputs : Ledger → Set⟨TxOutputRef⟩
  unspentOutputs []         = ∅
  unspentOutputs (tx ∷ txs) = unspentOutputs txs ─ spentOutputsTx tx
                            ∪ unspentOutputsTx tx

------------------------------------------------------------------------
-- Tx utilities.

lookupTx : Ledger → TxOutputRef → Maybe Tx
lookupTx (t ∷ ts) out with t ♯ ≟ id out
... | yes _ = just t
... | no  _ = lookupTx ts out
lookupTx [] _ = nothing

lookupOutput : Ledger → TxOutputRef → Maybe TxOutput
lookupOutput l out with outputs <$>ₘ (lookupTx l out)
... | nothing = nothing
... | just xs = lookupOutputTx (index out) xs
  where
    lookupOutputTx : ℕ → List TxOutput → Maybe TxOutput
    lookupOutputTx zero    (o ∷ os) = just o
    lookupOutputTx (suc i) (_ ∷ os) = lookupOutputTx i os
    lookupOutputTx _       []       = nothing

lookupValue : Ledger → TxInput → Maybe Value
lookupValue l input = mapMaybe value (lookupOutput l (outputRef input))

------------------------------------------------------------------------
-- Properties.

module _ where

  open SETᵢ
  open SETₒ using () renaming (_∈_ to _∈ₒ_)

  record IsValidTx (tx : Tx) (l : Ledger) : Set₁ where

    field

      lookupValueSucceeds :
        ∀[ i ∈ inputs tx ]
          T (is-just (lookupValue l i))

      lookupOutputSucceeds :
        ∀[ i ∈ inputs tx ]
          T (is-just (lookupOutput l (outputRef i)))

      hasValidReferences  :
        ∀[ i ∈ inputs tx ]
          outputRef i ∈ₒ unspentOutputs l

      preservesValues     :
        forge tx + Σ[ fromMaybe 0 ∘ lookupValue l ∈ txInputs tx ]
          ≡
        fee tx + Σ[ value ∈ outputs tx ]

      noDoubleSpending    :
        ∣ inputs tx ∣ ≡ length (outputRef <$>ₗ txInputs tx)

      allInputsValidate   : {R : Set} {_≈_ : Rel State 0ℓ} →
        ∀[ i ∈ inputs tx ]
          ∀ (stᵣ stᵥ : State) →
            stᵣ ≈ stᵥ →
              let redeemed  = ⟦ redeemer i ⟧ᵣ stᵣ
                  validated = ⟦ validator i ⟧ᵥ stᵥ (R ∋ redeemed)
              in  T validated

      validateValidHashes :
        ∀[ i ∈ inputs tx ]
          (address <$>ₘ (lookupOutput l (outputRef i)))
            ≡
          just ((validator i) ♯)
