module UTxO where

open import Function using (_∋_)
open import Data.Bool using (T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≟_)

open import Data.List using (List; []; _∷_; length; upTo)

open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Data.AVL.Sets as Sets

open import Utilities.Lists using (_<$>_; sumValues)
open import Utilities.Sets
open import STO-Modules using ( module STO⟦TxInput⟧; module STO⟦TxOutputRef⟧
                              ; Set⟨TxInput⟩; Set⟨TxOutputRef⟩ )
open import Types

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
txInputs tx = toList (inputs tx)
  where open STO⟦TxInput⟧

module _ where
  open STO⟦TxOutputRef⟧

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
-- Tx utilities

lookupTx : Ledger → TxOutputRef → Tx
lookupTx (t ∷ ts) out with t ♯ ≟ id out
... | yes _ = t
... | no  _ = lookupTx ts out
lookupTx [] _ = ⊥-elim impossible
  where postulate impossible : ⊥

lookupOutput : Ledger → TxOutputRef → TxOutput
lookupOutput l out = lookupOutputTx (outputs (lookupTx l out)) (index out)
  where
    lookupOutputTx : List TxOutput → ℕ → TxOutput
    lookupOutputTx (o ∷ os) zero    = o
    lookupOutputTx (_ ∷ os) (suc i) = lookupOutputTx os i
    lookupOutputTx []       _       = ⊥-elim impossible
      where postulate impossible : ⊥

lookupValue : Ledger → TxInput → Value
lookupValue l input = value (lookupOutput l (outputRef input))

------------------------------------------------------------------------
-- Properties

record IsValidTx (tx : Tx) (l : Ledger) : Set₁ where
  field
    hasValidReferences  :
      ∀[ i ∈ inputs tx ]
        outputRef i ∈ unspentOutputs l

    preservesValues     :
      forge tx + Σ[ lookupValue l ∈ txInputs tx ]
        ≡
      fee tx + Σ[ value ∈ outputs tx ]

    noDoubleSpending    :
      ∣ inputs tx ∣ ≡ length (outputRef <$> txInputs tx)

    allInputsValidate   : {R : Set} →
      ∀[ i ∈ inputs tx ]
        ∀ (st : State) →
          let redeemed  = ⟦ redeemer i ⟧ᵣ st
              validated = ⟦ validator i ⟧ᵥ st (R ∋ redeemed)
          in  T validated

    validateValidHashes :
      ∀[ i ∈ inputs tx ]
        (validator i) ♯ ≡ address (lookupOutput l (outputRef i))

