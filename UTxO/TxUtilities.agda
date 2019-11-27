open import Function using (_∘_; _∋_; flip; _$_)

open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (⊤; tt)
open import Data.Bool     using (Bool; T)
open import Data.Product  using (_×_; _,_; proj₁; ∃; ∃-syntax; Σ; Σ-syntax)
open import Data.Nat      using (ℕ; zero; suc; _+_; _<_; _≟_)
open import Data.Fin      using (Fin; toℕ; fromℕ<)
open import Data.List     using ([]; _∷_; length; map)
open import Data.List.Any using (Any)
open import Data.List.Membership.Propositional using (_∈_; mapWith∈; find)
open import Data.Maybe using (nothing)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists using (indices; _‼_)

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Hashing.MetaHash using (_♯)
open import UTxO.Types

module UTxO.TxUtilities
  (Address : Set)
  (_♯ᵃ : Hash Address)
  (_≟ᵃ_ : Decidable {A = Address} _≡_)
  where

open import UTxO.Ledger     Address _♯ᵃ _≟ᵃ_
open import UTxO.Hashing.Tx Address _♯ᵃ _≟ᵃ_

module _ where
  open SETₒ

  unspentOutputsTx : Tx → Set⟨TxOutputRef⟩
  unspentOutputsTx tx = fromList (map ((tx ♯ᵗˣ) indexed-at_) (indices (outputs tx)))

  spentOutputsTx : Tx → Set⟨TxOutputRef⟩
  spentOutputsTx tx = fromList (map outputRef (inputs tx))

  unspentOutputs : Ledger → Set⟨TxOutputRef⟩
  unspentOutputs []         = ∅
  unspentOutputs (tx ∷ txs) = unspentOutputs txs ─ spentOutputsTx tx
                            ∪ unspentOutputsTx tx

lookupTx : (l : Ledger)
         → (out : TxOutputRef)
         → Any (λ tx → tx ♯ᵗˣ ≡ id out) l
         → Tx
lookupTx l out ∃tx≡id = proj₁ (find ∃tx≡id)

lookupOutput : (l : Ledger)
             → (out : TxOutputRef)
             → (∃tx≡id : Any (λ tx → tx ♯ᵗˣ ≡ id out) l)
             → index out < length (outputs (lookupTx l out ∃tx≡id))
             → TxOutput
lookupOutput l out ∃tx≡id index≤len =
  outputs (lookupTx l out ∃tx≡id) ‼ (fromℕ< {index out} index≤len)

lookupValue : (l : Ledger)
            → (input : TxInput)
            → (∃tx≡id : Any (λ tx → tx ♯ᵗˣ ≡ id (outputRef input)) l)
            → index (outputRef input) <
                length (outputs (lookupTx l (outputRef input) ∃tx≡id))
            → Quantity
lookupValue l input ∃tx≡id index≤len =
  value (lookupOutput l (outputRef input) ∃tx≡id index≤len)

--------------------------------------------------------------------------------------
-- Pending transactions (i.e. parts of the transaction being passed to a validator).

mkPendingTxOut : TxOutput → PendingTxOutput
mkPendingTxOut txOut =
  record
    { value         = value txOut
    ; validatorHash = (address txOut) ♯ᵃ
    ; dataHash      = dataHash txOut
    }

mkPendingTxIn : (l : Ledger)
              → (input : TxInput)
              → (∃tx≡id : Any (λ tx → tx ♯ᵗˣ ≡ id (outputRef input)) l)
              → index (outputRef input) < length (outputs (lookupTx l (outputRef input) ∃tx≡id))
              → PendingTxInput
mkPendingTxIn l txIn ∃tx index< =
  record
    { validatorHash = (validator txIn) ♯
    ; dataHash      = dataHash txOut
    ; redeemerHash  = (redeemer txIn) ♯ᵈ
    ; value         = value txOut
    }
    where
      txOut = lookupOutput l (outputRef txIn) ∃tx index<

mkPendingTx : (l : Ledger)
            → (tx : Tx)
            → (i : TxInput)
            → i ∈ inputs tx
            → (v₁ : ∀ i → i ∈ inputs tx → Any (λ t → t ♯ᵗˣ ≡ id (outputRef i)) l)
            → (∀ i → (i∈ : i ∈ inputs tx) →
                 index (outputRef i) < length (outputs (lookupTx l (outputRef i) (v₁ i i∈))))
            → PendingTx
mkPendingTx l tx i i∈ v₁ v₂ =
   record
     { inputInfo     = mapWith∈ (inputs tx) λ {i} i∈ → mkPendingTxIn l i (v₁ i i∈) (v₂ i i∈)
     ; thisInput     = mkPendingTxIn l i (v₁ i i∈) (v₂ i i∈)
     ; outputInfo    = map mkPendingTxOut (outputs tx)
     ; dataWitnesses = dataWitnesses tx
     --; txHash        = tx ♯ᵗˣ
     ; fee           = fee tx
     ; forge         = forge tx }
