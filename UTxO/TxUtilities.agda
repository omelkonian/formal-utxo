open import Function using (_∘_; _∋_; flip; _$_)

open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (⊤; tt)
open import Data.Bool     using (Bool; T)
open import Data.Product  using (_×_; _,_; proj₁; ∃; ∃-syntax; Σ; Σ-syntax)
open import Data.Nat      using (ℕ; zero; suc; _+_; _<_; _≟_)
open import Data.Fin      using (Fin; toℕ; fromℕ≤)
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
  (_♯ₐ : Hash Address)
  (_≟ₐ_ : Decidable {A = Address} _≡_)
  where

open import UTxO.Ledger     Address _♯ₐ _≟ₐ_
open import UTxO.Hashing.Tx Address _♯ₐ _≟ₐ_

module _ where
  open SETₒ

  unspentOutputsTx : Tx → Set⟨TxOutputRef⟩
  unspentOutputsTx tx = fromList (map ((tx ♯ₜₓ) indexed-at_) (indices (outputs tx)))

  spentOutputsTx : Tx → Set⟨TxOutputRef⟩
  spentOutputsTx tx = fromList (map outputRef (inputs tx))

  unspentOutputs : Ledger → Set⟨TxOutputRef⟩
  unspentOutputs []         = ∅
  unspentOutputs (tx ∷ txs) = unspentOutputs txs ─ spentOutputsTx tx
                            ∪ unspentOutputsTx tx

lookupTx : (l : Ledger)
         → (out : TxOutputRef)
         → Any (λ tx → tx ♯ₜₓ ≡ id out) l
         → Tx
lookupTx l out ∃tx≡id = proj₁ (find ∃tx≡id)

lookupOutput : (l : Ledger)
             → (out : TxOutputRef)
             → (∃tx≡id : Any (λ tx → tx ♯ₜₓ ≡ id out) l)
             → index out < length (outputs (lookupTx l out ∃tx≡id))
             → TxOutput
lookupOutput l out ∃tx≡id index≤len =
  outputs (lookupTx l out ∃tx≡id) ‼ (fromℕ≤ {index out} index≤len)

lookupValue : (l : Ledger)
            → (input : TxInput)
            → (∃tx≡id : Any (λ tx → tx ♯ₜₓ ≡ id (outputRef input)) l)
            → index (outputRef input) <
                length (outputs (lookupTx l (outputRef input) ∃tx≡id))
            → Value
lookupValue l input ∃tx≡id index≤len =
  value (lookupOutput l (outputRef input) ∃tx≡id index≤len)

--------------------------------------------------------------------------------------
-- Pending transactions (i.e. parts of the transaction being passed to a validator).

mkPendingTxOut : TxOutput → PendingTxOutput
mkPendingTxOut txOut =
  record
    { value         = value txOut
    ; validatorHash = (address txOut) ♯ₐ
    ; dataHash      = (dataVal txOut) ♯ᵈ
    }

mkPendingTxIn : (l : Ledger)
              → (input : TxInput)
              → (∃tx≡id : Any (λ tx → tx ♯ₜₓ ≡ id (outputRef input)) l)
              → index (outputRef input) < length (outputs (lookupTx l (outputRef input) ∃tx≡id))
              → PendingTxInput
mkPendingTxIn l txIn ∃tx index< =
  record
    { validatorHash = (validator txIn) ♯
    ; dataHash      = (dataVal txOut) ♯ᵈ
    ; redeemerHash  = (redeemer txIn) ♯ᵈ
    ; value         = value txOut
    }
    where
      txOut = lookupOutput l (outputRef txIn) ∃tx index<

mkPendingTx : (l : Ledger)
            → (tx : Tx)
            → (i : TxInput)
            → i ∈ inputs tx
            → (v₁ : ∀ i → i ∈ inputs tx → Any (λ t → t ♯ₜₓ ≡ id (outputRef i)) l)
            → (∀ i → (i∈ : i ∈ inputs tx) →
                 index (outputRef i) < length (outputs (lookupTx l (outputRef i) (v₁ i i∈))))
            → PendingTx
mkPendingTx l tx i i∈ v₁ v₂ =
   record
     { inputInfo     = mapWith∈ (inputs tx) λ {i} i∈ → mkPendingTxIn l i (v₁ i i∈) (v₂ i i∈)
     ; thisInput     = mkPendingTxIn l i (v₁ i i∈) (v₂ i i∈)
     ; outputInfo    = map mkPendingTxOut (outputs tx)
     ; dataWitnesses = map (λ o → ((dataVal o) ♯ᵈ) , dataVal o) (outputs tx)
     ; txHash        = tx ♯ₜₓ
     ; fee           = fee tx
     ; forge         = forge tx }
