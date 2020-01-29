open import Function using (_∘_)

open import Data.Bool     using (T)
open import Data.Product  using (∃-syntax)
open import Data.Nat      using (_<_)
  renaming (_≟_ to _≟ℕ_)
open import Data.List     using ([]; _∷_; length; map; filter)

open import Data.Maybe renaming (map to _<$>_)
open import Data.List.Membership.Propositional            using (_∈_; mapWith∈)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.Any                  using (Any)

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Hashing.MetaHash using (_♯)

module UTxO.Validity
  (Address : Set)
  (_♯ₐ : Hash Address)
  (_≟ₐ_ : Decidable {A = Address} _≡_)
  where

open import UTxO.Types       Address _♯ₐ _≟ₐ_
open import UTxO.Value       Address _♯ₐ _≟ₐ_
open import UTxO.Ledger      Address _♯ₐ _≟ₐ_
open import UTxO.Hashing.Tx  Address _♯ₐ _≟ₐ_
open import UTxO.TxUtilities Address _♯ₐ _≟ₐ_

record IsValidTx (tx : Tx) (l : Ledger) : Set where

  field

    validTxRefs :
      ∀ i → i ∈ inputs tx →
        Any (λ t → t ♯ₜₓ ≡ id (outputRef i)) l

    validOutputIndices :
      ∀ i → (i∈ : i ∈ inputs tx) →
          index (outputRef i) < length (outputs (lookupTx l (outputRef i) (validTxRefs i i∈)))

    -----------------------------------------------------------------------------------------

    -- all inputs refer to unspent outputs
    validOutputRefs :
      ∀ i → i ∈ inputs tx →
        outputRef i ∈ map outRef (utxo l)

    preservesValues :
      forge tx + ∑∈ (inputs tx) (λ i p → value (lookupOutput l (outputRef i) (validTxRefs i p) (validOutputIndices i p)))
      ≡
      fee tx + ∑ (outputs tx) value

    noDoubleSpending :
      Unique (map outputRef (inputs tx))

    allInputsValidate :
      ∀ i → (i∈ : i ∈ inputs tx) →
        let out = lookupOutput l (outputRef i) (validTxRefs i i∈) (validOutputIndices i i∈)
            ptx = mkPendingTx l tx i i∈ validTxRefs validOutputIndices 
        in T (runValidation ptx i)

    validateValidHashes :
      ∀ i → (i∈ : i ∈ inputs tx) →
        let out = lookupOutput l (outputRef i) (validTxRefs i i∈) (validOutputIndices i i∈)
        in (address out) ♯ₐ ≡ (validator i) ♯

    validInterval :
      T (range tx ∋ length l)

open IsValidTx public

-- List notation for constructing valid ledgers.
data ValidLedger : Ledger → Set where

  ∙ : ValidLedger []

  _⊕_∶-_ : ∀ {l}
         → ValidLedger l
         → (t : Tx)
         → IsValidTx t l
         → ValidLedger (t ∷ l)

infixl 5 _⊕_∶-_
