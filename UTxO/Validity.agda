open import Data.Bool     using (T)
open import Data.Product  using (∃; ∃-syntax)
open import Data.Nat      using (_<_)
open import Data.List     using ([]; _∷_; length; map)
open import Data.List.Any using (Any)

open import Data.List.Membership.Propositional            using (_∈_; mapWith∈)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import UTxO.Types
open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Hashing.MetaHash using (_♯)

module UTxO.Validity
  (Address : Set)
  (_♯ₐ : Hash Address)
  (_≟ₐ_ : Decidable {A = Address} _≡_)
  where

open import UTxO.TxUtilities Address _♯ₐ _≟ₐ_ public

record IsValidTx (tx : Tx) (l : Ledger) : Set where

  field

    validTxRefs :
      ∀ i → i ∈ inputs tx →
        Any (λ t → t ♯ₜₓ ≡ id (outputRef i)) l

    validOutputIndices :
      ∀ i → (i∈ : i ∈ inputs tx) →
          index (outputRef i) < length (outputs (lookupTx l (outputRef i) (validTxRefs i i∈)))

    validOutputRefs :
      ∀ i → i ∈ inputs tx →
        outputRef i SETₒ.∈′ unspentOutputs l

    -----------------------------------------------------------------------------------------

    preservesValues :
      forge tx +ᶜ sumᶜ (mapWith∈ (inputs tx) λ {i} i∈ →
                          lookupValue l i (validTxRefs i i∈) (validOutputIndices i i∈))
        ≡
      fee tx +ᶜ sumᶜ (map value (outputs tx))

    noDoubleSpending :
      Unique (map outputRef (inputs tx))

    allInputsValidate :
      ∀ i → (i∈ : i ∈ inputs tx) →
        let out = lookupOutput l (outputRef i) (validTxRefs i i∈) (validOutputIndices i i∈)
            ptx = mkPendingTx l tx validTxRefs validOutputIndices
        in T (runValidation ptx i out)

    validateValidHashes :
      ∀ i → (i∈ : i ∈ inputs tx) →
        let out = lookupOutput l (outputRef i) (validTxRefs i i∈) (validOutputIndices i i∈)
        in (address out) ♯ₐ ≡ (validator i) ♯

    -- enforce monetary policies
    forging :
      ∀ c → c ∈ keys (forge tx) →
        ∃[ i ] ∃ λ (i∈ : i ∈ inputs tx) →
          let out = lookupOutput l (outputRef i) (validTxRefs i i∈) (validOutputIndices i i∈)
          in (address out) ♯ₐ ≡ c


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
