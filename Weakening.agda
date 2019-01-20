------------------------------------------------------------------------
-- Weakening (adding available addresses).
------------------------------------------------------------------------

module Weakening where

open import Data.Unit     using (⊤; tt)
open import Data.Bool     using (Bool; true; false)
open import Data.Nat      using (ℕ; zero; suc; _+_; _<_; _≟_)
open import Data.List     using (List; []; _∷_; _∷ʳ_; [_]; _++_; length; upTo; map)
open import Data.Fin      using (Fin)
  renaming (zero to 0ᶠ; suc to sucᶠ)
open import Data.List.Any using (Any; here; there)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Utilities.Lists
open import Basic

Ledger′ : List Address → Set₁
Ledger′ as = Ledger
  where open import UTxO as

Tx′ : List Address → Set₁
Tx′ as = Tx
  where open import UTxO as

IsValidTx′ : (as : List Address) → Tx′ as → Ledger′ as → Set₁
IsValidTx′ as t l = IsValidTx t l
  where open import UTxO as

TxInput′ : List Address → Set₁
TxInput′ as = TxInput
  where open import Types as

TxOutput′ : List Address → Set
TxOutput′ as = TxOutput
  where open import Types as

TxOutputRef′ : List Address → Set
TxOutputRef′ as = TxOutputRef
  where open import Types as

open import Data.List.Relation.Sublist.Propositional using (_⊆_)
open import Data.List.Relation.Sublist.Propositional.Properties using (⊆-length)

weakenOutRef : ∀ {as bs} → as ⊆ bs → TxOutputRef′ as → TxOutputRef′ bs
weakenOutRef {as} {bs} pr
    record { id = id ; index = i }
  = record { id = id ; index = i }

weakenTxInput : ∀ {as bs} → as ⊆ bs → TxInput′ as → TxInput′ bs
weakenTxInput {as} {bs} pr
    record { outputRef = or ; R = R ; redeemer = red ; validator = val}
  = record { outputRef = weakenOutRef pr or ; R = R ; redeemer = red ; validator = val }

open import Data.Fin using (inject≤)

weakenTxOutput : ∀ {as bs} → as ⊆ bs → TxOutput′ as → TxOutput′ bs
weakenTxOutput {as} {bs} pr
    record { value = v ; address = addr }
  = $ v at inject≤ addr (⊆-length pr)
  where open import Types bs

weakenTx : ∀ {as bs} → as ⊆ bs → Tx′ as → Tx′ bs
weakenTx {as} {bs} pr record { inputs = inputs
                             ; outputs = outputs
                             ; forge = forge
                             ; fee = fee } =
  record { inputs = map (weakenTxInput pr) inputs
         ; outputs = map (weakenTxOutput pr) outputs
         ; forge = forge
         ; fee = fee
         }

weakenLedger : ∀ {as bs} → as ⊆ bs → Ledger′ as → Ledger′ bs
weakenLedger pr = map (weakenTx pr)

weakening : ∀ {as bs : List Address} {t : Tx′ as} {l : Ledger′ as}

          → (as⊆bs : as ⊆ bs)
          → IsValidTx′ as t l
            -------------------------------------------
          → IsValidTx′ bs (weakenTx as⊆bs t) (weakenLedger as⊆bs l)
weakening as⊆bs pr = record
                       { validTxRefs = λ i x → {!!}
                       ; validOutputIndices = {!!}
                       ; validOutputRefs = {!!}
                       ; preservesValues = {!!}
                       ; noDoubleSpending = {!!}
                       ; allInputsValidate = {!!}
                       ; validateValidHashes = {!!}
                       }
