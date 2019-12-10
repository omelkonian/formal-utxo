module StateMachine.Properties.Liveness2 where

open import Data.Empty   using (⊥-elim)
open import Data.Bool    using (T)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; map₁; map₂)
open import Data.Maybe   using (fromMaybe)
  renaming (just to pure)
open import Data.Nat     using (_+_)
open import Data.Fin     using (toℕ)

import Data.List.Relation.Unary.Any as Any
open import Data.List.Membership.Propositional  using (_∈_)

open import Relation.Nullary                      using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Prelude.Lists

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Hashing.MetaHash
open import UTxO.Types hiding (I)
open import StateMachine.Base

open import StateMachine.Properties.Liveness

liveness′ : ∀ {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
              {s : S} {i : I} {s′ : S} {l : Ledger}
              {prevTx : Tx} {v : Value} {ptx≡ : TxConstraints}

    -- `s —→[i] s′` constitutes a valid transition in the state machine
  → step sm s i ≡ pure (s′ , ptx≡)

    -- we are not moving to a final state
  → ¬ (T (isFinal sm s′))

    -- existing ledger is valid
  → (vl : ValidLedger l)
  → l -compliesTo- ptx≡

    -- previous output is an element of previous transaction
  → (prevOut∈prevTx : s —→ $ v at sm ∈ outputs prevTx)

  → let prevTxRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈prevTx)
        txIn      = prevTxRef ←— i , sm
        v′        = v + fromMaybe ($ 0) (forge≡ ptx≡)
    in

    -- previous unspent output
    prevTxRef SETₒ.∈′ unspentOutputs l

    ---------------------------------------------------------------------------------------

  → ∃[ tx ](
      -- (1) new transaction is valid
      Σ[ vtx ∈ IsValidTx tx l ]
      -- (2) it contains the source state in its inputs, using the state machine's validator
      Σ[ i∈  ∈ (txIn ∈ inputs tx) ]
        let ptx = mkPendingTx l tx txIn i∈ (validTxRefs vtx) (validOutputIndices vtx) in
      -- (3) it contains the target state in its outputs
           (s′ —→ $ v′ at sm ∈ outputs tx)
      -- (4) it satisfied the constraints imposed by the state machine
         × T (verifyPtx ptx ptx≡))

liveness′ {S} {I} {sm} {s} {i} {s′} {l} {prevTx} {v} {ptx≡} step≡ ¬fin vl range∋l prevOut∈prevTx prev∈utxo
  = map₂ (map₂ (map₂ (map₁ (λ f → f ¬fin))))
         (liveness {S} {I} {sm} {s} {i} {s′} {l} {prevTx} {v} {ptx≡}
                   step≡ (λ p → ⊥-elim (¬fin p)) vl range∋l prevOut∈prevTx prev∈utxo)
