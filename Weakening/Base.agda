------------------------------------------------------------------------
-- Basic definition of weakening.
------------------------------------------------------------------------

open import Function.Injection using (module Injection; _↣_)

open import Data.List using (map)

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Hashing.Base

module Weakening.Base
  (𝔸 : Set) (_♯ᵃ : Hash 𝔸) (_≟ᵃ_ : Decidable {A = 𝔸} _≡_) -- smaller address space
  (𝔹 : Set) (_♯ᵇ : Hash 𝔹) (_≟ᵇ_ : Decidable {A = 𝔹} _≡_) -- larger address space
  (A↣B : 𝔸 , _♯ᵃ ↪ 𝔹 , _♯ᵇ)
  where

import UTxO.Validity          𝔸 _♯ᵃ _≟ᵃ_ as A
import UTxO.DecisionProcedure 𝔸 _♯ᵃ _≟ᵃ_ as DA
import UTxO.Validity          𝔹 _♯ᵇ _≟ᵇ_ as B
import UTxO.DecisionProcedure 𝔹 _♯ᵇ _≟ᵇ_ as DB

weakenTxOutput : A.TxOutput → B.TxOutput
weakenTxOutput record { value = v ; dataScript = ds ; address = addr }
             = record { value = v ; dataScript = ds ; address = A↣B ⟨$⟩ addr}

weakenTx : A.Tx → B.Tx
weakenTx record { inputs  = inputs
                ; outputs = outputs
                ; forge   = forge
                ; fee     = fee }
       = record { inputs  = inputs
                ; outputs = map weakenTxOutput outputs
                ; forge   = forge
                ; fee     = fee }

weakenLedger : A.Ledger → B.Ledger
weakenLedger = map weakenTx
