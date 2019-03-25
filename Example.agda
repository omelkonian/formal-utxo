------------------------------------------------------------------------
-- UTxO examples.
------------------------------------------------------------------------

module Example where

open import Level         using (0ℓ) renaming (suc to lsuc)
open import Function      using (case_of_)
open import Data.Unit     using (⊤; tt)
open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Product  using (_,_)
open import Data.Bool     using (Bool; true; false; T)
open import Data.Nat      using (ℕ; zero; suc; _+_; _<_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.List     using (List; []; _∷_; _∷ʳ_; [_]; _++_; length; upTo; sum; map)
open import Data.Fin      using (Fin; toℕ; fromℕ≤)
  renaming (zero to 0ᶠ; suc to sucᶠ)
open import Data.List.Any using (Any; here; there)

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; setoid; refl; cong; sym)

open import Relation.Nullary           using (¬_; yes; no)
open import Relation.Nullary.Negation  using (¬?)
open import Relation.Nullary.Decidable using (True; False; toWitness)

open import Utilities.Lists
open import Types

module Examples where

  -- available addresses
  addresses : List Address
  addresses = 1 ∷ 2 ∷ 3 ∷ []

  open import UTxO addresses
  open import DecisionProcedure addresses

  1ᶠ : Fin 3
  1ᶠ = sucᶠ 0ᶠ

  2ᶠ : Fin 3
  2ᶠ = sucᶠ (sucᶠ 0ᶠ)

  -- postulate valid hashing of (dummy) validator scripts
  dummyRedeemer : State → ℕ
  dummyRedeemer = λ _ → 0

  dummyValidator : State → Value → ℕ → ℕ → Bool
  dummyValidator = λ _ _ _ _ → true

  withScripts : TxOutputRef → TxInput
  withScripts tin = record { outputRef = tin
                           ; redeemer  = dummyRedeemer
                           ; validator = dummyValidator
                           }

  dummyDataScript : State → ℕ
  dummyDataScript = λ _ → 0

  $_at_ : Value → Index addresses → TxOutput
  $ v at addr = record { value      = v
                       ; address    = addr
                       ; dataScript = dummyDataScript
                       }

  postulate
    validator♯ : ∀ {i : Index addresses} → toℕ i ≡ dummyValidator ♯

  t₁ : Tx
  t₁ = record { inputs  = []
              ; outputs = [ $ 1000 at 0ᶠ ]
              ; forge   = $ 1000
              ; fee     = $ 0
              }

  out₁₀ : TxOutputRef
  out₁₀ = (t₁ ♯) indexed-at 0

  t₂ : Tx
  t₂ = record { inputs  = [ withScripts out₁₀ ]
              ; outputs = $ 800 at 1ᶠ ∷ $ 200 at 0ᶠ ∷ []
              ; forge   = $ 0
              ; fee     = $ 0
              }

  out₂₀ : TxOutputRef
  out₂₀ = (t₂ ♯) indexed-at 0

  out₂₁ : TxOutputRef
  out₂₁ = (t₂ ♯) indexed-at 1

  t₃ : Tx
  t₃ = record { inputs  = [ withScripts out₂₁ ]
              ; outputs = [ $ 199 at 2ᶠ ]
              ; forge   = $ 0
              ; fee     = $ 1
              }

  out₃₀ : TxOutputRef
  out₃₀ = (t₃ ♯) indexed-at 0

  t₄ : Tx
  t₄ = record { inputs  = [ withScripts out₃₀ ]
              ; outputs = [ $ 207 at 1ᶠ ]
              ; forge   = $ 10
              ; fee     = $ 2
              }

  out₄₀ : TxOutputRef
  out₄₀ = (t₄ ♯) indexed-at 0

  t₅ : Tx
  t₅ = record { inputs  = withScripts out₂₀ ∷ withScripts out₄₀ ∷ []
              ; outputs = $ 500 at 1ᶠ ∷ $ 500 at 2ᶠ ∷ []
              ; forge   = $ 0
              ; fee     = $ 7
              }

  out₅₀ : TxOutputRef
  out₅₀ = (t₅ ♯) indexed-at 0

  out₅₁ : TxOutputRef
  out₅₁ = (t₅ ♯) indexed-at 1


  t₆ : Tx
  t₆ = record { inputs  = withScripts out₅₀ ∷ withScripts out₅₁ ∷ []
              ; outputs = [ $ 999 at 2ᶠ ]
              ; forge   = $ 0
              ; fee     = $ 1
              }

  out₆₀ : TxOutputRef
  out₆₀ = (t₆ ♯) indexed-at 0

  ex-ledger : ValidLedger (t₆ ∷ t₅ ∷ t₄ ∷ t₃ ∷ t₂ ∷ t₁ ∷ [])
  ex-ledger =
    ∙ t₁ ∶- record
              { validTxRefs          = v₀₀
              ; validOutputIndices   = v₀₁
              ; validOutputRefs      = v₀₂
              ; validDataScriptTypes = v₀₃
              ; preservesValues      = refl
              ; noDoubleSpending     = tt
              ; allInputsValidate    = v₀₄
              ; validateValidHashes  = λ i ()
              }
    ⊕ t₂ ∶- record
              { validTxRefs          = v₀
              ; validOutputIndices   = v₁
              ; validOutputRefs      = v₂
              ; validDataScriptTypes = v₃
              ; preservesValues      = refl
              ; noDoubleSpending     = tt
              ; allInputsValidate    = v₄
              ; validateValidHashes  = λ{ i (here refl) → validator♯ ; i (there ()) }
              }
    ⊕ t₃ ∶- record
              { validTxRefs          = v₀′
              ; validOutputIndices   = v₁′
              ; validOutputRefs      = v₂′
              ; validDataScriptTypes = v₃′
              ; preservesValues      = refl
              ; noDoubleSpending     = tt
              ; allInputsValidate    = v₄′
              ; validateValidHashes  = λ{ i (here refl) → validator♯ ; i (there ()) }
              }
    ⊕ t₄ ∶- record
              { validTxRefs          = v₀″
              ; validOutputIndices   = v₁″
              ; validOutputRefs      = v₂″
              ; validDataScriptTypes = v₃″
              ; preservesValues      = refl
              ; noDoubleSpending     = tt
              ; allInputsValidate    = v₄″
              ; validateValidHashes  = λ{ i (here refl) → validator♯ ; i (there ()) }
              }
    ⊕ t₅ ∶- record
              { validTxRefs          = v₀‴
              ; validOutputIndices   = v₁‴
              ; validOutputRefs      = v₂‴
              ; validDataScriptTypes = v₃‴
              ; preservesValues      = refl
              ; noDoubleSpending     = nodup-20-40
              ; allInputsValidate    = v₄‴
              ; validateValidHashes  = λ{ i (here refl) → validator♯
                                        ; i (there (here refl)) → validator♯
                                        ; i (there (there ())) }
              }
    ⊕ t₆ ∶- record
              { validTxRefs          = v₀⁗
              ; validOutputIndices   = v₁⁗
              ; validOutputRefs      = v₂⁗
              ; validDataScriptTypes = v₃⁗
              ; preservesValues      = refl
              ; noDoubleSpending     = nodup-50-51
              ; allInputsValidate    = v₄⁗
              ; validateValidHashes  = λ{ i (here refl) → validator♯
                                        ; i (there (here refl)) → validator♯
                                        ; i (there (there ())) }
              }

    where

      open SETₒ using (_∈?_; from↔to; list; noDuplicates; noDuplicates?)
        renaming (_∈′_ to _∈ₒ_)
      open import Data.List.Membership.Propositional using (_∈_; mapWith∈)

      ----------------------------------------------------------------------------------

      l₀ : Ledger
      l₀ = []

      v₀₀ : ∀ i → i ∈ inputs t₁ → Any (λ tx → tx ♯ ≡ id (outputRef i)) l₀
      v₀₀ = toWitness {Q = validTxRefs? t₁ l₀} tt

      v₀₁ : ∀ i → (i∈ : i ∈ inputs t₁) →
             index (outputRef i) <
               length (outputs (lookupTx l₀ (outputRef i) (v₀₀ i i∈)))
      v₀₁ = toWitness {Q = validOutputIndices? t₁ l₀ v₀₀} tt

      v₀₂ : ∀ i → i ∈ inputs t₁ → outputRef i ∈ₒ unspentOutputs l₀
      v₀₂ = toWitness {Q = validOutputRefs? t₁ l₀} tt

      v₀₃ : ∀ i → (i∈ : i ∈ inputs t₁) →
        D i ≡ Data (lookupOutput l₀ (outputRef i) (v₀₀ i i∈) (v₀₁ i i∈))
      v₀₃ = toWitness {Q = validDataScriptTypes? t₁ l₀ v₀₀ v₀₁} tt

      v₀₄ : ∀ i → (i∈ : i ∈ inputs t₁) → (st : State) →
        T (runValidation i (lookupOutput l₀ (outputRef i) (v₀₀ i i∈) (v₀₁ i i∈)) (v₀₃ i i∈) st)
      v₀₄ i i∈ st = (toWitness {Q = allInputsValidate? t₁ l₀ v₀₀ v₀₁ v₀₃ st} tt) i i∈

      ----------------------------------------------------------------------------------

      l₁ : Ledger
      l₁ = t₁ ∷ []

      v₀ : ∀ i → i ∈ inputs t₂ → Any (λ tx → tx ♯ ≡ id (outputRef i)) l₁
      -- v₀ = toWitness {Q = validTxRefs? t₂ l₁} tt
      v₀ i (here refl) = here refl
      v₀ i (there ())

      v₁ : ∀ i → (i∈ : i ∈ inputs t₂) →
             index (outputRef i) <
               length (outputs (lookupTx l₁ (outputRef i) (v₀ i i∈)))
      v₁ = toWitness {Q = validOutputIndices? t₂ l₁ v₀} tt
      -- v₁ .(withScripts out₁₀) (here refl) = s≤s z≤n
      -- v₁ i (there ())

      v₂ : ∀ i → i ∈ inputs t₂ → outputRef i ∈ₒ unspentOutputs l₁
      -- v₂ = toWitness {Q = validOutputRefs? t₂ l₁} tt
      v₂ i (here refl) = here refl
      v₂ i (there ())

      v₃ : ∀ i → (i∈ : i ∈ inputs t₂) →
        D i ≡ Data (lookupOutput l₁ (outputRef i) (v₀ i i∈) (v₁ i i∈))
      v₃ = toWitness {Q = validDataScriptTypes? t₂ l₁ v₀ v₁} tt
      -- v₃ i (here refl) = refl
      -- v₃ i (there ())

      v₄ : ∀ i → (i∈ : i ∈ inputs t₂) → (st : State) →
        T (runValidation i (lookupOutput l₁ (outputRef i) (v₀ i i∈) (v₁ i i∈)) (v₃ i i∈) st)
      v₄ i i∈ st = (toWitness {Q = allInputsValidate? t₂ l₁ v₀ v₁ v₃ st} tt) i i∈
      -- v₄ .(withScripts out₁₀) (here refl) _ = tt
      -- v₄ i (there ())

      ----------------------------------------------------------------------------------

      l₂ : Ledger
      l₂ = t₂ ∷ t₁ ∷ []

      v₀′ : ∀ i → i ∈ inputs t₃ → Any (λ tx → tx ♯ ≡ id (outputRef i)) l₂
      -- v₀′ = toWitness {Q = validTxRefs? t₃ l₂} tt
      v₀′ i (here refl) = here refl
      v₀′ i (there ())

      v₁′ : ∀ i → (i∈ : i ∈ inputs t₃) →
             index (outputRef i) <
               length (outputs (lookupTx l₂ (outputRef i) (v₀′ i i∈)))
      v₁′ = toWitness {Q = validOutputIndices? t₃ l₂ v₀′} tt
      -- v₁′ .(withScripts out₂₁) (here refl) = s≤s ≤-refl
      -- v₁′ i (there ())

      nodup-20-21 : noDuplicates (out₂₀ ∷ out₂₁ ∷ [])
      nodup-20-21 with out₂₀ ∈? out₂₁ ∷ []
      ... | yes (here ())
      ... | yes (there ())
      ... | no ¬p = tt

      utxo-t₂ : list (unspentOutputsTx t₂) ≡ out₂₀ ∷ out₂₁ ∷ []
      utxo-t₂ rewrite from↔to {xs = out₂₀ ∷ out₂₁ ∷ [] } nodup-20-21 = refl

      utxo-l₂ : list (unspentOutputs l₂) ≡ out₂₀ ∷ out₂₁ ∷ []
      utxo-l₂ with out₁₀ ∈? [ out₁₀ ]
      ... | no ¬p = ⊥-elim (¬p (here refl))
      ... | yes p rewrite utxo-t₂ = refl

      v₂′ : ∀ i → i ∈ inputs t₃ → outputRef i ∈ₒ unspentOutputs l₂
      -- v₂′ = toWitness {Q = validOutputRefs? t₃ l₂} tt
      v₂′ .(withScripts out₂₁) (here refl) rewrite utxo-l₂ = there (here refl)
      v₂′ i (there ())

      v₃′ : ∀ i → (i∈ : i ∈ inputs t₃) →
        D i ≡ Data (lookupOutput l₂ (outputRef i) (v₀′ i i∈) (v₁′ i i∈))
      v₃′ = toWitness {Q = validDataScriptTypes? t₃ l₂ v₀′ v₁′} tt
      -- v₃′ i (here refl) = refl
      -- v₃′ i (there ())

      v₄′ : ∀ i → (i∈ : i ∈ inputs t₃) → (st : State) →
        T (runValidation i (lookupOutput l₂ (outputRef i) (v₀′ i i∈) (v₁′ i i∈)) (v₃′ i i∈) st)
      v₄′ i i∈ st = (toWitness {Q = allInputsValidate? t₃ l₂ v₀′ v₁′ v₃′ st} tt) i i∈
      -- v₄′ .(withScripts out₂₁) (here refl) _ = tt
      -- v₄′ i (there ())

      ----------------------------------------------------------------------------------

      l₃ : Ledger
      l₃ = t₃ ∷ t₂ ∷ t₁ ∷ []

      v₀″ : ∀ i → i ∈ inputs t₄ → Any (λ tx → tx ♯ ≡ id (outputRef i)) l₃
      -- v₀″ = toWitness {Q = validTxRefs? t₄ l₃} tt
      v₀″ i (here refl) = here refl
      v₀″ i (there ())

      v₁″ : ∀ i → (i∈ : i ∈ inputs t₄) →
             index (outputRef i) <
               length (outputs (lookupTx l₃ (outputRef i) (v₀″ i i∈)))
      v₁″ = toWitness {Q = validOutputIndices? t₄ l₃ v₀″} tt
      -- v₁″ .(withScripts out₃₀) (here refl) = s≤s ≤-refl
      -- v₁″ i (there ())

      index≡-inj : ∀ {t t′ i} → t indexed-at i ≡ t′ indexed-at i → t ≡ t′
      index≡-inj refl = refl

      utxo-l₃ : list (unspentOutputs l₃) ≡ out₂₀ ∷ out₃₀ ∷ []
      utxo-l₃ rewrite utxo-l₂
         with out₂₀ ∈? [ out₂₁ ]
      ... | yes (here ())
      ... | yes (there ())
      ... | no _
         with out₂₁ ∈? [ out₂₁ ]
      ... | no ¬p = ⊥-elim (¬p (here refl))
      ... | yes (there ())
      ... | yes (here refl)
         with out₃₀ ∈? [ out₂₀ ]
      ... | yes (here eq) = case (♯-injective (index≡-inj eq)) of λ ()
      ... | yes (there ())
      ... | no _ = refl

      v₂″ : ∀ i → i ∈ inputs t₄ → outputRef i ∈ₒ unspentOutputs l₃
      -- v₂″ = toWitness {Q = validOutputRefs? t₄ l₃} tt
      v₂″ .(withScripts out₃₀) (here refl) rewrite utxo-l₃ = there (here refl)
      v₂″ i (there ())

      v₃″ : ∀ i → (i∈ : i ∈ inputs t₄) →
        D i ≡ Data (lookupOutput l₃ (outputRef i) (v₀″ i i∈) (v₁″ i i∈))
      v₃″ = toWitness {Q = validDataScriptTypes? t₄ l₃ v₀″ v₁″} tt
      -- v₃″ i (here refl) = refl
      -- v₃″ i (there ())

      v₄″ : ∀ i → (i∈ : i ∈ inputs t₄) → (st : State) →
        T (runValidation i (lookupOutput l₃ (outputRef i) (v₀″ i i∈) (v₁″ i i∈)) (v₃″ i i∈) st)
      v₄″ i i∈ st = (toWitness {Q = allInputsValidate? t₄ l₃ v₀″ v₁″ v₃″ st} tt) i i∈
      -- v₄″ .(withScripts out₃₀) (here refl) _ = tt
      -- v₄″ i (there ())

      ----------------------------------------------------------------------------------

      l₄ : Ledger
      l₄ = t₄ ∷ t₃ ∷ t₂ ∷ t₁ ∷ []

      nodup-20-40 : noDuplicates (out₂₀ ∷ out₄₀ ∷ [])
      nodup-20-40 with out₂₀ ∈? [ out₄₀ ]
      ... | no  _         = tt
      ... | yes (here eq) = case (♯-injective (index≡-inj eq)) of λ ()
      ... | yes (there ())

      v₀‴ : ∀ i → i ∈ inputs t₅ → Any (λ tx → tx ♯ ≡ id (outputRef i)) l₄
      -- v₀‴ = toWitness {Q = validTxRefs? t₅ l₄} tt
      v₀‴ i (here refl)         = there (there (here refl))
      v₀‴ i (there (here refl)) = here refl
      v₀‴ i (there (there ()))

      v₁‴ : ∀ i → (i∈ : i ∈ inputs t₅) →
             index (outputRef i) <
               length (outputs (lookupTx l₄ (outputRef i) (v₀‴ i i∈)))
      v₁‴ = toWitness {Q = validOutputIndices? t₅ l₄ v₀‴} tt
      -- v₁‴ .(withScripts out₂₀) (here refl)         = s≤s z≤n
      -- v₁‴ .(withScripts out₄₀) (there (here refl)) = s≤s z≤n
      -- v₁‴ i (there (there ()))

      utxo-l₄ : list (unspentOutputs l₄) ≡ out₂₀ ∷ out₄₀ ∷ []
      utxo-l₄ rewrite utxo-l₃
         with out₂₀ ∈? [ out₃₀ ]
      ... | yes (here eq) = case (♯-injective (index≡-inj eq)) of λ ()
      ... | yes (there ())
      ... | no _
         with out₃₀ ∈? [ out₃₀ ]
      ... | no ¬p = ⊥-elim (¬p (here refl))
      ... | yes (there ())
      ... | yes (here refl)
         with out₄₀ ∈? [ out₂₀ ]
      ... | yes (here eq) = case (♯-injective (index≡-inj eq)) of λ ()
      ... | yes (there ())
      ... | no _ = refl

      v₂‴ : ∀ i → i ∈ inputs t₅ → outputRef i ∈ₒ unspentOutputs l₄
      -- v₂‴ = toWitness {Q = validOutputRefs? t₅ l₄} tt
      v₂‴ .(withScripts out₂₀) (here refl)         rewrite utxo-l₄ = here refl
      v₂‴ .(withScripts out₄₀) (there (here refl)) rewrite utxo-l₄ = there (here refl)
      v₂‴ i (there (there ()))

      v₃‴ : ∀ i → (i∈ : i ∈ inputs t₅) →
        D i ≡ Data (lookupOutput l₄ (outputRef i) (v₀‴ i i∈) (v₁‴ i i∈))
      v₃‴ = toWitness {Q = validDataScriptTypes? t₅ l₄ v₀‴ v₁‴} tt
      -- v₃‴ i (here refl)         = refl
      -- v₃‴ i (there (here refl)) = refl
      -- v₃‴ i (there (there ()))

      v₄‴ : ∀ i → (i∈ : i ∈ inputs t₅) → (st : State) →
        T (runValidation i (lookupOutput l₄ (outputRef i) (v₀‴ i i∈) (v₁‴ i i∈)) (v₃‴ i i∈) st)
      v₄‴ i i∈ st = (toWitness {Q = allInputsValidate? t₅ l₄ v₀‴ v₁‴ v₃‴ st} tt) i i∈
      -- v₄‴ .(withScripts out₂₀) (here refl)         _ = tt
      -- v₄‴ .(withScripts out₄₀) (there (here refl)) _ = tt
      -- v₄‴ i (there (there ()))

      ----------------------------------------------------------------------------------

      l₅ : Ledger
      l₅ = t₅ ∷ t₄ ∷ t₃ ∷ t₂ ∷ t₁ ∷ []

      nodup-50-51 : noDuplicates (out₅₀ ∷ out₅₁ ∷ [])
      nodup-50-51 with out₅₀ ∈? out₅₁ ∷ []
      ... | yes (here ())
      ... | yes (there ())
      ... | no ¬p = tt

      v₀⁗ : ∀ i → i ∈ inputs t₆ → Any (λ tx → tx ♯ ≡ id (outputRef i)) l₅
      -- v₀⁗ = toWitness {Q = validTxRefs? t₆ l₅} tt
      v₀⁗ i (here refl)         = here refl
      v₀⁗ i (there (here refl)) = here refl
      v₀⁗ i (there (there ()))

      v₁⁗ : ∀ i → (i∈ : i ∈ inputs t₆) →
             index (outputRef i) <
               length (outputs (lookupTx l₅ (outputRef i) (v₀⁗ i i∈)))
      v₁⁗ = toWitness {Q = validOutputIndices? t₆ l₅ v₀⁗} tt
      -- v₁⁗ .(withScripts out₅₀) (here refl)         = s≤s z≤n
      -- v₁⁗ .(withScripts out₅₁) (there (here refl)) = s≤s ≤-refl
      -- v₁⁗ i (there (there ()))

      utxo-t₅ : list (unspentOutputsTx t₅) ≡ out₅₀ ∷ out₅₁ ∷ []
      utxo-t₅ rewrite from↔to {xs = out₅₀ ∷ out₅₁ ∷ []} nodup-50-51 = refl

      stxo-t₅ : list (spentOutputsTx t₅) ≡ out₂₀ ∷ out₄₀ ∷ []
      stxo-t₅ rewrite from↔to {xs = out₂₀ ∷ out₄₀ ∷ []} nodup-20-40 = refl

      utxo-l₅ : list (unspentOutputs l₅) ≡ out₅₀ ∷ out₅₁ ∷ []
      utxo-l₅ rewrite utxo-l₄ | utxo-t₅ | stxo-t₅
         with out₂₀ ∈? out₂₀ ∷ out₄₀ ∷ []
      ... | no ¬p = ⊥-elim (¬p (here refl))
      ... | yes (there (there ()))
      ... | yes (there (here eq)) = case (♯-injective (index≡-inj eq)) of λ ()
      ... | yes (here refl)
         with out₄₀ ∈? out₂₀ ∷ out₄₀ ∷ []
      ... | no ¬p = ⊥-elim (¬p (there (here refl)))
      ... | yes (here eq) = case (♯-injective (index≡-inj eq)) of λ ()
      ... | yes (there (there ()))
      ... | yes (there (here refl)) = refl

      v₂⁗ : ∀ i → i ∈ inputs t₆ → outputRef i ∈ₒ unspentOutputs l₅
      -- v₂⁗ = toWitness {Q = validOutputRefs? t₆ l₅} tt
      v₂⁗ .(withScripts out₅₀) (here refl)         rewrite utxo-l₅ = here refl
      v₂⁗ .(withScripts out₅₁) (there (here refl)) rewrite utxo-l₅ = there (here refl)
      v₂⁗ i (there (there ()))

      v₃⁗ : ∀ i → (i∈ : i ∈ inputs t₆) →
        D i ≡ Data (lookupOutput l₅ (outputRef i) (v₀⁗ i i∈) (v₁⁗ i i∈))
      v₃⁗ = toWitness {Q = validDataScriptTypes? t₆ l₅ v₀⁗ v₁⁗} tt
      -- v₃⁗ i (here refl)         = refl
      -- v₃⁗ i (there (here refl)) = refl
      -- v₃⁗ i (there (there ()))

      v₄⁗ : ∀ i → (i∈ : i ∈ inputs t₆) → (st : State) →
        T (runValidation i (lookupOutput l₅ (outputRef i) (v₀⁗ i i∈) (v₁⁗ i i∈)) (v₃⁗ i i∈) st)
      v₄⁗ i i∈ st = (toWitness {Q = allInputsValidate? t₆ l₅ v₀⁗ v₁⁗ v₃⁗ st} tt) i i∈
      -- v₄⁗ .(withScripts out₅₀) (here refl)         _ = tt
      -- v₄⁗ .(withScripts out₅₁) (there (here refl)) _ = tt
      -- v₄⁗ i (there (there ()))
