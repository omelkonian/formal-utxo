{-# OPTIONS --rewriting #-}
module Example.Ledger where

open import Example.Setup

ex-ledger : ValidLedger (t₆ ∷ t₅ ∷ t₄ ∷ t₃ ∷ t₂ ∷ t₁ ∷ c₄ ∷ c₁ ∷ [])
ex-ledger =
    ∙ c₁ ∶- record
                { validTxRefs          = λ _ ()
                ; validOutputIndices   = λ _ ()
                ; validOutputRefs      = λ _ ()
                ; validDataScriptTypes = λ _ ()
                ; preservesValues      = refl
                ; noDoubleSpending     = tt
                ; allInputsValidate    = λ _ ()
                ; validateValidHashes  = λ _ ()
                ; forging              = λ _ ()
                }
    ⊕ c₄ ∶- record
                { validTxRefs          = λ _ ()
                ; validOutputIndices   = λ _ ()
                ; validOutputRefs      = λ _ ()
                ; validDataScriptTypes = λ _ ()
                ; preservesValues      = refl
                ; noDoubleSpending     = tt
                ; allInputsValidate    = λ _ ()
                ; validateValidHashes  = λ _ ()
                ; forging              = λ _ ()
                }
    ⊕ t₁ ∶- record
                { validTxRefs          = v₀₀
                ; validOutputIndices   = v₀₁
                ; validOutputRefs      = v₀₂
                ; validDataScriptTypes = v₀₃
                ; preservesValues      = refl
                ; noDoubleSpending     = tt
                ; allInputsValidate    = v₀₄
                ; validateValidHashes  = v₀₅
                ; forging              = v₀₆
                }
    ⊕ t₂ ∶- record
                { validTxRefs          = v₀
                ; validOutputIndices   = v₁
                ; validOutputRefs      = v₂
                ; validDataScriptTypes = v₃
                ; preservesValues      = refl
                ; noDoubleSpending     = tt
                ; allInputsValidate    = v₄
                ; validateValidHashes  = v₅
                ; forging              = λ _ ()
                }
    ⊕ t₃ ∶- record
                { validTxRefs          = v₀′
                ; validOutputIndices   = v₁′
                ; validOutputRefs      = v₂′
                ; validDataScriptTypes = v₃′
                ; preservesValues      = refl
                ; noDoubleSpending     = tt
                ; allInputsValidate    = v₄′
                ; validateValidHashes  = v₅′
                ; forging              = λ _ ()
                }
    ⊕ t₄ ∶- record
                { validTxRefs          = v₀″
                ; validOutputIndices   = v₁″
                ; validOutputRefs      = v₂″
                ; validDataScriptTypes = v₃″
                ; preservesValues      = refl
                ; noDoubleSpending     = tt
                ; allInputsValidate    = v₄″
                ; validateValidHashes  = v₅″
                ; forging              = v₆″
                }
    ⊕ t₅ ∶- record
                { validTxRefs          = v₀‴
                ; validOutputIndices   = v₁‴
                ; validOutputRefs      = v₂‴
                ; validDataScriptTypes = v₃‴
                ; preservesValues      = refl
                ; noDoubleSpending     = tt
                ; allInputsValidate    = v₄‴
                ; validateValidHashes  = v₅‴
                ; forging              = λ _ ()
                }
    ⊕ t₆ ∶- record
                { validTxRefs          = v₀⁗
                ; validOutputIndices   = v₁⁗
                ; validOutputRefs      = v₂⁗
                ; validDataScriptTypes = v₃⁗
                ; preservesValues      = refl
                ; noDoubleSpending     = tt
                ; allInputsValidate    = v₄⁗
                ; validateValidHashes  = v₅⁗
                ; forging              = λ _ ()
                }

   where

    ----------------------------------------------------------------------------

    l₀ : Ledger
    l₀ = c₄ ∷ c₁ ∷ []

    v₀₀ : ∀ (i : TxInput) → (i∈ : i ∈ (inputs t₁)) → Any (λ tx → tx ♯ ≡ id (outputRef i)) l₀
    v₀₀ = toWitness {Q = validTxRefs? t₁ l₀} tt

    v₀₁ : ∀ i → (i∈ : i ∈ inputs t₁) →
            index (outputRef i) < length (outputs (lookupTx l₀ (outputRef i) (v₀₀ i i∈)))
    v₀₁ = toWitness {Q = validOutputIndices? t₁ l₀ v₀₀} tt

    v₀₂ : ∀ i → i ∈ inputs t₁ → outputRef i ∈ₒ unspentOutputs l₀
    v₀₂ = toWitness {Q = validOutputRefs? t₁ l₀} tt

    v₀₃ : ∀ i → (i∈ : i ∈ inputs t₁) →
      D i ≡ Data (lookupOutput l₀ (outputRef i) (v₀₀ i i∈) (v₀₁ i i∈))
    v₀₃ = toWitness {Q = validDataScriptTypes? t₁ l₀ v₀₀ v₀₁} tt

    v₀₄ : ∀ i → (i∈ : i ∈ inputs t₁) →
      let out = lookupOutput l₀ (outputRef i) (v₀₀ i i∈) (v₀₁ i i∈)
          ptx = mkPendingTx l₀ t₁ v₀₀ v₀₁
      in T (runValidation ptx i out (v₀₃ i i∈) (getState l₀))
    v₀₄ = toWitness {Q = allInputsValidate? t₁ l₀ v₀₀ v₀₁ v₀₃} tt

    v₀₅ : ∀ i → (i∈ : i ∈ inputs t₁) →
      let out = lookupOutput l₀ (outputRef i) (v₀₀ i i∈) (v₀₁ i i∈)
      in (addresses ‼ address out) ≡ validator i ♯
    v₀₅ = toWitness {Q = validateValidHashes? t₁ l₀ v₀₀ v₀₁} tt

    v₀₆ : ∀ c → c ∈ values (forge t₁) → ∃[ i ] ∃ λ (i∈ : i ∈ inputs t₁) →
      let out = lookupOutput l₀ (outputRef i) (v₀₀ i i∈) (v₀₁ i i∈)
      in (addresses ‼ address out) ≡ c
    v₀₆ = toWitness {Q = forging? t₁ l₀ v₀₀ v₀₁} tt

    ----------------------------------------------------------------------------

    l₁ : Ledger
    l₁ = t₁ ∷ c₄ ∷ c₁ ∷ []

    v₀ : ∀ i → i ∈ inputs t₂ → Any (λ tx → tx ♯ ≡ id (outputRef i)) l₁
    v₀ = toWitness {Q = validTxRefs? t₂ l₁} tt

    v₁ : ∀ i → (i∈ : i ∈ inputs t₂) →
           index (outputRef i) < length (outputs (lookupTx l₁ (outputRef i) (v₀ i i∈)))
    v₁ = toWitness {Q = validOutputIndices? t₂ l₁ v₀} tt

    v₂ : ∀ i → i ∈ inputs t₂ → outputRef i ∈ₒ unspentOutputs l₁
    v₂ = toWitness {Q = validOutputRefs? t₂ l₁} tt

    v₃ : ∀ i → (i∈ : i ∈ inputs t₂) →
      D i ≡ Data (lookupOutput l₁ (outputRef i) (v₀ i i∈) (v₁ i i∈))
    v₃ = toWitness {Q = validDataScriptTypes? t₂ l₁ v₀ v₁} tt

    v₄ : ∀ i → (i∈ : i ∈ inputs t₂) →
      let out = lookupOutput l₁ (outputRef i) (v₀ i i∈) (v₁ i i∈)
          ptx = mkPendingTx l₁ t₂ v₀ v₁
      in T (runValidation ptx i out (v₃ i i∈) (getState l₁))
    v₄ = toWitness {Q = allInputsValidate? t₂ l₁ v₀ v₁ v₃} tt

    v₅ : ∀ i → (i∈ : i ∈ inputs t₂) →
      let out = lookupOutput l₁ (outputRef i) (v₀ i i∈) (v₁ i i∈)
      in (addresses ‼ address out) ≡ validator i ♯
    -- v₅ = toWitness {Q = validateValidHashes? t₂ l₁ v₀ v₁} tt
    v₅ _ (here refl) rewrite validator♯₁₀ = refl
    v₅ _ (there ())

    ----------------------------------------------------------------------------

    l₂ : Ledger
    l₂ = t₂ ∷ t₁ ∷ c₄ ∷ c₁ ∷ []

    v₀′ : ∀ i → i ∈ inputs t₃ → Any (λ tx → tx ♯ ≡ id (outputRef i)) l₂
    v₀′ = toWitness {Q = validTxRefs? t₃ l₂} tt

    v₁′ : ∀ i → (i∈ : i ∈ inputs t₃) →
            index (outputRef i) <
              length (outputs (lookupTx l₂ (outputRef i) (v₀′ i i∈)))
    v₁′ = toWitness {Q = validOutputIndices? t₃ l₂ v₀′} tt

    v₂′ : ∀ i → i ∈ inputs t₃ → outputRef i ∈ₒ unspentOutputs l₂
    v₂′ = toWitness {Q = validOutputRefs? t₃ l₂} tt

    v₃′ : ∀ i → (i∈ : i ∈ inputs t₃) →
      D i ≡ Data (lookupOutput l₂ (outputRef i) (v₀′ i i∈) (v₁′ i i∈))
    v₃′ = toWitness {Q = validDataScriptTypes? t₃ l₂ v₀′ v₁′} tt

    v₄′ : ∀ i → (i∈ : i ∈ inputs t₃) →
      let out = lookupOutput l₂ (outputRef i) (v₀′ i i∈) (v₁′ i i∈)
          ptx = mkPendingTx l₂ t₃ v₀′ v₁′
      in T (runValidation ptx i out (v₃′ i i∈) (getState l₂))
    v₄′ = toWitness {Q = allInputsValidate? t₃ l₂ v₀′ v₁′ v₃′} tt

    v₅′ : ∀ i → (i∈ : i ∈ inputs t₃) →
      let out = lookupOutput l₂ (outputRef i) (v₀′ i i∈) (v₁′ i i∈)
      in (addresses ‼ address out) ≡ validator i ♯
    -- v₅′ = toWitness {Q = validateValidHashes? t₃ l₂ v₀′ v₁′} tt
    v₅′ _ (here refl) rewrite validator♯₂₁ = refl
    v₅′ _ (there ())

    ----------------------------------------------------------------------------

    l₃ : Ledger
    l₃ = t₃ ∷ t₂ ∷ t₁ ∷ c₄ ∷ c₁ ∷ []

    v₀″ : ∀ i → i ∈ inputs t₄ → Any (λ tx → tx ♯ ≡ id (outputRef i)) l₃
    v₀″ = toWitness {Q = validTxRefs? t₄ l₃} tt

    v₁″ : ∀ i → (i∈ : i ∈ inputs t₄) →
            index (outputRef i) < length (outputs (lookupTx l₃ (outputRef i) (v₀″ i i∈)))
    v₁″ = toWitness {Q = validOutputIndices? t₄ l₃ v₀″} tt

    v₂″ : ∀ i → i ∈ inputs t₄ → outputRef i ∈ₒ unspentOutputs l₃
    v₂″ = toWitness {Q = validOutputRefs? t₄ l₃} tt

    v₃″ : ∀ i → (i∈ : i ∈ inputs t₄) →
      D i ≡ Data (lookupOutput l₃ (outputRef i) (v₀″ i i∈) (v₁″ i i∈))
    v₃″ = toWitness {Q = validDataScriptTypes? t₄ l₃ v₀″ v₁″} tt

    v₄″ : ∀ i → (i∈ : i ∈ inputs t₄) →
      let out = lookupOutput l₃ (outputRef i) (v₀″ i i∈) (v₁″ i i∈)
          ptx = mkPendingTx l₃ t₄ v₀″ v₁″
      in T (runValidation ptx i out (v₃″ i i∈) (getState l₃))
    v₄″ = toWitness {Q = allInputsValidate? t₄ l₃ v₀″ v₁″ v₃″} tt

    v₅″ : ∀ i → (i∈ : i ∈ inputs t₄) →
      let out = lookupOutput l₃ (outputRef i) (v₀″ i i∈) (v₁″ i i∈)
      in (addresses ‼ address out) ≡ validator i ♯
    -- v₅″ = toWitness {Q = validateValidHashes? t₄ l₃ v₀″ v₁″} tt
    v₅″ _ (here refl) rewrite validator♯₃₀ = refl
    v₅″ _ (there (here refl)) = refl
    v₅″ _ (there (there ()))

    v₆″ : ∀ c → c ∈ values (forge t₄) → ∃[ i ] ∃ λ (i∈ : i ∈ inputs t₄) →
      let out = lookupOutput l₃ (outputRef i) (v₀″ i i∈) (v₁″ i i∈)
      in (addresses ‼ address out) ≡ c
    v₆″ = toWitness {Q = forging? t₄ l₃ v₀″ v₁″} tt

    ----------------------------------------------------------------------------

    l₄ : Ledger
    l₄ = t₄ ∷ t₃ ∷ t₂ ∷ t₁ ∷ c₄ ∷ c₁ ∷ []

    v₀‴ : ∀ i → i ∈ inputs t₅ → Any (λ tx → tx ♯ ≡ id (outputRef i)) l₄
    v₀‴ = toWitness {Q = validTxRefs? t₅ l₄} tt

    v₁‴ : ∀ i → (i∈ : i ∈ inputs t₅) →
            index (outputRef i) <
            length (outputs (lookupTx l₄ (outputRef i) (v₀‴ i i∈)))
    v₁‴ = toWitness {Q = validOutputIndices? t₅ l₄ v₀‴} tt

    v₂‴ : ∀ i → i ∈ inputs t₅ → outputRef i ∈ₒ unspentOutputs l₄
    v₂‴ = toWitness {Q = validOutputRefs? t₅ l₄} tt

    v₃‴ : ∀ i → (i∈ : i ∈ inputs t₅) →
      D i ≡ Data (lookupOutput l₄ (outputRef i) (v₀‴ i i∈) (v₁‴ i i∈))
    v₃‴ = toWitness {Q = validDataScriptTypes? t₅ l₄ v₀‴ v₁‴} tt

    v₄‴ : ∀ i → (i∈ : i ∈ inputs t₅) →
      let out = lookupOutput l₄ (outputRef i) (v₀‴ i i∈) (v₁‴ i i∈)
          ptx = mkPendingTx l₄ t₅ v₀‴ v₁‴
      in T (runValidation ptx i out (v₃‴ i i∈) (getState l₄))
    v₄‴ = toWitness {Q = allInputsValidate? t₅ l₄ v₀‴ v₁‴ v₃‴} tt

    v₅‴ : ∀ i → (i∈ : i ∈ inputs t₅) →
      let out = lookupOutput l₄ (outputRef i) (v₀‴ i i∈) (v₁‴ i i∈)
      in (addresses ‼ address out) ≡ validator i ♯
    -- v₅‴ = toWitness {Q = validateValidHashes? t₅ l₄ v₀‴ v₁‴} tt
    v₅‴ _ (here refl)         rewrite validator♯₂₀ = refl
    v₅‴ _ (there (here refl)) rewrite validator♯₄₀ = refl
    v₅‴ _ (there (there ()))

    ----------------------------------------------------------------------------

    l₅ : Ledger
    l₅ = t₅ ∷ t₄ ∷ t₃ ∷ t₂ ∷ t₁ ∷ c₄ ∷ c₁ ∷ []

    v₀⁗ : ∀ i → i ∈ inputs t₆ → Any (λ tx → tx ♯ ≡ id (outputRef i)) l₅
    v₀⁗ = toWitness {Q = validTxRefs? t₆ l₅} tt

    v₁⁗ : ∀ i → (i∈ : i ∈ inputs t₆) →
            index (outputRef i) < length (outputs (lookupTx l₅ (outputRef i) (v₀⁗ i i∈)))
    v₁⁗ = toWitness {Q = validOutputIndices? t₆ l₅ v₀⁗} tt

    v₂⁗ : ∀ i → i ∈ inputs t₆ → outputRef i ∈ₒ unspentOutputs l₅
    v₂⁗ = toWitness {Q = validOutputRefs? t₆ l₅} tt

    v₃⁗ : ∀ i → (i∈ : i ∈ inputs t₆) →
      D i ≡ Data (lookupOutput l₅ (outputRef i) (v₀⁗ i i∈) (v₁⁗ i i∈))
    v₃⁗ = toWitness {Q = validDataScriptTypes? t₆ l₅ v₀⁗ v₁⁗} tt

    v₄⁗ : ∀ i → (i∈ : i ∈ inputs t₆) →
      let out = lookupOutput l₅ (outputRef i) (v₀⁗ i i∈) (v₁⁗ i i∈)
          ptx = mkPendingTx l₅ t₆ v₀⁗ v₁⁗
      in T (runValidation ptx i out (v₃⁗ i i∈) (getState l₅))
    v₄⁗ = toWitness {Q = allInputsValidate? t₆ l₅ v₀⁗ v₁⁗ v₃⁗} tt

    v₅⁗ : ∀ i → (i∈ : i ∈ inputs t₆) →
      let out = lookupOutput l₅ (outputRef i) (v₀⁗ i i∈) (v₁⁗ i i∈)
      in (addresses ‼ address out) ≡ validator i ♯
    -- v₅⁗ = toWitness {Q = validateValidHashes? t₆ l₅ v₀⁗ v₁⁗} tt
    v₅⁗ _ (here refl)         rewrite validator♯₅₀ = refl
    v₅⁗ _ (there (here refl)) rewrite validator♯₅₁ = refl
    v₅⁗ _ (there (there ()))
