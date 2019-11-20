{-# OPTIONS --rewriting #-}
module UTxO.Example.Ledger where

open import UTxO.Example.Setup

ex-ledger : ValidLedger (t₆ ∷ t₅ ∷ t₄ ∷ t₃ ∷ t₂ ∷ t₁ ∷ c₁ ∷ [])
ex-ledger =
    ∙
    ⊕ c₁ ∶- record
                { validTxRefs          = λ _ ()
                ; validOutputIndices   = λ _ ()
                ; validOutputRefs      = λ _ ()
                ; preservesValues      = refl
                ; noDoubleSpending     = toWitness {Q = noDoubleSpending? c₁ []} tt
                ; allInputsValidate    = λ _ ()
                ; validateValidHashes  = λ _ ()
                ; forging              = λ _ ()
                }
    ⊕ t₁ ∶- record
                { validTxRefs          = vtr₀
                ; validOutputIndices   = voi₀
                ; validOutputRefs      = toWitness {Q = validOutputRefs? t₁ l₀} tt
                ; preservesValues      = refl
                ; noDoubleSpending     = toWitness {Q = noDoubleSpending? t₁ l₀} tt
                ; allInputsValidate    = toWitness {Q = allInputsValidate? t₁ l₀ vtr₀ voi₀} tt
                ; validateValidHashes  = toWitness {Q = validateValidHashes? t₁ l₀ vtr₀ voi₀} tt
                ; forging              = toWitness {Q = forging? t₁ l₀ vtr₀ voi₀} tt
                }
    ⊕ t₂ ∶- record
                { validTxRefs          = vtr₁
                ; validOutputIndices   = voi₁
                ; validOutputRefs      = toWitness {Q = validOutputRefs? t₂ l₁} tt
                ; preservesValues      = refl
                ; noDoubleSpending     = toWitness {Q = noDoubleSpending? t₂ l₁} tt
                ; allInputsValidate    = toWitness {Q = allInputsValidate? t₂ l₁ vtr₁ voi₁} tt
                ; validateValidHashes  = toWitness {Q = validateValidHashes? t₂ l₁ vtr₁ voi₁} tt
                ; forging              = λ _ ()
                }
    ⊕ t₃ ∶- record
                { validTxRefs          = vtr₂
                ; validOutputIndices   = voi₂
                ; validOutputRefs      = toWitness {Q = validOutputRefs? t₃ l₂} tt
                ; preservesValues      = refl
                ; noDoubleSpending     = toWitness {Q = noDoubleSpending? t₃ l₂} tt
                ; allInputsValidate    = toWitness {Q = allInputsValidate? t₃ l₂ vtr₂ voi₂} tt
                ; validateValidHashes  = toWitness {Q = validateValidHashes? t₃ l₂ vtr₂ voi₂} tt
                ; forging              = λ _ ()
                }
    ⊕ t₄ ∶- record
                { validTxRefs          = vtr₃
                ; validOutputIndices   = voi₃
                ; validOutputRefs      = toWitness {Q = validOutputRefs? t₄ l₃} tt
                ; preservesValues      = refl
                ; noDoubleSpending     = toWitness {Q = noDoubleSpending? t₄ l₃} tt
                ; allInputsValidate    = toWitness {Q = allInputsValidate? t₄ l₃ vtr₃ voi₃} tt
                ; validateValidHashes  = toWitness {Q = validateValidHashes? t₄ l₃ vtr₃ voi₃} tt
                ; forging              = toWitness {Q = forging? t₄ l₃ vtr₃ voi₃} tt
                }
    ⊕ t₅ ∶- record
                { validTxRefs          = vtr₄
                ; validOutputIndices   = voi₄
                ; validOutputRefs      = toWitness {Q = validOutputRefs? t₅ l₄} tt
                ; preservesValues      = refl
                ; noDoubleSpending     = toWitness {Q = noDoubleSpending? t₅ l₄} tt
                ; allInputsValidate    = toWitness {Q = allInputsValidate? t₅ l₄ vtr₄ voi₄} tt
                ; validateValidHashes  = toWitness {Q = validateValidHashes? t₅ l₄ vtr₄ voi₄} tt
                ; forging              = λ _ ()
                }
    ⊕ t₆ ∶- record
                { validTxRefs          = vtr₅
                ; validOutputIndices   = voi₅
                ; validOutputRefs      = toWitness {Q = validOutputRefs? t₆ l₅} tt
                ; preservesValues      = refl
                ; noDoubleSpending     = toWitness {Q = noDoubleSpending? t₆ l₅} tt
                ; allInputsValidate    = toWitness {Q = allInputsValidate? t₆ l₅ vtr₅ voi₅} tt
                ; validateValidHashes  = toWitness {Q = validateValidHashes? t₆ l₅ vtr₅ voi₅} tt
                ; forging              = λ _ ()
                }
   where

    l₀ = c₁ ∷ []
    vtr₀ = toWitness {Q = validTxRefs? t₁ l₀} tt
    voi₀ = toWitness {Q = validOutputIndices? t₁ l₀ vtr₀} tt

    l₁ = t₁ ∷ c₁ ∷ []
    vtr₁ = toWitness {Q = validTxRefs? t₂ l₁} tt
    voi₁ = toWitness {Q = validOutputIndices? t₂ l₁ vtr₁} tt

    l₂ = t₂ ∷ t₁ ∷ c₁ ∷ []
    vtr₂ = toWitness {Q = validTxRefs? t₃ l₂} tt
    voi₂ = toWitness {Q = validOutputIndices? t₃ l₂ vtr₂} tt

    l₃ = t₃ ∷ t₂ ∷ t₁ ∷ c₁ ∷ []
    vtr₃ = toWitness {Q = validTxRefs? t₄ l₃} tt
    voi₃ = toWitness {Q = validOutputIndices? t₄ l₃ vtr₃} tt

    l₄ = t₄ ∷ t₃ ∷ t₂ ∷ t₁ ∷ c₁ ∷ []
    vtr₄ = toWitness {Q = validTxRefs? t₅ l₄} tt
    voi₄ = toWitness {Q = validOutputIndices? t₅ l₄ vtr₄} tt

    l₅ = t₅ ∷ t₄ ∷ t₃ ∷ t₂ ∷ t₁ ∷ c₁ ∷ []
    vtr₅ = toWitness {Q = validTxRefs? t₆ l₅} tt
    voi₅ = toWitness {Q = validOutputIndices? t₆ l₅ vtr₅} tt

    l₆ = t₆ ∷ t₅ ∷ t₄ ∷ t₃ ∷ t₂ ∷ t₁ ∷ c₁ ∷ []
    _ : list (unspentOutputs l₀) ≡ c₁₀ ∷ c₁₁ ∷ []
    _ = refl
    _ : list (unspentOutputs l₁) ≡ c₁₁ ∷ t₁₀ ∷ []
    _ = refl
    _ : list (unspentOutputs l₂) ≡ c₁₁ ∷ t₂₀ ∷ t₂₁ ∷ []
    _ = refl
    _ : list (unspentOutputs l₃) ≡ c₁₁ ∷ t₂₀ ∷ t₃₀ ∷ []
    _ = refl
    _ : list (unspentOutputs l₄) ≡ t₂₀ ∷ t₄₀ ∷ []
    _ = refl
    _ : list (unspentOutputs l₅) ≡ t₅₀ ∷ t₅₁ ∷ []
    _ = refl
    _ : list (unspentOutputs l₆) ≡ t₆₀ ∷ []
    _ = refl
