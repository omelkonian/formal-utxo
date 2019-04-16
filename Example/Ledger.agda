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
                { validTxRefs          = vtr₀
                ; validOutputIndices   = voi₀
                ; validOutputRefs      = toWitness {Q = validOutputRefs? t₁ l₀} tt
                ; validDataScriptTypes = vds₀
                ; preservesValues      = refl
                ; noDoubleSpending     = tt
                ; allInputsValidate    = toWitness {Q = allInputsValidate? t₁ l₀ vtr₀ voi₀ vds₀} tt
                ; validateValidHashes  = toWitness {Q = validateValidHashes? t₁ l₀ vtr₀ voi₀} tt
                ; forging              = toWitness {Q = forging? t₁ l₀ vtr₀ voi₀} tt
                }
    ⊕ t₂ ∶- record
                { validTxRefs          = vtr₁
                ; validOutputIndices   = voi₁
                ; validOutputRefs      = toWitness {Q = validOutputRefs? t₂ l₁} tt
                ; validDataScriptTypes = vds₁
                ; preservesValues      = refl
                ; noDoubleSpending     = tt
                ; allInputsValidate    = toWitness {Q = allInputsValidate? t₂ l₁ vtr₁ voi₁ vds₁} tt
                ; validateValidHashes  = toWitness {Q = validateValidHashes? t₂ l₁ vtr₁ voi₁} tt
                ; forging              = λ _ ()
                }
    ⊕ t₃ ∶- record
                { validTxRefs          = vtr₂
                ; validOutputIndices   = voi₂
                ; validOutputRefs      = toWitness {Q = validOutputRefs? t₃ l₂} tt
                ; validDataScriptTypes = vds₂
                ; preservesValues      = refl
                ; noDoubleSpending     = tt
                ; allInputsValidate    = toWitness {Q = allInputsValidate? t₃ l₂ vtr₂ voi₂ vds₂} tt
                ; validateValidHashes  = toWitness {Q = validateValidHashes? t₃ l₂ vtr₂ voi₂} tt
                ; forging              = λ _ ()
                }
    ⊕ t₄ ∶- record
                { validTxRefs          = vtr₃
                ; validOutputIndices   = voi₃
                ; validOutputRefs      = toWitness {Q = validOutputRefs? t₄ l₃} {!!}
                ; validDataScriptTypes = vds₃
                ; preservesValues      = refl
                ; noDoubleSpending     = tt
                ; allInputsValidate    = toWitness {Q = allInputsValidate? t₄ l₃ vtr₃ voi₃ vds₃} tt
                ; validateValidHashes  = toWitness {Q = validateValidHashes? t₄ l₃ vtr₃ voi₃} tt
                ; forging              = toWitness {Q = forging? t₄ l₃ vtr₃ voi₃} tt
                }
    ⊕ t₅ ∶- record
                { validTxRefs          = vtr₄
                ; validOutputIndices   = voi₄
                ; validOutputRefs      = toWitness {Q = validOutputRefs? t₅ l₄} tt
                ; validDataScriptTypes = vds₄
                ; preservesValues      = refl
                ; noDoubleSpending     = tt
                ; allInputsValidate    = toWitness {Q = allInputsValidate? t₅ l₄ vtr₄ voi₄ vds₄} tt
                ; validateValidHashes  = toWitness {Q = validateValidHashes? t₅ l₄ vtr₄ voi₄} tt
                ; forging              = λ _ ()
                }
    ⊕ t₆ ∶- record
                { validTxRefs          = vtr₅
                ; validOutputIndices   = voi₅
                ; validOutputRefs      = toWitness {Q = validOutputRefs? t₆ l₅} tt
                ; validDataScriptTypes = vds₅
                ; preservesValues      = refl
                ; noDoubleSpending     = tt
                ; allInputsValidate    = toWitness {Q = allInputsValidate? t₆ l₅ vtr₅ voi₅ vds₅} tt
                ; validateValidHashes  = toWitness {Q = validateValidHashes? t₆ l₅ vtr₅ voi₅} tt
                ; forging              = λ _ ()
                }

   where

    ----------------------------------------------------------------------------

    l₀ = c₄ ∷ c₁ ∷ []
    vtr₀ = toWitness {Q = validTxRefs? t₁ l₀} tt
    voi₀ = toWitness {Q = validOutputIndices? t₁ l₀ vtr₀} tt
    vds₀ = toWitness {Q = validDataScriptTypes? t₁ l₀ vtr₀ voi₀} tt

    l₁ = t₁ ∷ c₄ ∷ c₁ ∷ []
    vtr₁ = toWitness {Q = validTxRefs? t₂ l₁} tt
    voi₁ = toWitness {Q = validOutputIndices? t₂ l₁ vtr₁} tt
    vds₁ = toWitness {Q = validDataScriptTypes? t₂ l₁ vtr₁ voi₁} tt

    l₂ = t₂ ∷ t₁ ∷ c₄ ∷ c₁ ∷ []
    vtr₂ = toWitness {Q = validTxRefs? t₃ l₂} tt
    voi₂ = toWitness {Q = validOutputIndices? t₃ l₂ vtr₂} tt
    vds₂ = toWitness {Q = validDataScriptTypes? t₃ l₂ vtr₂ voi₂} tt

    l₃ = t₃ ∷ t₂ ∷ t₁ ∷ c₄ ∷ c₁ ∷ []
    vtr₃ = toWitness {Q = validTxRefs? t₄ l₃} tt
    voi₃ = toWitness {Q = validOutputIndices? t₄ l₃ vtr₃} tt
    vds₃ = toWitness {Q = validDataScriptTypes? t₄ l₃ vtr₃ voi₃} tt

    l₄ = t₄ ∷ t₃ ∷ t₂ ∷ t₁ ∷ c₄ ∷ c₁ ∷ []
    vtr₄ = toWitness {Q = validTxRefs? t₅ l₄} tt
    voi₄ = toWitness {Q = validOutputIndices? t₅ l₄ vtr₄} tt
    vds₄ = toWitness {Q = validDataScriptTypes? t₅ l₄ vtr₄ voi₄} tt

    l₅ = t₅ ∷ t₄ ∷ t₃ ∷ t₂ ∷ t₁ ∷ c₄ ∷ c₁ ∷ []
    vtr₅ = toWitness {Q = validTxRefs? t₆ l₅} tt
    voi₅ = toWitness {Q = validOutputIndices? t₆ l₅ vtr₅} tt
    vds₅ = toWitness {Q = validDataScriptTypes? t₆ l₅ vtr₅ voi₅} tt
