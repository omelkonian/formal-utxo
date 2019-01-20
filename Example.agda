------------------------------------------------------------------------
-- UTxO examples.
------------------------------------------------------------------------

module Example where

open import Data.Unit     using (⊤; tt)
open import Data.Bool     using (Bool; true; false)
open import Data.Nat      using (ℕ; zero; suc; _+_; _<_; _≟_)
open import Data.List     using (List; []; _∷_; _∷ʳ_; [_]; _++_; length; upTo)
open import Data.Fin      using (Fin)
  renaming (zero to 0ᶠ; suc to sucᶠ)
open import Data.List.Any using (Any; here; there)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Utilities.Lists
open import Basic

module Examples where
  addresses : List Address
  addresses = 1 ∷ 2 ∷ 3 ∷ []

  open import UTxO addresses

  1ᶠ : Fin 3
  1ᶠ = sucᶠ 0ᶠ

  2ᶠ : Fin 3
  2ᶠ = sucᶠ (sucᶠ 0ᶠ)

  t₁ : Tx
  t₁ = record { inputs  = []
              ; outputs = [ $ 1000 at 0ᶠ ]
              ; forge   = $ 1000
              ; fee     = $ 0
              }

  t₂ : Tx
  t₂ = record { inputs  = [ record { outputRef = (t₁ ♯) indexed-at 0
                                   ; redeemer  = λ _ → 0
                                   ; validator = λ _ _ → true
                                   } ]
              ; outputs = $ 800 at 1ᶠ ∷ $ 200 at 0ᶠ ∷ []
              ; forge   = $ 0
              ; fee     = $ 0
              }

  t₃ : Tx
  t₃ = record { inputs  = [ record { outputRef = (t₂ ♯) indexed-at 1
                                   ; redeemer  = λ _ → 0
                                   ; validator = λ _ _ → true
                                   } ]
              ; outputs = [ $ 100 at 2ᶠ ]
              ; forge   = $ 0
              ; fee     = $ 1
              }

  t₄ : Tx
  t₄ = record { inputs  = [ record { outputRef = (t₃ ♯) indexed-at 0
                                   ; redeemer  = λ _ → 0
                                   ; validator = λ _ _ → true
                                   } ]
              ; outputs = [ $ 207 at 1ᶠ ]
              ; forge   = $ 10
              ; fee     = $ 2
              }

  t₅ : Tx
  t₅ = record { inputs  = record { outputRef = (t₄ ♯) indexed-at 0
                                  ; redeemer  = λ _ → 0
                                  ; validator = λ _ _ → true
                                  }
                          ∷ record { outputRef = (t₂ ♯) indexed-at 0
                                   ; redeemer  = λ _ → 0
                                   ; validator = λ _ _ → true
                                   }
                          ∷ []
              ; outputs = $ 500 at 1ᶠ ∷ $ 500 at 2ᶠ ∷ []
              ; forge   = $ 0
              ; fee     = $ 7
              }

  t₆ : Tx
  t₆ = record { inputs  = record { outputRef = (t₅ ♯) indexed-at 0
                                 ; redeemer  = λ _ → 0
                                 ; validator = λ _ _ → true
                                 }
                          ∷ record { outputRef = (t₅ ♯) indexed-at 1
                                   ; redeemer  = λ _ → 0
                                   ; validator = λ _ _ → true
                                   }
                          ∷ []
              ; outputs = [ $ 999 at 2ᶠ ]
              ; forge   = $ 0
              ; fee     = $ 1
              }


  ex-ledger : Ledger
  ex-ledger =
    ∙ t₁ ∶- record
              { validTxRefs         = λ i ()
              ; validOutputIndices  = λ i ()
              ; validOutputRefs     = λ i ()
              ; preservesValues     = refl
              ; noDoubleSpending    = refl
              ; allInputsValidate   = λ i ()
              ; validateValidHashes = λ i ()
              }
    ⊕ t₂ ∶- record
              { validTxRefs         = λ{ i (here refl) → here refl
                                       ; i (there ()) }
              ; validOutputIndices  = λ{ i (here refl) → {!!}
                                       ; i (there ()) }
              ; validOutputRefs     = λ{ i (here refl) → {!!}
                                       ; i (there ()) }
              ; preservesValues     = {!!}
              ; noDoubleSpending    = refl
              ; allInputsValidate   = λ{ i (here refl) stᵣ stᵥ stᵣ≈stᵥ → tt
                                       ; i (there ()) }
              ; validateValidHashes = λ{ i (here refl) → {!!}
                                       ; i (there ()) }
              }
    ⊕ t₃ ∶- {!!}
    ⊕ t₄ ∶- {!!}
    ⊕ t₅ ∶- {!!}
    ⊕ t₆ ∶- {!!}
