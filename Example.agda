------------------------------------------------------------------------
-- UTxO examples.
------------------------------------------------------------------------

open import Data.Nat  using (ℕ; zero; suc; _+_; _<_; _≟_)
open import Data.List using (List; []; _∷_; [_]; length; upTo)
open import Data.Fin  using (Fin)
  renaming (zero to 0ᶠ; suc to sucᶠ)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Utilities.Lists
open import Basic

addresses : List Address
addresses = 1 ∷ 2 ∷ 3 ∷ []

open import UTxO addresses

open SETᵢ using (_∈_; ∅; singleton; fromList)

1ᶠ : Fin 3
1ᶠ = sucᶠ 0ᶠ

2ᶠ : Fin 3
2ᶠ = sucᶠ (sucᶠ 0ᶠ)

t₁ : Tx
t₁ = record { inputs  = ∅
            ; outputs = [ $ 1000 at 0ᶠ ]
            ; forge   = $ 1000
            ; fee     = $ 0
            }

t₂ : Tx
t₂ = record { inputs  = singleton (record { outputRef = (t₁ ♯) indexed-at 0
                                          ; validator = "noop"
                                          ; redeemer  = "noop"
                                          })
            ; outputs = $ 800 at 1ᶠ ∷ $ 200 at 0ᶠ ∷ []
            ; forge   = $ 0
            ; fee     = $ 0
            }

t₃ : Tx
t₃ = record { inputs  = singleton (record { outputRef = (t₂ ♯) indexed-at 1
                                          ; validator = "noop"
                                          ; redeemer  = "noop"
                                          })
            ; outputs = [ $ 100 at 2ᶠ ]
            ; forge   = $ 0
            ; fee     = $ 1
            }

t₄ : Tx
t₄ = record { inputs  = singleton ( record { outputRef = (t₃ ♯) indexed-at 0
                                           ; validator = "noop"
                                           ; redeemer  = "noop"
                                           })
            ; outputs = [ $ 207 at 1ᶠ ]
            ; forge   = $ 10
            ; fee     = $ 2
            }

t₅ : Tx
t₅ = record { inputs  = fromList ( record { outputRef = (t₄ ♯) indexed-at 0
                                          ; validator = "noop"
                                          ; redeemer  = "noop"
                                          }
                                 ∷ record { outputRef = (t₂ ♯) indexed-at 0
                                          ; validator = "noop"
                                          ; redeemer  = "noop"
                                          }
                                 ∷ [])
            ; outputs = $ 500 at 1ᶠ ∷ $ 500 at 2ᶠ ∷ []
            ; forge   = $ 0
            ; fee     = $ 7
            }

t₆ : Tx
t₆ = record { inputs  = fromList ( record { outputRef = (t₅ ♯) indexed-at 0
                                          ; validator = "noop"
                                          ; redeemer  = "noop"
                                          }
                                 ∷ record { outputRef = (t₅ ♯) indexed-at 1
                                          ; validator = "noop"
                                          ; redeemer  = "noop"
                                          }
                                 ∷ [])
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
            { validTxRefs         = {!!}
            ; validOutputIndices  = {!!}
            ; validOutputRefs     = {!!}
            ; preservesValues     = {!!}
            ; noDoubleSpending    = {!!}
            ; allInputsValidate   = {!!}
            ; validateValidHashes = {!!}
            }
  ⊕ t₃ ∶- {!!}
  ⊕ t₄ ∶- {!!}
  ⊕ t₅ ∶- {!!}
  ⊕ t₆ ∶- {!!}
