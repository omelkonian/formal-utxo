{-# OPTIONS --rewriting #-}
{- NB: We use REWRITE rules to help normalization containing calls to the hash
       function _♯, which otherwise would not normalize. -}

module Example.Setup where

open import Level         using (0ℓ) renaming (suc to lsuc) public
open import Function      using (case_of_) public
open import Data.Unit     using (⊤; tt) public
open import Data.Empty    using (⊥; ⊥-elim) public
open import Data.Product  using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax) public
open import Data.Bool     using (Bool; true; false; T; _∧_; _∨_) public
open import Data.Nat      using (ℕ; zero; suc; _+_; _<_; _≟_; s≤s; z≤n; _≡ᵇ_) public
open import Data.Nat.Properties using (≤-refl) public
open import Data.List     using (List; []; _∷_; _∷ʳ_; [_]; _++_; length; upTo; sum; map) public
open import Data.Fin      using (Fin; toℕ; fromℕ≤) public
  renaming (zero to 0ᶠ; suc to sucᶠ)
open import Data.List.Any using (Any; here; there) public

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; setoid; refl; cong; sym) public
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎) public

open import Relation.Nullary           using (¬_; yes; no) public
open import Relation.Nullary.Negation  using (¬?) public
open import Relation.Nullary.Decidable using (True; False; toWitness) public

open import Utilities.Lists public
open import UTxO.Types hiding ($) public
open import Hashing.Types public
open import Hashing.MetaHash public
open SETₒ using (_∈?_; from↔to; list; noDuplicates; noDuplicates?) public
  renaming (_∈′_ to _∈ₒ_)
open import Data.List.Membership.Propositional using (_∈_; mapWith∈) public

-- available addresses
addresses : List Address
addresses = 111  -- first address
          ∷ 222  -- second address
          ∷ 333  -- third address
          ∷ 1234 -- ADA identifier
          ∷ []

open import UTxO.Validity          addresses public
open import UTxO.DecisionProcedure addresses public

1ᶠ : Fin 4
1ᶠ = sucᶠ 0ᶠ
2ᶠ : Fin 4
2ᶠ = sucᶠ (sucᶠ 0ᶠ)
3ᶠ : Fin 4
3ᶠ = sucᶠ (sucᶠ (sucᶠ 0ᶠ))

-- setup scripts and hash postulates
adaValidator : State → Value → PendingTx → (ℕ × ℕ) → ℕ → Bool
adaValidator (record {height = h}) _ _ _ _ = (h ≡ᵇ 2) ∨ (h ≡ᵇ 5)

dummyValidator : State → Value → PendingTx → (ℕ × ℕ) → ℕ → Bool
dummyValidator _ _ _ _ _ = true

mkValidator : TxOutputRef → (State → Value → PendingTx → (ℕ × ℕ) → ℕ → Bool)
mkValidator tin _ _ _ tin′ _ = (id tin ≡ᵇ proj₁ tin′) ∧ (index tin ≡ᵇ proj₂ tin′)

-- smart constructors
withScripts : TxOutputRef → TxInput
withScripts tin = record { outputRef = tin
                        ; redeemer  = λ _ → id tin , index tin
                        ; validator = mkValidator tin
                        }

withAda : TxOutputRef → TxInput
withAda tin = record { outputRef = tin
                    ; redeemer  = λ _ → id tin , index tin
                    ; validator = adaValidator
                    }

$ : ℕ → Value
$ v = [ (1234 , v) ]

$0 : Value
$0 = []

_at_ : Value → Index addresses → TxOutput
v at addr = record { value      = v
                    ; address    = addr
                    ; dataScript = λ _ → 0
                    }

-- define transactions
c₁ : Tx
c₁ = record { inputs  = []
            ; outputs = [ $0 at 3ᶠ ]
            ; forge   = $0
            ; fee     = $0
            }

c₁₀ : TxOutputRef
c₁₀ = (c₁ ♯ₜₓ) indexed-at 0

t₁ : Tx
t₁ = record { inputs  = [ withAda c₁₀ ]
            ; outputs = [ $ 1000 at 0ᶠ ]
            ; forge   = $ 1000
            ; fee     = $0
            }

out₁₀ : TxOutputRef
out₁₀ = (t₁ ♯ₜₓ) indexed-at 0

t₂ : Tx
t₂ = record { inputs  = [ withScripts out₁₀ ]
            ; outputs = $ 800 at 1ᶠ ∷ $ 200 at 0ᶠ ∷ []
            ; forge   = $0
            ; fee     = $0
            }

out₂₀ : TxOutputRef
out₂₀ = (t₂ ♯ₜₓ) indexed-at 0

out₂₁ : TxOutputRef
out₂₁ = (t₂ ♯ₜₓ) indexed-at 1

t₃ : Tx
t₃ = record { inputs  = [ withScripts out₂₁ ]
            ; outputs = [ $ 199 at 2ᶠ ]
            ; forge   = $0
            ; fee     = $ 1
            }

out₃₀ : TxOutputRef
out₃₀ = (t₃ ♯ₜₓ) indexed-at 0

c₄ : Tx
c₄ = record { inputs  = []
            ; outputs = [ $0 at 3ᶠ ]
            ; forge   = $0
            ; fee     = $0
            }

c₄₀ : TxOutputRef
c₄₀ = (c₄ ♯ₜₓ) indexed-at 0

t₄ : Tx
t₄ = record { inputs  = (withScripts out₃₀ ∷ withAda c₄₀ ∷ [])
            ; outputs = [ $ 207 at 1ᶠ ]
            ; forge   = $ 10
            ; fee     = $ 2
            }

out₄₀ : TxOutputRef
out₄₀ = (t₄ ♯ₜₓ) indexed-at 0

t₅ : Tx
t₅ = record { inputs  = withScripts out₂₀ ∷ withScripts out₄₀ ∷ []
            ; outputs = $ 500 at 1ᶠ ∷ $ 500 at 2ᶠ ∷ []
            ; forge   = $0
            ; fee     = $ 7
            }

out₅₀ : TxOutputRef
out₅₀ = (t₅ ♯ₜₓ) indexed-at 0

out₅₁ : TxOutputRef
out₅₁ = (t₅ ♯ₜₓ) indexed-at 1


t₆ : Tx
t₆ = record { inputs  = withScripts out₅₀ ∷ withScripts out₅₁ ∷ []
            ; outputs = [ $ 999 at 2ᶠ ]
            ; forge   = $0
            ; fee     = $ 1
            }

out₆₀ : TxOutputRef
out₆₀ = (t₆ ♯ₜₓ) indexed-at 0

-- hash postulates + rewriting
postulate
  adaValidator♯  : adaValidator ♯ ≡ 1234
  validator♯₁₀   : (mkValidator out₁₀) ♯ ≡ 111
  validator♯₂₀   : (mkValidator out₂₀) ♯ ≡ 222
  validator♯₂₁   : (mkValidator out₂₁) ♯ ≡ 111
  validator♯₃₀   : (mkValidator out₃₀) ♯ ≡ 333
  validator♯₄₀   : (mkValidator out₄₀) ♯ ≡ 222
  validator♯₅₀   : (mkValidator out₅₀) ♯ ≡ 222
  validator♯₅₁   : (mkValidator out₅₁) ♯ ≡ 333
  validator♯₆₀   : (mkValidator out₆₀) ♯ ≡ 333

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE adaValidator♯ #-}
{-# REWRITE validator♯₁₀ #-}
{-# REWRITE validator♯₂₀ #-}
{-# REWRITE validator♯₂₁ #-}
{-# REWRITE validator♯₃₀ #-}
{-# REWRITE validator♯₄₀ #-}
{-# REWRITE validator♯₅₀ #-}
{-# REWRITE validator♯₅₁ #-}
{-# REWRITE validator♯₆₀ #-}
