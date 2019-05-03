{-# OPTIONS --rewriting #-}
{- NB: We use REWRITE rules to help normalization containing calls to the hash
       function _♯, which otherwise would not normalize. -}

module Example.Setup where

open import Data.Unit     using (tt) public
open import Data.Product  using (_×_; _,_; proj₁; proj₂) public
open import Data.Bool     using (Bool; true; _∧_; _∨_) public
open import Data.Nat      using (ℕ; _≟_; _≡ᵇ_) public
open import Data.List     using (List; []; [_]) public

open import Relation.Binary.PropositionalEquality using (_≡_; refl) public
open import Relation.Nullary.Decidable            using (toWitness) public

open import UTxO.Types hiding ($) public
open import Hashing.Base public
open import Hashing.Types public
open import Hashing.MetaHash public
open SETₒ using (_∈?_; from↔to; list; noDuplicates; noDuplicates?) public
  renaming (_∈′_ to _∈ₒ_)
open import Data.List.Membership.Propositional using (_∈_; mapWith∈) public

-- available addresses

Address = ℕ

open import UTxO.Validity          Address (λ x → x) _≟_ public
open import UTxO.DecisionProcedure Address (λ x → x) _≟_ public

1ᵃ : Address
1ᵃ = 111 -- first address

2ᵃ : Address
2ᵃ = 222 -- second address

3ᵃ : Address
3ᵃ = 333 -- third address

adaᵃ : Address
adaᵃ = 1234 -- ADA identifier

-- setup scripts and hash postulates
adaValidator : State → Value → PendingTx → (ℕ × ℕ) → ℕ → Bool
adaValidator (record {height = h}) _ _ _ _ = (h ≡ᵇ 1) ∨ (h ≡ᵇ 4)

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
$ v = [ (adaᵃ , v) ]

$0 : Value
$0 = []

_at_ : Value → Address → TxOutput
v at addr = record { value      = v
                   ; address    = addr
                   ; dataScript = λ _ → 0
                   }

-- define transactions
c₁ : Tx
c₁ = record { inputs  = []
            ; outputs = $0 at adaᵃ ∷ $0 at adaᵃ ∷ []
            ; forge   = $0
            ; fee     = $0
            }

c₁₀ : TxOutputRef
c₁₀ = (c₁ ♯ₜₓ) indexed-at 0

c₁₁ : TxOutputRef
c₁₁ = (c₁ ♯ₜₓ) indexed-at 1

t₁ : Tx
t₁ = record { inputs  = [ withAda c₁₀ ]
            ; outputs = [ $ 1000 at 1ᵃ ]
            ; forge   = $ 1000
            ; fee     = $0
            }

t₁₀ : TxOutputRef
t₁₀ = (t₁ ♯ₜₓ) indexed-at 0

t₂ : Tx
t₂ = record { inputs  = [ withScripts t₁₀ ]
            ; outputs = $ 800 at 2ᵃ ∷ $ 200 at 1ᵃ ∷ []
            ; forge   = $0
            ; fee     = $0
            }

t₂₀ : TxOutputRef
t₂₀ = (t₂ ♯ₜₓ) indexed-at 0

t₂₁ : TxOutputRef
t₂₁ = (t₂ ♯ₜₓ) indexed-at 1

t₃ : Tx
t₃ = record { inputs  = [ withScripts t₂₁ ]
            ; outputs = [ $ 199 at 3ᵃ ]
            ; forge   = $0
            ; fee     = $ 1
            }

t₃₀ : TxOutputRef
t₃₀ = (t₃ ♯ₜₓ) indexed-at 0

t₄ : Tx
t₄ = record { inputs  = (withScripts t₃₀ ∷ withAda c₁₁ ∷ [])
            ; outputs = [ $ 207 at 2ᵃ ]
            ; forge   = $ 10
            ; fee     = $ 2
            }

t₄₀ : TxOutputRef
t₄₀ = (t₄ ♯ₜₓ) indexed-at 0

t₅ : Tx
t₅ = record { inputs  = withScripts t₂₀ ∷ withScripts t₄₀ ∷ []
            ; outputs = $ 500 at 2ᵃ ∷ $ 500 at 3ᵃ ∷ []
            ; forge   = $0
            ; fee     = $ 7
            }

t₅₀ : TxOutputRef
t₅₀ = (t₅ ♯ₜₓ) indexed-at 0

t₅₁ : TxOutputRef
t₅₁ = (t₅ ♯ₜₓ) indexed-at 1


t₆ : Tx
t₆ = record { inputs  = withScripts t₅₀ ∷ withScripts t₅₁ ∷ []
            ; outputs = [ $ 999 at 3ᵃ ]
            ; forge   = $0
            ; fee     = $ 1
            }

t₆₀ : TxOutputRef
t₆₀ = (t₆ ♯ₜₓ) indexed-at 0

-- hash postulates + rewriting
postulate
  adaValidator♯  : adaValidator ♯        ≡ adaᵃ
  validator♯₁₀   : (mkValidator t₁₀) ♯ ≡ 1ᵃ
  validator♯₂₀   : (mkValidator t₂₀) ♯ ≡ 2ᵃ
  validator♯₂₁   : (mkValidator t₂₁) ♯ ≡ 1ᵃ
  validator♯₃₀   : (mkValidator t₃₀) ♯ ≡ 3ᵃ
  validator♯₄₀   : (mkValidator t₄₀) ♯ ≡ 2ᵃ
  validator♯₅₀   : (mkValidator t₅₀) ♯ ≡ 2ᵃ
  validator♯₅₁   : (mkValidator t₅₁) ♯ ≡ 3ᵃ
  validator♯₆₀   : (mkValidator t₆₀) ♯ ≡ 3ᵃ

{-# BUILTIN REWRITE _≡_   #-}
{-# REWRITE adaValidator♯ #-}
{-# REWRITE validator♯₁₀  #-}
{-# REWRITE validator♯₂₀  #-}
{-# REWRITE validator♯₂₁  #-}
{-# REWRITE validator♯₃₀  #-}
{-# REWRITE validator♯₄₀  #-}
{-# REWRITE validator♯₅₀  #-}
{-# REWRITE validator♯₅₁  #-}
{-# REWRITE validator♯₆₀  #-}