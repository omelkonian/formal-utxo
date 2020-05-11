{-# OPTIONS --rewriting #-}
{- NB: We use REWRITE rules to help normalization of calls to the postulated hash function _♯. -}

module UTxO.ExampleLedger where

open import Agda.Builtin.Equality.Rewrite

open import Data.Product  using (_,_)
open import Data.Bool     using (Bool; true; false; _∧_; _∨_)
open import Data.Nat      using (ℕ; _≟_; _≡ᵇ_)
open import Data.List     using (List; []; [_]; _∷_)
open import Data.Integer  using (ℤ)
open import Data.Maybe    using (just)

open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Prelude.Default

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types
open import UTxO.Validity

open import UTxO.Defaults

1ᵃ : Address
1ᵃ = 111 -- first address

2ᵃ : Address
2ᵃ = 222 -- second address

3ᵃ : Address
3ᵃ = 333 -- third address

adaᵃ : Address
adaᵃ = 1234 -- ADA identifier

adaPolicy : PendingMPS → Bool
adaPolicy (record {txInfo = record {range = r}}) = ⌊ r ≟ˢ (t= 0 ⋯ t= 0) ⌋ ∨ ⌊ r ≟ˢ (t= 3 ⋯ t= 3) ⌋

dummyValidator : PendingTx → DATA → DATA → Bool
dummyValidator _ _ _ = true

mkValidator : TxOutputRef → (PendingTx → DATA → DATA → Bool)
mkValidator tin _ (LIST (I (ℤ.pos n) ∷ I (ℤ.pos n') ∷ [])) _ = (id tin ≡ᵇ n) ∧ (index tin ≡ᵇ n')
mkValidator tin _ _ _                                        = false

-- smart constructors
withScripts : TxOutputRef → TxInput
withScripts tin = record { outputRef = tin
                         ; redeemer  = LIST (I (ℤ.pos (id tin)) ∷ (I (ℤ.pos (index tin)) ∷ []))
                                       {- λ _ → id tin , index tin -}
                         ; validator = mkValidator tin
                         ; datum     = def
                         }

$ : ℕ → Value
$ v = [ (adaᵃ , [ 0 , v ]) ]

_at_ : Value → Address → TxOutput
v at addr = record { value    = v
                   ; address  = addr
                   ; datumHash = def ♯ᵈ
                   }

-- define transactions

t₁ : Tx
t₁ = record def
  { outputs  = [ $ 1000 at 1ᵃ ]
  ; forge    = $ 1000
  ; policies = [ adaPolicy ]
  ; range    = t= 0 ⋯ t= 0
  ; datumWitnesses = [ def ♯ᵈ , def ] }
t₁₀ = (t₁ ♯ₜₓ) indexed-at 0

t₂ : Tx
t₂ = record def
  { inputs   = [ withScripts t₁₀ ]
  ; outputs  = $ 800 at 2ᵃ ∷ $ 200 at 1ᵃ ∷ []
  ; datumWitnesses = [ def ♯ᵈ , def ] }
t₂₀ = (t₂ ♯ₜₓ) indexed-at 0
t₂₁ = (t₂ ♯ₜₓ) indexed-at 1

t₃ : Tx
t₃ = record def
  { inputs   = [ withScripts t₂₁ ]
  ; outputs  = [ $ 200 at 3ᵃ ]
  ; datumWitnesses = [ def ♯ᵈ , def ] }
t₃₀ = (t₃ ♯ₜₓ) indexed-at 0

t₄ : Tx
t₄ = record
  { inputs   = [ withScripts t₃₀ ]
  ; outputs  = [ $ 210 at 2ᵃ ]
  ; forge    = $ 10
  ; policies = [ adaPolicy ]
  ; range    = t= 3 ⋯ t= 3
  ; datumWitnesses = [ def ♯ᵈ , def ] }
t₄₀ = (t₄ ♯ₜₓ) indexed-at 0

t₅ : Tx
t₅ = record def
  { inputs   = withScripts t₂₀ ∷ withScripts t₄₀ ∷ []
  ; outputs  = $ 505 at 2ᵃ ∷ $ 505 at 3ᵃ ∷ []
  ; datumWitnesses = [ def ♯ᵈ , def ] }
t₅₀ = (t₅ ♯ₜₓ) indexed-at 0
t₅₁ = (t₅ ♯ₜₓ) indexed-at 1

t₆ : Tx
t₆ = record def
  { inputs   = withScripts t₅₀ ∷ withScripts t₅₁ ∷ []
  ; outputs  = [ $ 1010 at 3ᵃ ]
  ; datumWitnesses = [ def ♯ᵈ , def ] }
t₆₀ = (t₆ ♯ₜₓ) indexed-at 0

-- hash postulates + rewriting
postulate
  adaValidator♯ : adaPolicy ♯         ≡ adaᵃ
  validator♯₁₀  : (mkValidator t₁₀) ♯ ≡ 1ᵃ
  validator♯₂₀  : (mkValidator t₂₀) ♯ ≡ 2ᵃ
  validator♯₂₁  : (mkValidator t₂₁) ♯ ≡ 1ᵃ
  validator♯₃₀  : (mkValidator t₃₀) ♯ ≡ 3ᵃ
  validator♯₄₀  : (mkValidator t₄₀) ♯ ≡ 2ᵃ
  validator♯₅₀  : (mkValidator t₅₀) ♯ ≡ 2ᵃ
  validator♯₅₁  : (mkValidator t₅₁) ♯ ≡ 3ᵃ
  validator♯₆₀  : (mkValidator t₆₀) ♯ ≡ 3ᵃ

{-# REWRITE adaValidator♯ #-}
{-# REWRITE validator♯₁₀  #-}
{-# REWRITE validator♯₂₀  #-}
{-# REWRITE validator♯₂₁  #-}
{-# REWRITE validator♯₃₀  #-}
{-# REWRITE validator♯₄₀  #-}
{-# REWRITE validator♯₅₀  #-}
{-# REWRITE validator♯₅₁  #-}
{-# REWRITE validator♯₆₀  #-}

ex-ledger : ValidLedger (t₆ ∷ t₅ ∷ t₄ ∷ t₃ ∷ t₂ ∷ t₁ ∷ [])
ex-ledger = ∙ ⊕ t₁ ⊕ t₂ ⊕ t₃ ⊕ t₄ ⊕ t₅ ⊕ t₆
