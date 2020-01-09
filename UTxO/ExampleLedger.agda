{-# OPTIONS --rewriting #-}
{- NB: We use REWRITE rules to help normalization of calls to the postulated hash function _♯. -}

module UTxO.ExampleLedger where

open import Data.Product  using (_,_)
open import Data.Bool     using (Bool; true; false; _∧_)
open import Data.Nat      using (ℕ; _≟_; _≡ᵇ_)
open import Data.List     using (List; []; [_]; _∷_)
open import Data.Integer  using (ℤ)
open import Data.Maybe    using (just)

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Agda.Builtin.Equality.Rewrite
open import UTxO.Types
open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Hashing.MetaHash

-- available addresses
Address = ℕ

open import UTxO.Ledger      Address (λ x → x) _≟_
open import UTxO.Hashing.Tx  Address (λ x → x) _≟_
open import UTxO.Validity    Address (λ x → x) _≟_
open import UTxO.DecValidity Address (λ x → x) _≟_

1ᵃ : Address
1ᵃ = 111 -- first address

2ᵃ : Address
2ᵃ = 222 -- second address

3ᵃ : Address
3ᵃ = 333 -- third address

mkValidator : TxOutputRef → Validator
mkValidator tin _ (LIST (I (ℤ.pos n) ∷ I (ℤ.pos n') ∷ [])) _ = (id tin ≡ᵇ n) ∧ (index tin ≡ᵇ n')
mkValidator tin _ _ _                                        = false

-- smart constructors
withScripts : TxOutputRef → TxInput
withScripts tin = record { outputRef = tin
                         ; redeemer  = LIST (I (ℤ.pos (id tin)) ∷ (I (ℤ.pos (index tin)) ∷ []))
                                       {- λ _ → id tin , index tin -}
                         ; validator = mkValidator tin
                         }

_at_ : Value → Address → TxOutput
v at addr = record { value   = v
                   ; address = addr
                   ; dataVal = I (ℤ.pos 0)
                   }

-- define transactions
t₁ : Tx
inputs  t₁ = []
outputs t₁ = [ $ 1000 at 1ᵃ ]
forge   t₁ = $ 1000
fee     t₁ = $0
range   t₁ = t= 0 ⋯ t= 0

t₁₀ : TxOutputRef
t₁₀ = (t₁ ♯ₜₓ) indexed-at 0

t₂ : Tx
inputs  t₂ = [ withScripts t₁₀ ]
outputs t₂ = $ 800 at 2ᵃ ∷ $ 200 at 1ᵃ ∷ []
forge   t₂ = $0
fee     t₂ = $0
range   t₂ = -∞ ⋯ t= 1

t₂₀ : TxOutputRef
t₂₀ = (t₂ ♯ₜₓ) indexed-at 0

t₂₁ : TxOutputRef
t₂₁ = (t₂ ♯ₜₓ) indexed-at 1

t₃ : Tx
inputs  t₃ = [ withScripts t₂₁ ]
outputs t₃ = [ $ 199 at 3ᵃ ]
forge   t₃ = $0
fee     t₃ = $ 1
range   t₃ = -∞ ⋯ +∞

t₃₀ : TxOutputRef
t₃₀ = (t₃ ♯ₜₓ) indexed-at 0

t₄ : Tx
inputs  t₄ = withScripts t₃₀ ∷ []
outputs t₄ = [ $ 207 at 2ᵃ ]
forge   t₄ = $ 10
fee     t₄ = $ 2
range   t₄ = -∞ ⋯ +∞

t₄₀ : TxOutputRef
t₄₀ = (t₄ ♯ₜₓ) indexed-at 0

t₅ : Tx
inputs  t₅ = withScripts t₂₀ ∷ withScripts t₄₀ ∷ []
outputs t₅ = $ 500 at 2ᵃ ∷ $ 500 at 3ᵃ ∷ []
forge   t₅ = $0
fee     t₅ = $ 7
range   t₅ = -∞ ⋯ +∞

t₅₀ : TxOutputRef
t₅₀ = (t₅ ♯ₜₓ) indexed-at 0

t₅₁ : TxOutputRef
t₅₁ = (t₅ ♯ₜₓ) indexed-at 1

t₆ : Tx
inputs  t₆ = withScripts t₅₀ ∷ withScripts t₅₁ ∷ []
outputs t₆ = [ $ 999 at 3ᵃ ]
forge   t₆ = $0
fee     t₆ = $ 1
range   t₆ = -∞ ⋯ +∞

t₆₀ : TxOutputRef
t₆₀ = (t₆ ♯ₜₓ) indexed-at 0

-- hash postulates + rewriting
postulate
  validator♯₁₀  : (mkValidator t₁₀) ♯ ≡ 1ᵃ
  validator♯₂₀  : (mkValidator t₂₀) ♯ ≡ 2ᵃ
  validator♯₂₁  : (mkValidator t₂₁) ♯ ≡ 1ᵃ
  validator♯₃₀  : (mkValidator t₃₀) ♯ ≡ 3ᵃ
  validator♯₄₀  : (mkValidator t₄₀) ♯ ≡ 2ᵃ
  validator♯₅₀  : (mkValidator t₅₀) ♯ ≡ 2ᵃ
  validator♯₅₁  : (mkValidator t₅₁) ♯ ≡ 3ᵃ
  validator♯₆₀  : (mkValidator t₆₀) ♯ ≡ 3ᵃ

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