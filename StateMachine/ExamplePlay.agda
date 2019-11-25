{-# OPTIONS --rewriting #-}
{- NB: We use REWRITE rules to help normalization of calls to the postulated hash function _♯. -}

module StateMachine.ExamplePlay where

open import Data.Product  using (_×_; _,_; proj₁)
open import Data.Bool     using (Bool; true; _∧_)
open import Data.Nat      using (ℕ)
  renaming (_≟_ to _≟ℕ_)
open import Data.List     using (List; []; [_]; _∷_; reverse)
open import Data.Integer  using (ℤ)
open import Data.Maybe    using (just; is-just)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Hashing.MetaHash
open import UTxO.Types

open import StateMachine.Base hiding (mkValidator)
open import StateMachine.GuessingGame

-- available addresses
Address = ℕ

open import UTxO.Ledger            Address (λ x → x) _≟ℕ_
open import UTxO.Hashing.Tx        Address (λ x → x) _≟ℕ_
open import UTxO.Validity          Address (λ x → x) _≟ℕ_
open import UTxO.DecisionProcedure Address (λ x → x) _≟ℕ_

_at_←—_ : Tx → ℕ → GameInput → TxInput
outputRef (t at i ←— _) = (t ♯ₜₓ) indexed-at i
redeemer  (_ at _ ←— d) = toData IsDataᵍⁱ d
validator (_ at _ ←— _) = mkValidator

_—→_at_ : GameState → Value → Address → TxOutput
value   (_ —→ v at _) = v
address (_ —→ _ at a) = a
dataVal (d —→ _ at _) = toData IsDataᵍˢ d

-----------------------------------------------------------------------

-- dummy currency address, need a concrete number for decision procedure to compute
𝕍 = 3
postulate
  eq : mkValidator ♯ ≡ 𝕍
{-# REWRITE eq #-}

tn : TokenName
tn = "guess" ♯ₛₜᵣ

-----------------------------------------------------------------------

$ : ℕ → Value
$ v = [ 𝕍 , [ tn , v ] ]

-- define transactions
t₀ : Tx
inputs  t₀ = []
outputs t₀ = [ Initialised ("zero" ♯ₛₜᵣ) —→ $0 at 𝕍 ]
forge   t₀ = $0
fee     t₀ = $0

t₁ : Tx
inputs  t₁ = t₀ at 0 ←— ForgeToken tn
           ∷ []
outputs t₁ = [ Locked tn ("zero" ♯ₛₜᵣ) —→ $ 1 at 𝕍 ]
forge   t₁ = $ 1
fee     t₁ = $0

t₂ : Tx
inputs  t₂ =  [ t₁ at 0 ←— Guess "zero" ("one" ♯ₛₜᵣ) ]
outputs t₂ =  [ Locked tn ("one" ♯ₛₜᵣ) —→ $ 1 at 𝕍 ]
forge   t₂ = $0
fee     t₂ = $0

t₃ : Tx
inputs  t₃ =  [ t₂ at 0 ←— Guess "one" ("two" ♯ₛₜᵣ) ]
outputs t₃ =  [ Locked tn ("two" ♯ₛₜᵣ) —→ $ 1 at 𝕍 ]
forge   t₃ = $0
fee     t₃ = $0

ex-ledger : ValidLedger (t₃ ∷ t₂ ∷ t₁ ∷ t₀ ∷ [])
ex-ledger = ∙ ⊕ t₀ ⊕ t₁ ⊕ t₂ ⊕ t₃

-----------------------------------------------------------------------

infix  -2 begin_
infixr -1 _—→[_]_
infix  0 _∎

data GameTransition : Set where

  _∎ : GameState → GameTransition

  _—→[_]_ : GameState → GameInput → GameTransition → GameTransition

begin_ : GameTransition → GameTransition
begin_ x = x

ex-transition : GameTransition
ex-transition =
  begin
    Initialised ("zero" ♯ₛₜᵣ)
  —→[ ForgeToken tn ]
    Locked tn ("zero" ♯ₛₜᵣ)
  —→[ Guess "zero" ("one" ♯ₛₜᵣ) ]
    Locked tn ("one" ♯ₛₜᵣ)
  —→[ Guess "one" ("two" ♯ₛₜᵣ) ]
    Locked tn ("two" ♯ₛₜᵣ)
  ∎

view : GameTransition → GameState × List (GameInput × GameState)
view (s ∎)         = s , []
view (s —→[ i ] t) with view t
... | s′ , ls = s , ((i , s′) ∷ ls)

getForge : GameInput → Value
getForge (ForgeToken tn) = $ 1
getForge _               = $0

compile : GameTransition → Ledger
compile t with view t
... | s₀ , ts = reverse (tx₀ ∷ go (tx₀ , $0) ts)
  where
    tx₀ : Tx
    inputs  tx₀ = []
    outputs tx₀ = [ s₀ —→ $0 at 𝕍 ]
    forge   tx₀ = $0
    fee     tx₀ = $0

    go : Tx × Value → List (GameInput × GameState) → Ledger
    go _            []             = []
    go (prevTx , v) ((i , s) ∷ ts) = tx ∷ go (tx , v′) ts
      where
        v′ = v +ᶜ getForge i

        tx : Tx
        inputs  tx = [ prevTx at 0 ←— i ]
        outputs tx = [ s —→ v′ at 𝕍 ]
        forge   tx = getForge i
        fee     tx = $0

_ : compile ex-transition ≡ t₃ ∷ t₂ ∷ t₁ ∷ t₀ ∷ []
_ = refl
