module StateMachine.Counter where

open import StateMachine.Base
open import UTxO.Value
open import UTxO.Types
open import UTxO.TxUtilities
open import UTxO.Validity
open import Prelude.Default

open import Data.Integer using (_<_;_≥_;_≤_;ℤ;+_;+≤+)
open import Data.Integer.Properties using ()
open import Data.Nat.Properties
open import Data.Nat using (z≤n;s≤s;suc)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.Product
open import Function
open import Data.Bool using (true;false;T)
open import Data.Bool.Properties using () renaming (_≟_ to _≟B_)
open import Data.Sum
--open import Data.Unit
--open import Data.Empty


data CounterState : Set where
  counter : ℤ → CounterState

data CounterInput : Set where
  inc : CounterInput

instance
  IsData-CS : IsData CounterState
  toData   ⦃ IsData-CS ⦄ (counter i) = I i
  fromData ⦃ IsData-CS ⦄ (I i) = just (counter i)
  fromData ⦃ IsData-CS ⦄ _     = nothing
  from∘to  ⦃ IsData-CS ⦄ (counter i) = refl
  from-inj ⦃ IsData-CS ⦄ (I i) (counter .i) refl = refl

  IsData-CI : IsData CounterInput
  toData   ⦃ IsData-CI ⦄ inc = LIST []
  fromData ⦃ IsData-CI ⦄ (LIST []) = just inc
  fromData ⦃ IsData-CI ⦄ _         = nothing
  from∘to  ⦃ IsData-CI ⦄ inc = refl
  from-inj ⦃ IsData-CI ⦄ (LIST []) inc refl = refl
  
CounterSM : StateMachine CounterState CounterInput
isInitial CounterSM (counter (+ 0) ) = true
isInitial CounterSM (counter _     ) = false
-- isFinal   CounterSM (counter (+ 10)) = false
isFinal   CounterSM (counter _     ) = false
step      CounterSM (counter i) inc =
  just (counter (Data.Integer.suc i) , def Default-TxConstraints)
origin    CounterSM = nothing -- this will probably break initiality

Valid : CounterState → Set
Valid s@(counter i)     =
  T (isInitial CounterSM s) ⊎ i ≥ (+ 0) -- ⊎ T (isFinal CounterSM s)

_—→[_]_ : CounterState → CounterInput → (CounterState × TxConstraints) → Set
s —→[ i ] (s′ , tx≡) =
  Σ TxConstraints λ tx → step CounterSM s i ≡ just (s′ , tx≡)

-- step preserves validity
lemma-step : ∀{s s' : CounterState}{i : CounterInput}{tc : TxConstraints} → s —→[ i ] (s' , tc) → Valid s → Valid s'
lemma-step {counter (+ 0)}       {i = inc} (_ , refl) (inj₁ p) = inj₂ (+≤+ z≤n)
lemma-step {counter (+ (suc n))} {i = inc} (_ , refl) (inj₁ ())
lemma-step {counter (+_ n)} {i = inc} (_ , refl) (inj₂ p) = inj₂ (+≤+ z≤n)

-- initial state is valid
lemma-initial : ∀{s} → T (isInitial CounterSM s) → Valid s
lemma-initial {counter (+ 0)} _ = inj₁ _
