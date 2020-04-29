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
-- isFinal   CounterSM _ = false
step      CounterSM (counter i) inc =
  just (counter (Data.Integer.suc i) , def Default-TxConstraints)
origin    CounterSM = nothing

-- Some basic properties of this machine

Valid : CounterState → Set
Valid s@(counter i)     =
  T (isInitial CounterSM s) ⊎ i ≥ (+ 0) -- ⊎ T (isFinal CounterSM s)

_—→[_]_ : CounterState → CounterInput → CounterState → Set
s —→[ i ] s′ =
  Σ TxConstraints λ tx≡ → step CounterSM s i ≡ just (s′ , tx≡)

-- step preserves validity
lemma-step : ∀{s s' : CounterState}{i : CounterInput} → s —→[ i ] s' → Valid s → Valid s'
lemma-step {counter (+ 0)}       {i = inc} (_ , refl) (inj₁ p) = inj₂ (+≤+ z≤n)
lemma-step {counter (+ (suc n))} {i = inc} (_ , refl) (inj₁ ())
lemma-step {counter (+_ n)} {i = inc} (_ , refl) (inj₂ p) = inj₂ (+≤+ z≤n)

-- initial state is valid
lemma-initial : ∀{s} → T (isInitial CounterSM s) → Valid s
lemma-initial {counter (+ 0)} _ = inj₁ _


--

liveness : ∀ s → Σ CounterInput λ i → Σ CounterState λ s' → s —→[ i ] s'
liveness (counter x) = inc , _ , _ , refl

--

open CEM {sm = CounterSM}

open import Bisimulation.Base {sm = CounterSM} hiding (_—→[_]_)
open import Bisimulation.Completeness {sm = CounterSM}

lemma : ∀{tx l}
  → ∀{vtx : IsValidTx tx l}{vl : ValidLedger l}{vl′}
  → vl —→[ tx ∶- vtx ] vl′
  → ∀ s → vl ~ s
  → Valid s
  → (Σ CounterState λ s′ → Valid s′ × (vl′ ~ s′)) ⊎ vl′ ~ s
lemma p s q v with completeness {s = s} p q
lemma p s q v | inj₁ (i , s′ , tx≡ , r , r′ , r″) =
  inj₁ (s′ , lemma-step (tx≡ , r) v ,  r′)
lemma p s q v | inj₂ r = inj₂ r

-- this would also work for any property preserved by step,
-- or for any SM for that matter

lemmaP : ∀{tx l}
  → (P : CounterState → Set)
  → (X : ∀{s s' : CounterState}{i : CounterInput} → s —→[ i ] s' → P s → P s')
  → ∀{vtx : IsValidTx tx l}{vl : ValidLedger l}{vl′}
  → vl —→[ tx ∶- vtx ] vl′
  → ∀ s → vl ~ s
  → P s
  → (Σ CounterState λ s′ → P s′ × (vl′ ~ s′)) ⊎ vl′ ~ s
lemmaP P X p s q v with completeness {s = s} p q
lemmaP P X p s q v | inj₁ (i , s′ , tx≡ , r , r′ , r″) =
  inj₁ (s′ , X (tx≡ , r) v , r′)
lemmaP P X p s q v | inj₂ r = inj₂ r

-- liveness on chain

open import Bisimulation.Soundness {sm = CounterSM}

-- not sure what to do about satisfiability
-- the constraints are trivial/default so it should be ok 

liveness-lem : ∀ {l vl} s → vl ~ s →
  Σ Tx λ tx → Σ (IsValidTx tx l) λ vtx → Σ (ValidLedger (tx ∷ l)) λ vl' → vl —→[ tx ∶- vtx ] vl'
liveness-lem s b =
 let
   i , s' , tx≡ , p = liveness s
   tx , vtx , vl' , p , b' , X = soundness p b {!!}
  in
    tx , vtx , vl' , p

