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
open import Relation.Binary.PropositionalEquality renaming ([_] to remember)
open import Data.List
open import Data.Product
open import Function
open import Data.Bool using (true;false;T)
open import Data.Bool.Properties using () renaming (_≟_ to _≟B_)
open import Data.Sum

data State : Set where
  counter : ℤ → State

data Input : Set where
  inc : Input

instance
  IsData-CS : IsData State
  toData   ⦃ IsData-CS ⦄ (counter i) = I i
  fromData ⦃ IsData-CS ⦄ (I i) = just (counter i)
  fromData ⦃ IsData-CS ⦄ _     = nothing
  from∘to  ⦃ IsData-CS ⦄ (counter i) = refl
  from-inj ⦃ IsData-CS ⦄ (I i) (counter .i) refl = refl

  IsData-CI : IsData Input
  toData   ⦃ IsData-CI ⦄ inc = LIST []
  fromData ⦃ IsData-CI ⦄ (LIST []) = just inc
  fromData ⦃ IsData-CI ⦄ _         = nothing
  from∘to  ⦃ IsData-CI ⦄ inc = refl
  from-inj ⦃ IsData-CI ⦄ (LIST []) inc refl = refl
  
CounterSM : StateMachine State Input
isInitial CounterSM (counter (+ 0) ) = true
isInitial CounterSM (counter _     ) = false
-- isFinal   CounterSM (counter (+ 10)) = false
-- isFinal   CounterSM _ = false
step      CounterSM (counter i) inc =
  just (counter (Data.Integer.suc i) , def Default-TxConstraints)
origin    CounterSM = nothing

-- An invariant/safety property: all reachable states are non-negative
-- ============================

Valid : State → Set
Valid s@(counter i)     =
  T (isInitial CounterSM s) ⊎ i ≥ (+ 0) -- ⊎ T (isFinal CounterSM s)

open import StateMachine.Properties {sm = CounterSM}

-- step preserves validity
lemma-step : ∀{s s' : State}{i : Input} → s —→[ i ]' s' → Valid s → Valid s'
lemma-step {counter (+ 0)}       {i = inc} (_ , refl) (inj₁ p) = inj₂ (+≤+ z≤n)
lemma-step {counter (+ (suc n))} {i = inc} (_ , refl) (inj₁ ())
lemma-step {counter (+_ n)} {i = inc} (_ , refl) (inj₂ p) = inj₂ (+≤+ z≤n)

-- initial state is valid
lemma-initial : ∀{s} → T (isInitial CounterSM s) → Valid s
lemma-initial {counter (+ 0)} _ = inj₁ _

-- Validity for all states in any rooted run
all-valid : ∀{s s'}(xs : RootedRun s s') → AllR Valid xs
all-valid xs = all-lem Valid lemma-initial lemma-step xs

open CEM {sm = CounterSM}
open import Bisimulation.Base {sm = CounterSM} hiding (_—→[_]_)
open import StateMachine.Properties.Ledger {sm = CounterSM}

-- Validity holds for all on chain traces
all-valid-ledger : ∀{l l'}{vl : ValidLedger l}{vl' : ValidLedger l'}{s s'}
  → (xs : X vl s vl' s') → AllR Valid (forget xs)
all-valid-ledger xs = all-valid (forget xs)

-- Validity holds on chain in a different sense
lemma : ∀{tx l}
  → ∀{vtx : IsValidTx tx l}{vl : ValidLedger l}{vl′}
  → vl —→[ tx ∶- vtx ] vl′
  → ∀ s → vl ~ s
  → Valid s
  → (Σ State λ s′ → Valid s′ × (vl′ ~ s′)) ⊎ vl′ ~ s
lemma = lemmaP Valid lemma-step

-- Liveness
-- ========

-- A liveness property: all states can advance/the machine cannot get stuck

liveness : ∀ s → Σ Input λ i → Σ State λ s' → s —→[ i ]' s'
liveness (counter x) = inc , _ , _ , refl

open import Bisimulation.Soundness {sm = CounterSM}

livesat-lem : ∀ s → (proj₁ (proj₂ (proj₂ (liveness s)))) ≡ def Default-TxConstraints
livesat-lem (counter x) = refl

-- liveness holds on chain (in a particular sense)

liveness-lem : ∀ {l vl} s → vl ~ s →
  Σ Tx λ tx → Σ (IsValidTx tx l) λ vtx → Σ (ValidLedger (tx ∷ l)) λ vl' → vl —→[ tx ∶- vtx ] vl'
liveness-lem {l}{vl} s@(counter x) b =
 let
   i , s' , tx≡ , p = liveness s
   tx , vtx , vl' , p , b' , X = soundness {s = s} p b (lemmaSat {s}{l}{vl} b)
  in
    tx , vtx , vl' , p


