module StateMachine.Examples.Counter where

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

open import Prelude.Default
open import UTxO.Value
open import UTxO.Types
open import UTxO.TxUtilities
open import UTxO.Validity
open import StateMachine.Base

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

open import StateMachine.Properties {sm = CounterSM}
open import StateMachine.Inductive {sm = CounterSM}
open import Bisimulation.Base {sm = CounterSM}

-- An invariant/safety property: all reachable states are non-negative
-- ============================

Valid : State → Set
Valid s@(counter i)     =
  T (isInitial CounterSM s) ⊎ i ≥ (+ 0) -- ⊎ T (isFinal CounterSM s)


-- step preserves validity
lemma-step : ∀{s s' : State} → s ↝ s' → Valid s → Valid s'
lemma-step {counter (+ 0)}       (inc , _ , refl) (inj₁ p) = inj₂ (+≤+ z≤n)
lemma-step {counter (+ (suc n))} (inc , _ , refl) (inj₁ ())
lemma-step {counter (+_ n)}      (inc , _ , refl) (inj₂ p) = inj₂ (+≤+ z≤n)

-- for a slightly different representation of step
lemma-step' : ∀{s s'} → s ↝ s' → Valid s → Valid s'
lemma-step' {counter (+ 0)}       (inc , _ , refl) (inj₁ p) = inj₂ (+≤+ z≤n)
lemma-step' {counter (+ (suc n))} (inc , _ , refl) (inj₁ ())
lemma-step' {counter (+_ n)}      (inc , _ , refl) (inj₂ p) = inj₂ (+≤+ z≤n)


-- initial state is valid
lemma-initial : ∀{s} → T (isInitial CounterSM s) → Valid s
lemma-initial {counter (+ 0)} _ = inj₁ _

-- Validity for all states in any rooted run
all-valid : ∀{s s'}(xs : s ↝* s') → AllS Valid xs
all-valid xs = all-lem Valid lemma-initial lemma-step xs

open CEM {sm = CounterSM}
open import StateMachine.Properties.Ledger {sm = CounterSM}

-- Validity holds for all on chain traces
all-valid-ledger : ∀{l l'}{vl : ValidLedger l}{vl' : ValidLedger l'}{s s'}
  → (xs : X vl s vl' s') → AllS Valid (forget xs)
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

liveness : ∀ s → Σ Input λ i → Σ TxConstraints λ tx≡ → Σ State λ s' → s —→[ i ] (s' , tx≡)
liveness (counter x) = inc , _ , _ , refl

open import Bisimulation.Soundness {sm = CounterSM}

livesat-lem : ∀ s → (proj₁ $ proj₂ $ liveness s) ≡ def
livesat-lem (counter x) = refl

-- liveness holds on chain (in a particular sense)

liveness-lem : ∀ {l vl} s → vl ~ s →
  Σ Tx λ tx → Σ (IsValidTx tx l) λ vtx → Σ (ValidLedger (tx ∷ l)) λ vl' → vl —→[ tx ∶- vtx ] vl'
liveness-lem {l}{vl} s@(counter x) b =
 let
   i , tx≡ , s' , p = liveness s
   tx , vtx , vl' , p , b' , X = soundness {s = s} p b (lemmaSat {s}{l}{vl} b)
  in
    tx , vtx , vl' , p
