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
open import Relation.Binary.PropositionalEquality hiding ([_])
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

-- some notation

_—→[_]_ : CounterState → CounterInput → CounterState → Set
s —→[ i ] s′ =
  Σ TxConstraints λ tx≡ → step CounterSM s i ≡ just (s′ , tx≡)

-- An invariant/safety property: all reachable states are non-negative

Valid : CounterState → Set
Valid s@(counter i)     =
  T (isInitial CounterSM s) ⊎ i ≥ (+ 0) -- ⊎ T (isFinal CounterSM s)

-- step preserves validity
lemma-step : ∀{s s' : CounterState}{i : CounterInput} → s —→[ i ] s' → Valid s → Valid s'
lemma-step {counter (+ 0)}       {i = inc} (_ , refl) (inj₁ p) = inj₂ (+≤+ z≤n)
lemma-step {counter (+ (suc n))} {i = inc} (_ , refl) (inj₁ ())
lemma-step {counter (+_ n)} {i = inc} (_ , refl) (inj₂ p) = inj₂ (+≤+ z≤n)

-- initial state is valid
lemma-initial : ∀{s} → T (isInitial CounterSM s) → Valid s
lemma-initial {counter (+ 0)} _ = inj₁ _

-- Validity holds on chain

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

-- Any such invariant holds on chain

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

-- Liveness
-- ========

-- A liveness property: all states can advance/the machine cannot get stuck

liveness : ∀ s → Σ CounterInput λ i → Σ CounterState λ s' → s —→[ i ] s'
liveness (counter x) = inc , _ , _ , refl

open import Bisimulation.Soundness {sm = CounterSM}

open import Data.List.Relation.Unary.All

-- trivial constraints are satisfiable, could be proved elsewhere

lemmaSat : ∀ {s l} {vl : ValidLedger l}
  → (p : vl ~ s)
  → Satisfiable {s}{l}{vl} (def Default-TxConstraints) p
lemmaSat p = refl , (refl , (λ tx → []))

livesat-lem : ∀ s → (proj₁ (proj₂ (proj₂ (liveness s)))) ≡ def Default-TxConstraints
livesat-lem (counter x) = refl

-- liveness holds on chain

liveness-lem : ∀ {l vl} s → vl ~ s →
  Σ Tx λ tx → Σ (IsValidTx tx l) λ vtx → Σ (ValidLedger (tx ∷ l)) λ vl' → vl —→[ tx ∶- vtx ] vl'
liveness-lem {l}{vl} s@(counter x) b =
 let
   i , s' , tx≡ , p = liveness s
   tx , vtx , vl' , p , b' , X = soundness {s = s} p b (lemmaSat {s}{l}{vl} b)
  in
    tx , vtx , vl' , p

-- trying to tie the knot with invariants for this state machine
-- (hopefully can be generalised to all machines)

-- a rooted run of the machine

data RootedRun : CounterState → CounterState → Set where
  root : ∀{s} → T (isInitial CounterSM s) → RootedRun s s
  cons : ∀{s s' i s''} → RootedRun s s' → s' —→[ i ] s'' → RootedRun s s''

-- the predicate P holds for all states in the run
data AllR (P : CounterState → Set) : ∀{s s'} → RootedRun s s' → Set where
  root : ∀ {s} → (p : T (isInitial CounterSM s)) → P s → AllR P (root p)
  cons : ∀ {s s' i s''} (p : RootedRun s s')(q : s' —→[ i ] s'')
    → P s'' → AllR P p → AllR P (cons p q)

-- the property holds in the end
end : ∀ P {s s'}{p : RootedRun s s'} → AllR P p → P s'
end P (root p q) = q
end P (cons p q r s) = r

all-lem : (P : CounterState → Set)
        → (∀{s} → T (isInitial CounterSM s) → P s)
        → (∀{s i s'} → s —→[ i ] s' → P s → P s')
        → ∀ {s s'}(p : RootedRun s s') → AllR P p
all-lem P base step (root p) = root p (base p)
all-lem P base step (cons p q) =
  cons p q (step q (end P h)) h
  where h = all-lem P base step p

-- a sequence of transactions from one bisimilar ledger and state pair to another
-- it starts from an initial state at the root and then proceeds via transactions we care about and skips those we don't
data X : ∀ {l l'} → ValidLedger l → CounterState → ValidLedger l' → CounterState → Set where
  root : ∀{l}(vl : ValidLedger l) → ∀ s → T (isInitial CounterSM s) → vl ~ s → X vl s vl s
  keep : ∀{l l' s s'}{vl : ValidLedger l}{vl' : ValidLedger l'} → X vl s vl' s' → ∀{tx}{vtx : IsValidTx tx l'}{vl''} → vl' —→[ tx ∶- vtx ] vl'' → ∀ s'' → vl'' ~ s'' →
    X vl s vl'' s''
--  skip : ∀{l l' s s'}{vl : ValidLedger l}{vl' : ValidLedger l'} → X vl s vl' s' → ∀{tx}{vtx : IsValidTx tx l'}{vl''} → vl' —→[ tx ∶- vtx ] vl'' → vl'' ~ s' → X vl s vl'' s'

-- the predicate P holds for all states in the sequence
data AllX (P : CounterState → Set) : ∀ {l l'}{vl : ValidLedger l}{s}{vl' : ValidLedger l'}{s'} → X vl s vl' s' → Set where
  root : ∀{l}(vl : ValidLedger l) → ∀ s → (i : T (isInitial CounterSM s))(p : vl ~ s) → P s → AllX P (root vl s i p)
  keep : ∀{l l' s s'}{vl : ValidLedger l}{vl' : ValidLedger l'}(xs : X vl s vl' s') → ∀{tx}{vtx : IsValidTx tx l'}{vl''}(p : vl' —→[ tx ∶- vtx ] vl'') → ∀ s'' (q : vl'' ~ s'') → P s''
    → AllX P xs → AllX P {s = s}{s' = s''} (keep xs p s'' q)

endX : (P : CounterState → Set) → ∀{l}{s}{vl : ValidLedger l}{s'}{l'}{vl' : ValidLedger l'}{xs : X vl s vl' s'} → AllX P xs → P s'
endX P (root vl s i p q) = q
endX P (keep xs p s'' q r ps) = r

end~ : (P : CounterState → Set) → ∀{l}{s}{vl : ValidLedger l}{s'}{l'}{vl' : ValidLedger l'}{xs : X vl s vl' s'} → AllX P xs → vl' ~ s'
end~ P (root vl s i p q) = p
end~ P (keep xs p s'' q r ps) = q

postulate ~uniq : ∀ l (vl : ValidLedger l) s s' → vl ~ s → vl ~ s' → s ≡ s'

all-lem-chain : (P : CounterState → Set)
        → (∀{s} → T (isInitial CounterSM s) → P s)
        → (∀{s i s'} → s —→[ i ] s' → P s → P s')
        → ∀{s s' l l'}{vl : ValidLedger l}{vl' : ValidLedger l'}(xs : X vl s vl' s') → AllX P xs
all-lem-chain P p q (root vl s p' q') = root vl s p' q' (p p')
all-lem-chain P p q (keep {s' = s'} xs {vl'' = vl''} p' s'' q') = keep xs p' s'' q' (Data.Sum.[ (λ {(_ , s''' , tx≡ , x , y , z) → subst P (~uniq _ vl'' s''' s'' y q') (q (tx≡ , x) (endX P blah))}) , (λ q'' → subst P (~uniq _ vl'' s' s'' q'' q') (endX P blah)) ] (completeness {s = s'} p'  (end~ P blah))) blah
  where blah = all-lem-chain P p q xs 
