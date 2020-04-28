module StateMachine.Timer where

open import StateMachine.Base
open import UTxO.Types
open import UTxO.Validity
open import Prelude.Default

open import Data.Integer using (+_;_≤_;_≥_;_>_;_<_;ℤ;+<+)
open import Data.Integer.Properties using (<-trans)
open import Data.Nat using (ℕ;_<?_;suc;z≤n;s≤s)
open import Data.Nat.Properties using (n<1+n;1+n≰n)
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Data.Bool using (true;false;T)
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Data.Empty

data TimerState : Set where
  timer : ℤ → _

data TimerInput : Set where
  inc : _

instance
  IsData-CS : IsData TimerState
  toData   ⦃ IsData-CS ⦄ (timer i) = I i
  fromData ⦃ IsData-CS ⦄ (I i) = just (timer i)
  fromData ⦃ IsData-CS ⦄ _     = nothing
  from∘to  ⦃ IsData-CS ⦄ (timer i) = refl
  from-inj ⦃ IsData-CS ⦄ (I i) (timer .i) refl = refl

  IsData-CI : IsData TimerInput
  toData   ⦃ IsData-CI ⦄ inc = LIST []
  fromData ⦃ IsData-CI ⦄ (LIST []) = just inc
  fromData ⦃ IsData-CI ⦄ _         = nothing
  from∘to  ⦃ IsData-CI ⦄ inc = refl
  from-inj ⦃ IsData-CI ⦄ (LIST []) inc refl = refl

TimerSM : StateMachine TimerState TimerInput
isInitial TimerSM (timer (+ 0)) = true
isInitial TimerSM (timer x) = false
isFinal TimerSM (timer (+_ 10)) = true
isFinal TimerSM (timer x) = false
step TimerSM (timer (+ n)) i with n <? 10
... | yes p = just (timer (+ (suc n)) , def Default-TxConstraints)
... | no ¬p = nothing
step TimerSM (timer (ℤ.negsuc n)) i = nothing
origin TimerSM = nothing

Valid : TimerState → Set
Valid s@(timer x) = T (isInitial TimerSM s) ⊎ (x > + 0 × x < + 10) ⊎ T (isFinal TimerSM s)

_—→[_]_ : TimerState → TimerInput → TimerState → Set
s —→[ i ] s′ =
  Σ TxConstraints λ tx≡ → step TimerSM s i ≡ just (s′ , tx≡)

lemma-step : ∀{s s' : TimerState}{i : TimerInput}
  → s —→[ i ] s' → Valid s → Valid s'
lemma-step {timer (+ 0)}  {timer (+ 1)} (tx≡ , p) v =
  inj₂ (inj₁ (+<+ (s≤s z≤n) , +<+ (Data.Nat.s≤s (s≤s z≤n))))
lemma-step {timer (+ 1)}  {timer (+ 2)} (tx≡ , p) v = inj₂ (inj₁ (+<+ (s≤s z≤n) , +<+ (s≤s (s≤s (s≤s z≤n)))))
lemma-step {timer (+ 2)}  {timer (+ 3)} (tx≡ , p) v = inj₂ (inj₁ (+<+ (s≤s z≤n) , +<+ (s≤s (s≤s (s≤s (s≤s z≤n))))))
lemma-step {timer (+ 3)}  {timer (+ 4)} (tx≡ , p) v = inj₂ (inj₁ (+<+ (s≤s z≤n) , +<+ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
lemma-step {timer (+ 4)}  {timer (+ 5)} (tx≡ , p) v = inj₂ (inj₁ (+<+ (s≤s z≤n) , +<+ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
lemma-step {timer (+ 5)}  {timer (+ 6)} (tx≡ , p) v = inj₂ (inj₁ (+<+ (s≤s z≤n) , +<+ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))
lemma-step {timer (+ 6)}  {timer (+ 7)} (tx≡ , p) v = inj₂ (inj₁ (+<+ (s≤s z≤n) , +<+ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))
lemma-step {timer (+ 7)}  {timer (+ 8)} (tx≡ , p) v = inj₂ (inj₁ (+<+ (s≤s z≤n) , +<+ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))
lemma-step {timer (+ 8)}  {timer (+ 9)} (tx≡ , p) v = inj₂ (inj₁ (+<+ (s≤s z≤n) , +<+ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))))
lemma-step {timer (+ 9)}  {timer (+ 10)} (tx≡ , p) v = inj₂ (inj₂ _)
lemma-step {timer (ℤ.negsuc n)} (tx≡ , ()) v

progress : ∀ s → Valid s → 
  (Σ TimerState λ s' → Σ TimerInput λ i → s —→[ i ] s') ⊎ T (isFinal TimerSM s)
progress (timer (+ 0)) p = inj₁ (timer (+ 1) , inc , _ , refl)
progress (timer (+ 1)) p = inj₁ (timer (+ 2) , inc , _ , refl) 
progress (timer (+ 2)) p = inj₁ (timer (+ 3) , inc , _ , refl)
progress (timer (+ 3)) p = inj₁ (timer (+ 4) , inc , _ , refl)
progress (timer (+ 4)) p = inj₁ (timer (+ 5) , inc , _ , refl)
progress (timer (+ 5)) p = inj₁ (timer (+ 6) , inc , _ , refl)
progress (timer (+ 6)) p = inj₁ (timer (+ 7) , inc , _ , refl)
progress (timer (+ 7)) p = inj₁ (timer (+ 8) , inc , _ , refl)
progress (timer (+ 8)) p = inj₁ (timer (+ 9) , inc , _ , refl)
progress (timer (+ 9)) p = inj₁ (timer (+ 10) , inc , _ , refl)
progress (timer (+ 10)) p = inj₂ _
progress (timer (+_ (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))))) (inj₂ (inj₁ (_ , +<+ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))))))))))
progress (timer (ℤ.negsuc n)) (inj₂ (inj₁ ()))
progress (timer (ℤ.negsuc n)) (inj₂ (inj₂ ()))

--

open CEM {sm = TimerSM}

open import Bisimulation.Base {sm = TimerSM} hiding (_—→[_]_)
open import Bisimulation.Completeness {sm = TimerSM}

-- This doesn't work for final states

{-
lemma : ∀{tx l}
  → ∀{vtx : IsValidTx tx l}{vl : ValidLedger l}{vl′}
  → vl —→[ tx ∶- vtx ] vl′
  → ∀ s → vl ~ s
  → Valid s
  → (Σ TimerState λ s′ → Valid s′ × (vl′ ~ s′)) ⊎ vl′ ~ s
lemma p s q v with completeness {s = s} p q
lemma p s q v | inj₁ (i , s′ , tx≡ , r , r′ , r″) =
  inj₁ (s′ , lemma-step (tx≡ , r) v , {!r′!})
lemma p s q v | inj₂ r = inj₂ r
-}

lemma : ∀{tx l}
  → ∀{vtx : IsValidTx tx l}{vl : ValidLedger l}{vl′}
  → vl —→[ tx ∶- vtx ] vl′
  → ∀ s → vl ~ s
  → Valid s
  → (Σ TimerState λ s′ → Σ TimerInput λ t → Valid s′ × s —→[ t ] s′) ⊎ vl′ ~ s
lemma p s q v with completeness {s = s} p q
lemma p s q v | inj₁ (i , s′ , tx≡ , r , r′ , r″) =
  inj₁ (s′ , i , lemma-step (tx≡ , r) v , tx≡ , r)
lemma p s q v | inj₂ r = inj₂ r
