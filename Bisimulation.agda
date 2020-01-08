module Bisimulation where

open import UTxO.Types
open import StateMachine.Base

open import Data.Product
open import Data.Maybe   using (Maybe; fromMaybe; nothing)
  renaming (just to pure; ap to _<*>_) -- to use idiom brackets
open import Data.List    using (List; []; _∷_; [_]; map; length; filter; null)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Bool using (Bool; T; true; false; if_then_else_; not)
open import Data.List.Membership.Propositional  using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here)

data _* {P : Set}(R : P → P → Set) : P → P → Set where
  nil : ∀ {p} → (R *) p p
  cons : ∀ {p p' p''} → R p p' → (R *) p' p'' → (R *) p p''

data ⇒l {P : Set} (V I : P → P → Set) : P → P → Set where
  -- V = visible; I = internal
  con : ∀{p p' p'' p'''} → (I *) p p' → V p' p'' → (I *) p'' p''' → ⇒l V I p p'''

data ⇒τ {P : Set} (I : P → P → Set) : P → P → Set where
  -- I = internal
  con : ∀{p p' p'' p'''} → (I *) p p' → I p' p'' → (I *) p'' p''' → ⇒τ I p p'''

record WeakBiSim {P Q : Set}
  (_R_ : P → Q → Set)
  (_P⇒l_ _P⇒τ_ _P⇒_ : P → P → Set)
  (_Q⇒l_ _Q⇒τ_ _Q⇒_ : Q → Q → Set)
  : Set where
 field prop1   : ∀{p q} → p R q
         → ∀ p' → p P⇒l p' → Σ Q λ q' → q Q⇒l q' × p' R q'
       prop2   : ∀{p q} → p R q
         → ∀ p' → p P⇒τ p' → Σ Q λ q' → q Q⇒ q' × p' R q'
       prop1⁻¹ : ∀{p q} → p R q
         → ∀ q' → (x : q Q⇒l q') → Σ P λ p' → p P⇒l p' × p' R q'
       prop2⁻¹ : ∀{p q} → p R q
         → ∀ q' → q Q⇒τ q' → Σ P λ p' → p P⇒ p' × p' R q'
open WeakBiSim

module _ {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where
  open import Bisimulation.Base {S}{I}{sm}
  open import Bisimulation.Soundness {S}{I}{sm}
  open import Bisimulation.Completeness

  open import Relation.Binary.PropositionalEquality
  open import Data.Empty

  _—→_ : S → S → Set
  s —→ s′ = Σ I λ i → Σ TxConstraints λ tx≡ → stepₛₘ s i ≡ pure (s′ , tx≡) × ¬ T (finalₛₘ s′)

  _—→∶_ : (Σ Ledger ValidLedger) → (Σ Ledger ValidLedger) → Set
  (l , vl) —→∶ (l' , vl') = Σ Tx λ tx → Σ (IsValidTx tx l) λ vtx → Σ (l' ≡ tx ∷ l) λ p → subst ValidLedger p vl' ≡ vl ⊕ tx ∶- vtx  

  -- assume that all transactions are within range
  postulate complies : ∀ l tx≡ → l -compliesTo- tx≡

  docare : Σ Ledger ValidLedger → Σ Ledger ValidLedger → Set
  docare (l , vl) (l' , vl') = Σ Tx λ tx → Σ (IsValidTx tx l) λ vtx →  Σ (l' ≡ tx ∷ l) λ p → subst ValidLedger p vl' ≡ vl ⊕ tx ∶- vtx ×
    -- has a output that is locked with our validator
    𝕍 ∈ (Data.List.map address (outputs tx))

  dontcare : Σ Ledger ValidLedger → Σ Ledger ValidLedger → Set
  dontcare (l , vl) (l' , vl') = Σ Tx λ tx → Σ (IsValidTx tx l) λ vtx →  Σ (l' ≡ tx ∷ l) λ p → subst ValidLedger p vl' ≡ vl ⊕ tx ∶- vtx ×
    -- doesn't have a output that is locked with our validator
    𝕍 ∉ (Data.List.map address (outputs tx))

  ~IsWeakBiSim : WeakBiSim
    (λ (p : Σ Ledger ValidLedger) s → proj₂ p ~ s)
    (⇒l docare dontcare) -- this should allow internal actions on either side of a visible one
    (⇒τ dontcare)        -- this should allow one or more internal actions only
    (dontcare *)         -- this should allow zero or more internal actions only
    (⇒l _—→_ λ _ _ → ⊥)  -- internal actions on either side of visible
    (⇒τ λ _ _ → ⊥)       -- one or more internal actions
    (_—→_ *)             -- zero or more internal actions
  prop1 ~IsWeakBiSim X (l , vl) (con vs (tx , vtx , p , p') vs') = {!vs !}
  prop2   ~IsWeakBiSim = {!!}
  prop1⁻¹ ~IsWeakBiSim {l , vl}{s} X s' (con nil (i , tx≡ , p , p') nil) = let tx , vtx , vl' , q , r = soundness {l = l}{vl = vl} p' p X (complies l tx≡) in
    (tx ∷ l , vl') , con nil (tx , vtx , refl , refl , here refl) nil , r
  prop2⁻¹ ~IsWeakBiSim = λ x q' → λ{(con _ () _)}

