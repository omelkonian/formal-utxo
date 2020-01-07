module Bisimulation where

open import UTxO.Types
open import StateMachine.Base

open import Data.Product
open import Data.Maybe   using (Maybe; fromMaybe; nothing)
  renaming (just to pure; ap to _<*>_) -- to use idiom brackets
open import Data.List    using (List; []; _∷_; [_]; map; length; filter; null)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Bool using (Bool; T; true; false; if_then_else_; not)


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
         → ∀ q' → q Q⇒l q' → Σ P λ p' → p P⇒l p' × p' R q'
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
  (l , vl) —→∶ (l' , vl') = Σ Tx λ tx → Σ (IsValidTx tx l) λ vtx →  Σ (l' ≡ tx ∷ l) λ p → subst ValidLedger p vl' ≡ vl ⊕ tx ∶- vtx  

  -- assume that all transactions are within range
  postulate complies : ∀ l tx≡ → l -compliesTo- tx≡

  ~IsWeakBiSim : WeakBiSim
    (λ (p : Σ Ledger ValidLedger) s → proj₂ p ~ s)
    _—→∶_ -- this should allow internal actions on either side
    (λ _ _ → ⊥) -- this should allow one or more internal actions only
    (λ _ _ → ⊥) -- this should allow zero or more internal actions only
    _—→_        -- this is correct
    (λ _ _ → ⊥) -- this is correct
    (λ _ _ → ⊥) -- this is correct
  prop1   ~IsWeakBiSim = λ X lvl Y → {! !}
  prop2   ~IsWeakBiSim = {!!}
  prop1⁻¹ ~IsWeakBiSim {l , vl}{s} X s' (i , tx≡ , p , p') = let tx , vtx , vl' , q , r = soundness {l = l}{vl = vl} p' p X (complies l tx≡) in
    (tx ∷ l , vl') , (tx , vtx , (refl , q)) , r
  prop2⁻¹ ~IsWeakBiSim = λ _ _ ()

