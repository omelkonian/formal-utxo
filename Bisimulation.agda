module Bisimulation where

open import Bisimulation.Base
open import Bisimulation.Soundness
open import Bisimulation.Completeness

open import Data.Product

record WeakBiSim {P Q : Set}
  (_R_ : P → Q → Set)
  (_P⇒τ_ _P⇒l_ _P⇒_ : P → P → Set)
  (_Q⇒τ_ _Q⇒l_ _Q⇒_ : Q → Q → Set)
  : Set where
 field prop1   : ∀{p q} → p R q
         → ∀ p' → p P⇒l p' → Σ Q λ q' → q Q⇒l q' × p' R q'
       prop2   : ∀{p q} → p R q
         → ∀ p' → p P⇒τ p' → Σ Q λ q' → q Q⇒ q' × p' R q'
       prop1⁻¹ : ∀{p q} → p R q
         → ∀ q' → q Q⇒l q' → Σ P λ p' → p P⇒l p' × p' R q'
       prop2⁻¹ : ∀{p q} → p R q
         → ∀ q' → q Q⇒τ q' → Σ P λ p' → p P⇒ p' × p' R q'
