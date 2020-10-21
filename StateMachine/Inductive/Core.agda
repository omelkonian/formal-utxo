open import Prelude.Init

open import UTxO.Hashing
open import UTxO.Value
open import UTxO.Types

open import StateMachine.Base

module StateMachine.Inductive.Core
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open CEM {sm = sm}

Predⁱ = Pred I 0ℓ
Predˢ = Pred S 0ℓ

-- Well-rooted CEM traces
_↝[_∣_]_ : S → I → TxConstraints → S → Set
s ↝[ i ∣ tx≡ ] s′ = stepₛₘ s i ≡ just (s′ , tx≡)

_↝[_]_ : S → I → S → Set
s ↝[ i ] s′ = ∃ λ tx≡ → s ↝[ i ∣ tx≡ ] s′

_↝_ : Rel S 0ℓ
s ↝ s′ = ∃ λ i → ∃ λ tx≡ → s ↝[ i ∣ tx≡ ] s′

-- T0D0: s/root/base and s/snoc/step
data _↝⋆_ : Rel S 0ℓ where
  root : ∀ {s} → Init s → s ↝⋆ s
  snoc : ∀{s s' s''} → s ↝⋆ s' → s' ↝ s'' → s ↝⋆ s''

snoc-lem : ∀{s s' s''}{xs xs' : s ↝⋆ s'}{x x' : s' ↝ s''}
  → snoc xs x ≡ snoc xs' x'
  → xs ≡ xs' × x ≡ x'
snoc-lem refl = refl , refl

-- ** temporal logic operators

private
  variable
    s s′ s″ : S
    i i′ i″ : I

Reachable : Predˢ
Reachable s = ∃ λ s₀ → Init s₀ × (s₀ ↝⋆ s)

-- safety (always)
□_ : Predˢ → Set
□ P = ∀ s → Reachable s → P s

-- liveness (eventually)
◇_ : Predˢ → Set
◇ P = ∃ λ s → Reachable s × P s
-- ◇ P = ¬ □ (¬_ ∘ P)

data _⁇_↝⋆_ (Pⁱ : Predⁱ) : S → S → Set where
  base⁇ : Pⁱ ⁇ s ↝⋆ s
  step⁇ : Pⁱ ⁇ s ↝⋆ s′
        → s′ ↝[ i ] s″
        → Pⁱ i
        → Pⁱ ⁇ s  ↝⋆ s″

sinceAsLong : Predˢ → Predˢ → Predⁱ → Set
sinceAsLong P Q Pⁱ = ∀ s → P s → (∀ s′ → Pⁱ ⁇ s ↝⋆ s′ → Q s′)

_↝⋆⟨_⟩_ : Predˢ → Predⁱ → Predˢ → Set
P ↝⋆⟨ Pⁱ ⟩ Q = sinceAsLong P Q Pⁱ
