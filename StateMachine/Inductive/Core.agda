open import Prelude.Init

open import UTxO.Hashing
open import UTxO.Value
open import UTxO.Types

open import StateMachine.Base

module StateMachine.Inductive.Core
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open CEM {sm = sm}

-- Well-rooted CEM traces
_↝_ : Rel S 0ℓ
s ↝ s′ = ∃ λ i → ∃ λ tx≡ → stepₛₘ s i ≡ just (s′ , tx≡)

-- T0D0: s/root/base and s/snoc/step
data _↝*_ : Rel S 0ℓ where
  root : ∀ {s} → Init s → s ↝* s
  snoc : ∀{s s' s''} → s ↝* s' → s' ↝ s'' → s ↝* s''

snoc-lem : ∀{s s' s''}{xs xs' : s ↝* s'}{x x' : s' ↝ s''}
  → snoc xs x ≡ snoc xs' x'
  → xs ≡ xs' × x ≡ x'
snoc-lem refl = refl , refl
