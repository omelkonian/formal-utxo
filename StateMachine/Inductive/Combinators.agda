open import Level
open import Function

open import Data.Maybe
open import Data.Product

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import UTxO.Hashing
open import UTxO.Value
open import UTxO.Types

open import StateMachine.Base

module StateMachine.Inductive.Combinators
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open CEM {sm = sm}
open import StateMachine.Inductive.Core {sm = sm}

-- *** All ***

-- the predicate P holds for all states in the run
data AllS (P : S → Set) : ∀{s s'} → s ↝* s' → Set where
  root : ∀ {s} (p : Init s)
    → P s
    → AllS P (root p)
  snoc : ∀ {s s' s''} (p : s ↝* s')(q : s' ↝ s'')
    → P s''
    → AllS P p → AllS P (snoc p q)

-- the property holds in the end
end : ∀ P {s s'}{p : s ↝* s'} → AllS P p → P s'
end P (root p q) = q
end P (snoc p q r s) = r

all-lem : (P : S → Set)
        → (∀{s} → Init s → P s)
        → (∀{s s'} → s ↝ s' → P s → P s')
        → ∀ {s s'}(p : s ↝* s') → AllS P p
all-lem P base step (root p) = root p (base p)
all-lem P base step (snoc p q) =
  snoc p q (step q (end P h)) h
  where h = all-lem P base step p

-- properties of inputs (which may refer to the other stuff)
data AllI (P₀ : S → Set) (P : S → I → TxConstraints → S → Set) : ∀ {s s'} → s ↝* s' → Set where
  root : ∀ {s} (p : Init s)
    → P₀ s
    → AllI P₀ P (root p)
  snoc : ∀ {s s' s'' } (p : s ↝* s')(q : s' ↝ s'')
    → P s' (proj₁ q) (proj₁ $ proj₂ q) s''
    → AllI P₀ P p → AllI P₀ P (snoc p q)

-- *** Any ***

data AnyS (P : S → Set) : ∀{s s'} → s ↝* s' → Set where

  root : ∀ {s} (p : Init s)
    → P s
    → AnyS P (root p)

  here : ∀ {s s' s''} (p : s ↝* s')(q : s' ↝ s'')
    → P s''
    → AnyS P (snoc p q)

  there : ∀ {s s' s''} (p : s ↝* s')(q : s' ↝ s'')
    → AnyS P p
    → AnyS P (snoc p q)
-- TODO: this isn't right, it needs two snoctructors for root

-- *** Until ***

-- P+Q*
-- P holds and then Q holds

-- * P has to hold at least at the initial state, it can hold forever
-- and then Q doesn't need to hold at all

-- * if Q takes over then P does not need to hold anymore. There is no
-- enforced overlap

data UntilS (P Q : S → Set) : ∀{s s'} → s ↝* s' → Set where
  prefix : ∀{s s'}(xs : s ↝* s')
    → AllS P xs
    → UntilS P Q xs

  suffix : ∀{s s' s''}(xs : s ↝* s')
    → UntilS P Q xs
    → (x : s' ↝ s'')
    → Q s''
    → UntilS P Q (snoc xs x)
