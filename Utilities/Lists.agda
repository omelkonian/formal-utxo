------------------------------------------------------------------------
-- List utilities
------------------------------------------------------------------------

module Utilities.Lists where

open import Data.List using (List; map; sum)
open import Data.Nat using (ℕ)

_<$>_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → List A → List B
_<$>_ = map

sumValues : ∀ {A : Set} → (A → ℕ) → List A → ℕ
sumValues f xs = sum (f <$> xs)
syntax sumValues f xs = Σ[ f ∈ xs ]
