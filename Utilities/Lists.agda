------------------------------------------------------------------------
-- List utilities
------------------------------------------------------------------------

module Utilities.Lists where

open import Data.List             using (List; map; sum)
open import Data.Nat              using (ℕ)

Σ-sum-syntax : ∀ {A : Set} → (A → ℕ) → List A → ℕ
Σ-sum-syntax f xs = sum (map f xs)
syntax Σ-sum-syntax f xs = Σ[ f ∈ xs ]
