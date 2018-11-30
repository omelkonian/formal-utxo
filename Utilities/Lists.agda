------------------------------------------------------------------------
-- List utilities
------------------------------------------------------------------------

module Utilities.Lists where

open import Level                 using (0ℓ)
open import Category.Functor      using (RawFunctor)
open import Data.List             using (List; map; sum)
open import Data.List.Categorical using (functor)
open import Data.Nat              using (ℕ)

open RawFunctor {0ℓ} functor public

sumValues : ∀ {A : Set} → (A → ℕ) → List A → ℕ
sumValues f xs = sum (f <$> xs)
syntax sumValues f xs = Σ[ f ∈ xs ]
