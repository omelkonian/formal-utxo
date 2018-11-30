------------------------------------------------------------------------
-- Set utilities
------------------------------------------------------------------------

module Utilities.Sets where

open import Level     using (0ℓ)
open import Function  using (const)
open import Data.Unit using (⊤)
open import Data.Bool using (T)
open import Data.Nat  using (ℕ; _<_)
open import Data.List using (boolFilter; _++_; length)

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary using (IsStrictTotalOrder; Rel)

import Data.AVL.Sets as Sets

module _ {A : Set} {_<_  : Rel A 0ℓ} {A-sto : IsStrictTotalOrder _≡_ _<_} where

  open Sets A-sto

  Set⟨A⟩ : Set
  Set⟨A⟩ = ⟨Set⟩' (const ⊤)

  _∈_ : A → Set⟨A⟩ → Set
  o ∈ os = T (o ∈? os)

  data ∀∈ (xs : Set⟨A⟩) (P : A → Set) : Set where
   mk∀∈ : ∀ (x : A) → (x ∈ xs) → P x → ∀∈ xs P

  infix 2 ∀∈
  syntax ∀∈ xs (λ x → P) = ∀[ x ∈ xs ] P

  ∅ : Set⟨A⟩
  ∅ = empty

  ∣_∣ : Set⟨A⟩ → ℕ
  ∣ xs ∣ = length (toList xs)

  infixr 5 _─_
  _─_ : Set⟨A⟩ → Set⟨A⟩ → Set⟨A⟩
  xs ─ ys = fromList (boolFilter (λ x → x ∈? ys) (toList xs))

  infixr 4 _∪_
  _∪_ : Set⟨A⟩ → Set⟨A⟩ → Set⟨A⟩
  xs ∪ ys = fromList (toList xs ++ toList ys)
