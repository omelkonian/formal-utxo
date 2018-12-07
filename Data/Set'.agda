------------------------------------------------------------------------
-- Set utilities
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Function     using (_∘_)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (Bool; true; false; T)
open import Data.Nat     using (ℕ)
open import Data.List    using (List; []; _∷_; [_]; filter; _++_; length)
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂; _,_; Σ)

open import Relation.Nullary                      using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation             using (contradiction)
open import Relation.Nullary.Decidable            using (True)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Data.Set' {A : Set} (_≟_ : Decidable (_≡_ {A = A})) where

  open import Data.List.Membership.DecPropositional _≟_ renaming (_∈_ to _∈′_) public

  noDuplicates : List A → Bool
  noDuplicates [] = true
  noDuplicates (x ∷ xs) with x ∈? xs
  ... | yes _ = false
  ... | no  _ = noDuplicates xs

  Set' : Set
  Set' = ∃[ xs ] T (noDuplicates xs)

  _∈_ : A → Set' → Set
  o ∈ os = o ∈′ proj₁ os

  ¬? : {A : Set} → Dec A → Dec (¬ A)
  ¬? (yes x) = no (contradiction x)
  ¬? (no ¬x) = yes ¬x

  data ∀∈ (xs : Set') (P : A → Set) : Set where
   mk∀∈ : ∀ (x : A) → (x ∈ xs) → P x → ∀∈ xs P

  infix 2 ∀∈
  syntax ∀∈ xs (λ x → P) = ∀[ x ∈ xs ] P

  data ∃∈ (xs : Set') (P : A → Set) : Set where
   mk∃∈ : ∃[ x ] ((x ∈ xs) × P x) → ∃∈ xs P

  infix 2 ∃∈
  syntax ∃∈ xs (λ x → P) = ∃[ x ∈ xs ] P

  ∅ : Set'
  ∅ = [] , tt

  singleton : A → Set'
  singleton a = [ a ] , tt

  ∣_∣ : Set' → ℕ
  ∣_∣ = length ∘ proj₁

  infixr 5 _─_
  _─_ : Set' → Set' → Set'
  (xs , pxs) ─ (ys , pys) = zs , {!!}
    where
      zs : List A
      zs = filter (λ x → ¬? (x ∈? ys)) xs

  infixr 4 _∪_
  _∪_ : Set' → Set' → Set'
  x@(xs , pxs) ∪ y@(ys , pys) = xs ++ proj₁ z , {!!}
    where
      z : Set'
      z = x ─ y

  fromList : List A → Set'
  fromList [] = [] , tt
  fromList (x ∷ xs) with x ∈? xs
  ... | yes _ = fromList xs
  ... | no  _ = x ∷ proj₁ (fromList xs) , {!!}
