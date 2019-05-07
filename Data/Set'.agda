------------------------------------------------------------------------
-- Set utilities
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Level         using (0ℓ)
open import Function      using (_∘_)
open import Data.Unit     using (⊤; tt)
open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Product  using (_×_; ∃-syntax; proj₁; proj₂; _,_; Σ)
open import Data.Sum      using (_⊎_; inj₁; inj₂; map₁; map₂)
open import Data.Bool     using (Bool; true; false; T)
open import Data.Nat      using (ℕ)
open import Data.List     using (List; []; _∷_; [_]; filter; _++_; length)

open import Data.List.Relation.Unary.Any using (Any; any; here; there)
open import Data.List.Relation.Unary.All using (All) renaming ([] to ∀[]; _∷_ to _∀∷_)
import Data.List.Relation.Unary.Unique.Propositional as Uniq
open import Data.List.Membership.Propositional.Properties using (∈-filter⁻; ∈-++⁻)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)

open import Relation.Nullary                      using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation             using (contradiction; ¬?)
open import Relation.Nullary.Decidable            using (True; False; fromWitness; toWitness; ⌊_⌋)
open import Relation.Unary                        using (Pred)
  renaming (Decidable to UnaryDec)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; inspect)

module Data.Set' {A : Set} (_≟_ : Decidable (_≡_ {A = A})) where

  open import Data.List.Membership.DecPropositional _≟_ using (_∈_; _∉_; _∈?_) public

  ------------------------------------------------------------------------
  -- Decidable equality.

  infix 4 _≟ₗ_
  _≟ₗ_ : Decidable {A = List A} _≡_
  []     ≟ₗ []     = yes refl
  []     ≟ₗ _ ∷ _  = no λ ()
  _ ∷ _  ≟ₗ []     = no λ ()
  x ∷ xs ≟ₗ y ∷ ys with x ≟ y
  ... | no ¬p      = no λ{refl → ¬p refl}
  ... | yes refl   with xs ≟ₗ ys
  ... | no ¬pp     = no λ{refl → ¬pp refl}
  ... | yes refl   = yes refl

  ------------------------------------------------------------------------
  -- Subset relation.

  _⊆?_ : List A → List A → Set
  []       ⊆? _  = ⊤
  (x ∷ xs) ⊆? ys with x ∈? ys
  ... | yes _ = xs ⊆? ys
  ... | no  _ = ⊥

  sound-⊆ : ∀ {xs ys} → {p : xs ⊆? ys} → xs ⊆ ys
  sound-⊆ {[]} {ys} {xs⊆?ys} = λ ()
  sound-⊆ {x ∷ xs} {ys} {xs⊆?ys} with x ∈? ys
  ... | yes x∈ys = λ{ (here refl)  → x∈ys
                    ; (there y∈xs) → (sound-⊆ {p = xs⊆?ys}) y∈xs }
  ... | no  x∉ys = ⊥-elim xs⊆?ys

  head⊆ : ∀ {x : A} {xs : List A} → [ x ] ⊆ x ∷ xs
  head⊆ {x} {xs} (here refl) = here refl
  head⊆ {x} {xs} (there ())

  ------------------------------------------------------------------------
  -- Sets as lists with no duplicates.
  open Uniq {0ℓ} {A} using (Unique) public renaming ([] to U[]; _∷_ to _U∷_)
  open import Data.List.Relation.Unary.AllPairs using (allPairs?)

  unique? : ∀ xs → Dec (Unique xs)
  unique? xs = allPairs? (λ x y → ¬? (x ≟ y)) xs

  record Set' : Set where
    constructor ⟨_⟩∶-_
    field
      list  : List A
      .uniq : Unique list
  open Set' public

  infix 4 _∈′_
  _∈′_ : A → Set' → Set
  o ∈′ ⟨ os ⟩∶- _ = o ∈ os

  ∅ : Set'
  ∅ = ⟨ [] ⟩∶- U[]

  singleton : A → Set'
  singleton a = ⟨ [ a ] ⟩∶- (∀[] U∷ U[])

  ∣_∣ : Set' → ℕ
  ∣_∣ = length ∘ list

  infixr 5 _─_
  _─_ : Set' → Set' → Set'
  ⟨ xs ⟩∶- pxs ─ ⟨ ys ⟩∶- pys = ⟨ filter (λ x → ¬? (x ∈? ys)) xs ⟩∶- {!!}

  infixr 4 _∪_
  _∪_ : Set' → Set' → Set'
  x@(⟨ xs ⟩∶- pxs) ∪ y@(⟨ ys ⟩∶- pys) = ⟨ xs ++ list (y ─ x) ⟩∶- {!!}

  fromList : List A → Set'
  fromList [] = ⟨ [] ⟩∶- U[]
  fromList (x ∷ xs) with x ∈? xs
  ... | yes _ = fromList xs
  ... | no  _ = ⟨ x ∷ list (fromList xs) ⟩∶- {!!}

  -----------------------------------------------------
  -- Properties

  ≡-Set' : ∀ {xs ys px py}
         → xs ≡ ys
         → ⟨ xs ⟩∶- px ≡ ⟨ ys ⟩∶- py
  ≡-Set' refl = refl

  ∅─-identityʳ : ∀ {x} → (x ─ ∅) ≡ x
  ∅─-identityʳ {x} = {!!}

  ∅∪-identityˡ : ∀ {x} → (∅ ∪ x) ≡ x
  ∅∪-identityˡ {x} rewrite ∅─-identityʳ {x} = refl

  ∅─∅≡∅ : ∅ ─ ∅ ≡ ∅
  ∅─∅≡∅ = ∅─-identityʳ {∅}

  from↔to : ∀ {xs}
    → Unique xs
    → list (fromList xs) ≡ xs
  from↔to {[]} uniq = refl
  from↔to {x ∷ xs} uniq with x ∈? xs
  ... | no  _ = cong (x ∷_) (from↔to (Uniq.tail {0ℓ} {A} {0ℓ} {0ℓ} uniq))
  ... | yes p with uniq
  ... | p1 U∷ p2 = {!!}

  ∈-─ : ∀ {x : A} {xs ys : Set'}
    → x ∈′ (xs ─ ys)
    → x ∈′ xs
  ∈-─ {x} {xs} {ys} x∈ = proj₁ (∈-filter⁻ (λ x → ¬? (x ∈? list ys)) x∈)

  ∈-∪ : ∀ {x : A} {xs ys : Set'}
    → x ∈′ (xs ∪ ys)
    → x ∈′ xs ⊎ x ∈′ ys
  ∈-∪ {x} {xs} {ys} x∈ = map₂ (∈-─ {x} {ys} {xs}) (∈-++⁻ {v = x} (list xs) {ys = list (ys ─ xs)} x∈)
