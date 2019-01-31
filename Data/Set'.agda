------------------------------------------------------------------------
-- Set utilities
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Level         using (0ℓ)
open import Function      using (_∘_)
open import Data.Unit     using (⊤; tt)
open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Bool     using (Bool; true; false; T)
open import Data.Nat      using (ℕ)
open import Data.List     using (List; []; _∷_; [_]; filter; _++_; length)
open import Data.List.Any using (Any; any; here; there)
open import Data.Product  using (_×_; ∃-syntax; proj₁; proj₂; _,_; Σ)

open import Data.List.Membership.Propositional.Properties using (∈-filter⁻)

open import Relation.Nullary                      using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation             using (contradiction; ¬?)
open import Relation.Nullary.Decidable            using (True; False; fromWitness; ⌊_⌋)
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

  open import Data.List.Relation.Subset.Propositional {A = A} using (_⊆_) public

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

  head⊆ : ∀ {x xs} → [ x ] ⊆ x ∷ xs
  head⊆ {x} {xs} (here refl) = here refl
  head⊆ {x} {xs} (there ())

  ------------------------------------------------------------------------
  -- Sets as lists with no duplicates.

  noDuplicates : List A → Set
  noDuplicates [] = ⊤
  noDuplicates (x ∷ xs) with x ∈? xs
  ... | yes _ = ⊥
  ... | no  _ = noDuplicates xs

  record Set' : Set where
    constructor ⟨_⟩∶-_
    field
      list   : List A
      .nodup : noDuplicates list
  open Set' public

  -- Set' : Set
  -- Set' = ∃[ xs ] noDuplicates xs

  infix 4 _∈′_
  _∈′_ : A → Set' → Set
  o ∈′ ⟨ os ⟩∶- _ = o ∈ os

  ∅ : Set'
  ∅ = ⟨ [] ⟩∶- tt

  singleton : A → Set'
  singleton a = ⟨ [ a ] ⟩∶- tt

  doubleton_,_∶-_ : (x : A) → (y : A) → False (x ≟ y) → Set'
  doubleton x , y ∶- pr with x ∈? [ y ]
  ... | yes (here refl) = ⊥-elim {!!}
  ... | yes (there ())
  ... | no ¬p = ⟨ x ∷ y ∷ [] ⟩∶- {!!}

  ∣_∣ : Set' → ℕ
  ∣_∣ = length ∘ list

  infixr 5 _─_
  _─_ : Set' → Set' → Set'
  ⟨ xs ⟩∶- pxs ─ ⟨ ys ⟩∶- pys = ⟨ zs ⟩∶- lem₂ {as = xs} pxs
    where
      zs : List A
      zs = filter (λ x → ¬? (x ∈? ys)) xs

      lem₁ : ∀ {a as}

           → noDuplicates as
           → ¬ (a ∈ as)
             ---------------------
           → noDuplicates (a ∷ as)
      lem₁ {a} {as} pas a∉as with a ∈? as
      ... | yes a∈as = a∉as a∈as
      ... | no  _    = pas


      lem₂ : ∀ {as : List A} {P : Pred A 0ℓ} {P? : UnaryDec P}

         → noDuplicates as
           ---------------------------
         → noDuplicates (filter P? as)

      lem₂ {[]}     {P} {P?} pas = tt
      lem₂ {a ∷ as} {P} {P?} pas with a ∈? as | P? a | a ∈? filter P? as
      ... | yes _   | _     | _     = ⊥-elim pas
      ... | no  _   | no  _ | _     = lem₂ {as} pas
      ... | no _    | yes _ | no ¬p = lem₁ (lem₂ {as} pas) ¬p
      ... | no a∉as | yes _ | yes p = ⊥-elim (a∉as (proj₁ (∈-filter⁻ P? p)))

  infixr 4 _∪_
  _∪_ : Set' → Set' → Set'
  x@(⟨ xs ⟩∶- pxs) ∪ y@(⟨ ys ⟩∶- pys) = ⟨ xs ++ list z ⟩∶- {!!}
    where
      z : Set'
      z = y ─ x

  fromList : List A → Set'
  fromList [] = ⟨ [] ⟩∶- tt
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
  ∅∪-identityˡ {x} rewrite ∅─-identityʳ {x} = {!!}

  ∅─∅≡∅ : ∅ ─ ∅ ≡ ∅
  ∅─∅≡∅ = ∅─-identityʳ {∅}

  from↔to : ∀ {xs}
    → noDuplicates xs
    → list (fromList xs) ≡ xs
  from↔to {[]} nodup = refl
  from↔to {x ∷ xs} nodup with x ∈? xs
  ... | yes _ = ⊥-elim nodup
  ... | no  _ = cong (x ∷_) (from↔to nodup)
