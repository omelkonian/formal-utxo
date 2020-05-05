module UTxO.Hashing.Base where

open import Level                using (_⊔_)
open import Function             using (_∘_)
open import Function.Definitions using (Injective)
open import Function.Bundles     using (module Injection; _↣_)

open import Data.Product  using (_,_; _×_)
open import Data.String   using (String; toList)
open import Data.Char     using (toℕ)
open import Data.Nat      using (ℕ; _+_)
open import Data.Nat.Show using (show)
open import Data.List     using (List; []; _∷_; map; sum)

open import Data.List.Membership.Propositional  using (_∈_)
open import Data.List.Relation.Unary.Any as Any using (Any)

open import Relation.Binary.PropositionalEquality using (_≡_)

--------------------------------------------------------------------------------
-- Types for hash functions.

HashId : Set
HashId = ℕ

Hash : ∀ {ℓ} → (A : Set ℓ) → Set ℓ
Hash A = A → HashId

_-via-_ : ∀ {ℓᵃ ℓᵇ} {A : Set ℓᵃ} {B : Set ℓᵇ} → A → A ↣ B → B
a -via- record { f = f } = f a

-- A hash-preserving injection.
record _,_↪_,_ {ℓᵃ ℓᵇ} (A : Set ℓᵃ) (_♯ᵃ : Hash A) (B : Set ℓᵇ) (_♯ᵇ : Hash B) : Set (ℓᵃ ⊔ ℓᵇ) where
  field
    A↣B        : A ↣ B
    preserves♯ : ∀ (a : A) → a ♯ᵃ ≡ (a -via- A↣B) ♯ᵇ

open _,_↪_,_ public

_⟨$⟩_ : ∀ {ℓᵃ ℓᵇ} {A : Set ℓᵃ} {B : Set ℓᵇ} {_♯ᵃ : Hash A} {_♯ᵇ : Hash B}
      → A , _♯ᵃ ↪ B , _♯ᵇ
      → A → B
inj ⟨$⟩ a = a -via- (A↣B inj)

-- Common hashing utilities.
merge♯ : List HashId → HashId
merge♯ = sum

hashList : ∀ {ℓ} {A : Set ℓ} → Hash A → Hash (List A)
hashList hash1 = merge♯ ∘ map hash1

hashPair : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → Hash A → Hash B → Hash (A × B)
hashPair h₁ h₂ (a , b) = merge♯ (h₁ a ∷ h₂ b ∷ [])

_♯ₛₜᵣ : String → HashId
_♯ₛₜᵣ = hashList toℕ ∘ toList

-- Postulate there are hash functions for any type, e.g. functions.
postulate
  _♯ : ∀ {A : Set} → Hash A
  ♯-injective : ∀ {A : Set} → Injective {A = A} _≡_ _≡_ _♯

∈♯ : ∀ {A : Set} {x : A} {xs : List A}
  → Any ((x ♯ ≡_) ∘  _♯) xs
  → x ∈ xs
∈♯ = Any.map ♯-injective
