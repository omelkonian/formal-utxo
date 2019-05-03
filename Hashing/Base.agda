module Hashing.Base where

open import Level              using (_⊔_)
open import Function           using (_∘_)
open import Function.Injection using (module Injection; _↣_)

open import Data.Product  using (_,_; _×_)
open import Data.String   using (String; toList)
open import Data.Char     using (toNat)
open import Data.Nat      using (ℕ; _+_)
open import Data.Nat.Show using (show)
open import Data.List     using (List; []; _∷_; map; sum)

open import Relation.Binary.PropositionalEquality using (_≡_)

--------------------------------------------------------------------------------
-- Types for hash functions.

Hash : ∀ {ℓ} → (A : Set ℓ) → Set ℓ
Hash A = A → ℕ

Injective : ∀ {ℓ} {A : Set ℓ} → (A → ℕ) → Set ℓ
Injective _# = ∀ {x y} → (x #) ≡ (y #) → x ≡ y

_-via-_ : ∀ {ℓᵃ ℓᵇ} {A : Set ℓᵃ} {B : Set ℓᵇ} → A → A ↣ B → B
a -via- record { to = record { _⟨$⟩_ = f } } = f a

-- A hash-preserving injection.
record _,_↪_,_ {ℓᵃ ℓᵇ} (A : Set ℓᵃ) (_♯ᵃ : Hash A) (B : Set ℓᵇ) (_♯ᵇ : Hash B) : Set (ℓᵃ ⊔ ℓᵇ) where
  field
    injection  : A ↣ B
    preserves♯ : ∀ (a : A) → a ♯ᵃ ≡ (a -via- injection) ♯ᵇ

open _,_↪_,_ public

_⟨$⟩_ : ∀ {ℓᵃ ℓᵇ} {A : Set ℓᵃ} {B : Set ℓᵇ} {_♯ᵃ : Hash A} {_♯ᵇ : Hash B}
      → A , _♯ᵃ ↪ B , _♯ᵇ
      → A → B
record {injection = A↣B} ⟨$⟩ a = a -via- A↣B

-- Common hashing utilities.
merge♯ : List ℕ → ℕ
merge♯ = sum

hashList : ∀ {ℓ} {A : Set ℓ} → (A → ℕ) → (List A → ℕ)
hashList hash1 = merge♯ ∘ map hash1

hashPair : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → Hash A → Hash B → Hash (A × B)
hashPair h₁ h₂ (a , b) = merge♯ (h₁ a ∷ h₂ b ∷ [])

_♯ₛₜᵣ : String → ℕ
_♯ₛₜᵣ = hashList toNat ∘ toList
