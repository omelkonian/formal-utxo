module Hashing.Base where

open import Function      using (_∘_)
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

merge♯ : List ℕ → ℕ
merge♯ = sum

hashList : ∀ {ℓ} {A : Set ℓ} → (A → ℕ) → (List A → ℕ)
hashList hash1 = merge♯ ∘ map hash1

hashPair : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → Hash A → Hash B → Hash (A × B)
hashPair h₁ h₂ (a , b) = merge♯ (h₁ a ∷ h₂ b ∷ [])

-- Hashing strings.
_♯ₛₜᵣ : String → ℕ
_♯ₛₜᵣ = hashList toNat ∘ toList
