module UTxO.Crypto where

open import Function.Definitions using (Injective)

open import Data.Bool using (Bool)
open import Data.Nat  using (ℕ)
open import Data.List using (List)

open import Relation.Binary.PropositionalEquality using (_≡_)

--------------------------------------------------------------------------------
-- Types for hash functions.

HashId Signature : Set
HashId    = ℕ
Signature = HashId

Hash : ∀ {ℓ} → (A : Set ℓ) → Set ℓ
Hash A = A → HashId

postulate
  -- collision-resistant hashing function for any type, e.g. functions
  _♯ : ∀ {A : Set} → Hash A
  ♯-injective : ∀ {A : Set} → Injective {A = A} _≡_ _≡_ _♯

  -- verify signature
  isSignedBy : ∀ {A : Set} → A → Signature → HashId → Bool

  -- m-of-n signature
  MultiSignature : Set
  checkMultiSig : MultiSignature → List Signature → Bool
