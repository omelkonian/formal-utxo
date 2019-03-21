------------------------------------------------------------------------
-- Fixed universe of types used on-chain.
------------------------------------------------------------------------
module Data.TYPE where

open import Data.Unit    using (⊤)
open import Data.Product using (_×_)
open import Data.Sum     using (_⊎_)
open import Data.Bool    using (Bool)
open import Data.Nat     using (ℕ)
open import Data.List    using (List)

data 𝕌 : Set where
  UNIT    : 𝕌
  BOOL    : 𝕌
  NAT     : 𝕌
  PRODUCT : 𝕌 → 𝕌 → 𝕌
  SUM     : 𝕌 → 𝕌 → 𝕌
  LIST    : 𝕌 → 𝕌

el : 𝕌 → Set
el UNIT          = ⊤
el BOOL          = Bool
el NAT           = ℕ
el (PRODUCT x y) = el x × el y
el (SUM x y)     = el x ⊎ el y
el (LIST x)      = List (el x)

open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

_≟ᵤ_ : Decidable {A = 𝕌} _≡_
UNIT ≟ᵤ UNIT = yes refl
UNIT ≟ᵤ BOOL = no λ ()
UNIT ≟ᵤ NAT = no λ ()
UNIT ≟ᵤ PRODUCT _ _ = no λ ()
UNIT ≟ᵤ SUM _ _ = no λ ()
UNIT ≟ᵤ LIST _ = no λ ()

BOOL ≟ᵤ BOOL = yes refl
BOOL ≟ᵤ UNIT = no λ ()
BOOL ≟ᵤ NAT = no λ ()
BOOL ≟ᵤ PRODUCT _ _ = no λ ()
BOOL ≟ᵤ SUM _ _ = no λ ()
BOOL ≟ᵤ LIST _ = no λ ()

NAT ≟ᵤ NAT = yes refl
NAT ≟ᵤ UNIT = no λ ()
NAT ≟ᵤ BOOL = no λ ()
NAT ≟ᵤ PRODUCT _ _ = no λ ()
NAT ≟ᵤ SUM _ _ = no λ ()
NAT ≟ᵤ LIST _ = no λ ()

PRODUCT u₁ u₂ ≟ᵤ PRODUCT u₁′ u₂′
  with u₁ ≟ᵤ u₁′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl
  with u₂ ≟ᵤ u₂′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl = yes refl
PRODUCT _ _  ≟ᵤ UNIT = no λ ()
PRODUCT _ _  ≟ᵤ BOOL = no λ ()
PRODUCT _ _  ≟ᵤ NAT = no λ ()
PRODUCT _ _  ≟ᵤ SUM _ _ = no λ ()
PRODUCT _ _  ≟ᵤ LIST _ = no λ ()

SUM u₁ u₂ ≟ᵤ SUM u₁′ u₂′
  with u₁ ≟ᵤ u₁′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl
  with u₂ ≟ᵤ u₂′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl = yes refl
SUM _ _  ≟ᵤ UNIT = no λ ()
SUM _ _  ≟ᵤ BOOL = no λ ()
SUM _ _  ≟ᵤ NAT = no λ ()
SUM _ _  ≟ᵤ PRODUCT _ _ = no λ ()
SUM _ _  ≟ᵤ LIST _ = no λ ()

LIST u ≟ᵤ LIST u′
  with u ≟ᵤ u′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl = yes refl
LIST _  ≟ᵤ UNIT = no λ ()
LIST _  ≟ᵤ BOOL = no λ ()
LIST _  ≟ᵤ NAT = no λ ()
LIST _  ≟ᵤ PRODUCT _ _ = no λ ()
LIST _  ≟ᵤ SUM _ _ = no λ ()
