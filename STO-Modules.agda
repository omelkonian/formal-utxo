-------------------------------------------------------------------
-- Strict Total Orders for all basic UTxO datatypes.
-------------------------------------------------------------------

module STO-Modules where

open import Function            using (const; _on_; _∘_)
open import Level               using (0ℓ)
open import Data.Nat.Properties using ( <-trans; 1+n≰n; <-isStrictTotalOrder
                                      ; <-cmp; <-resp₂-≡ )
open import Data.Nat            using (ℕ; _<_; _>_)
open import Data.Unit           using (⊤)
open import Data.Empty          using (⊥)
open import Data.List           using (List; _∷_)
open import Data.Char as Char
open import Agda.Builtin.Char   using (Char)
  renaming (primCharToNat to →ℕ)
open import Data.String         using ()
  renaming (primStringToList to →[]; primStringFromList to []→)
open import Data.String.Unsafe  using (fromList∘toList)

import Data.AVL.Sets as Sets
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary  using ( StrictTotalOrder; _⇒_; IsEquivalence; _Respects₂_
                                   ; IsStrictTotalOrder; Rel; Transitive; Trichotomous
                                   ; tri≈; tri<; tri> )
import Relation.Binary.Construct.On          as On
import Relation.Binary.PropositionalEquality as Eq
open IsStrictTotalOrder using (compare)
  renaming (trans to sto-trans)

open Eq.≡-Reasoning
open Eq using (_≡_; refl; sym; trans; cong; cong₂)
  renaming (isEquivalence to ≡-isEquivalence)

import Data.List.Relation.Lex.Strict     as StrictLex
open import Data.List.Relation.Pointwise as Pointwise using (Pointwise)
open import Data.List.Relation.Lex.Core               using (Lex)

open import Utilities.Sets
open import Types

-------------------------------------------------------------------
-- Natural numbers.

STO⟨ℕ⟩ : IsStrictTotalOrder _≡_ _<_
STO⟨ℕ⟩ = <-isStrictTotalOrder

module STO⟦ℕ⟧ = Sets STO⟨ℕ⟩

Set⟨ℕ⟩ : Set
Set⟨ℕ⟩ = ⟨Set⟩' (const ⊤)
  where open STO⟦ℕ⟧

-------------------------------------------------------------------
-- Characters, strings, scripts.

STO⟨Char⟩ : IsStrictTotalOrder _≡_ (_<_ on →ℕ)
STO⟨Char⟩ =
  record { isEquivalence = ≡-isEquivalence
         ; trans = λ {i} {j} {k} i≺j j≺k → ≺-trans {i} {j} {k} i≺j j≺k
         ; compare = ≺-trichotomous
         }

  where
    ≺-trans : Transitive (_<_ on →ℕ)
    ≺-trans {i} {j} {k} i<j j<k = On.transitive →ℕ _<_ <-trans {i} {j} {k} i<j j<k

    -- should be in stdlib
    →ℕ-inj : ∀ {x y} → →ℕ x ≡ →ℕ y → x ≡ y
    →ℕ-inj _ = trustMe
      where open import Relation.Binary.PropositionalEquality.TrustMe

    ≺-trichotomous : Trichotomous _≡_ (_<_ on →ℕ)
    ≺-trichotomous x y with <-cmp (→ℕ x) (→ℕ y)
    ... | tri< a ¬b ¬c = tri< a (λ z → ¬b (cong →ℕ z)) ¬c
    ... | tri≈ ¬a b ¬c = tri≈ ¬a (→ℕ-inj b) ¬c
    ... | tri> ¬a ¬b c = tri> ¬a (λ z → ¬b (cong →ℕ z)) c

_≡ₛ_ : Rel Script 0ℓ
_≡ₛ_ = Pointwise (_≡_ on →ℕ) on →[]

_≺ₛ_ : Rel Script 0ℓ
_≺ₛ_ = Lex ⊥ (_≡_ on →ℕ) (_<_ on →ℕ) on →[]

STO⟨Script⟩′ : IsStrictTotalOrder {A = Script} _≡ₛ_ _≺ₛ_
STO⟨Script⟩′ =
  StrictTotalOrder.isStrictTotalOrder
    (On.strictTotalOrder (StrictLex.<-strictTotalOrder Char.strictTotalOrder) →[])

STO⟨Script⟩ : IsStrictTotalOrder _≡_ _≺ₛ_
STO⟨Script⟩ =
  record { isEquivalence = ≡-isEquivalence
         ; trans = λ {i} {j} {k} → ≺-trans {i} {j} {k}
         ; compare = ≺-trichotomous
         }

  where
    ≺-trans : Transitive _≺ₛ_
    ≺-trans = StrictLex.<-transitive
      (On.isEquivalence →ℕ ≡-isEquivalence)
      (On.respects₂ →ℕ _<_ _≡_ <-resp₂-≡)
      (λ {i} {j} {k} → sto-trans STO⟨Char⟩ {i} {j} {k})

    -- should be in stdlib
    →ℕ-inj : ∀ {x y} → →ℕ x ≡ →ℕ y → x ≡ y
    →ℕ-inj _ = trustMe
      where open import Relation.Binary.PropositionalEquality.TrustMe

    help : _≡ₛ_ ⇒ _≡_
    help {x} {y} pr =
      begin
        x
      ≡⟨ sym (fromList∘toList x) ⟩
        []→ (→[] x)
      ≡⟨ cong []→ (aux pr) ⟩
        []→ (→[] y)
      ≡⟨ fromList∘toList y ⟩
        y
      ∎
      where
        aux : {xs ys : List Char} → Pointwise (_≡_ on →ℕ) xs ys → xs ≡ ys
        aux = Pointwise.rec (λ {xs} {ys} _ → xs ≡ ys) (cong₂ _∷_ ∘ →ℕ-inj) refl

    ≺-trichotomous : Trichotomous _≡_ _≺ₛ_
    ≺-trichotomous x y with compare STO⟨Script⟩′ x y
    ... | tri< a ¬b ¬c = tri< a (λ{ refl → ¬c a }) ¬c
    ... | tri≈ ¬a b ¬c = tri≈ ¬a (help b) ¬c
    ... | tri> ¬a ¬b c = tri> ¬a (λ{ refl → ¬a c }) c

module STO⟦Script⟧ = Sets STO⟨Script⟩

Set⟨Script⟩ : Set
Set⟨Script⟩ = ⟨Set⟩' (const ⊤)
  where open STO⟦Script⟧

-------------------------------------------------------------------
--  Transaction output references.

data _≺ₒᵤₜ_ : Rel TxOutputRef 0ℓ where

  ≺id : ∀ {t t′ : TxOutputRef}
    → id t < id t′
      -----------
    → t ≺ₒᵤₜ t′

  ≡id : ∀ {t t′ : TxOutputRef}
    → id t ≡ id t′
    → index t < index t′
      ------------------
    → t ≺ₒᵤₜ t′

STO⟨TxOutputRef⟩ : IsStrictTotalOrder _≡_ _≺ₒᵤₜ_
STO⟨TxOutputRef⟩ =
  record
    { isEquivalence = ≡-isEquivalence
    ; trans         = ≺-trans
    ; compare       = ≺-trichotomous
    }

  where
    ≺-trans : Transitive _≺ₒᵤₜ_
    ≺-trans (≺id i<j)      (≺id j<k)      = ≺id (<-trans i<j j<k)
    ≺-trans (≺id i<j)      (≡id refl j<k) = ≺id i<j
    ≺-trans (≡id refl i<j) (≺id j<k)      = ≺id j<k
    ≺-trans (≡id refl i<j) (≡id refl j<k) = ≡id refl (<-trans i<j j<k)

    ≺-trichotomous : Trichotomous _≡_ _≺ₒᵤₜ_
    ≺-trichotomous x y with compare STO⟨ℕ⟩ (id x) (id y)
    ... | tri≈ ¬x≺y  refl ¬x>y with compare STO⟨ℕ⟩ (index x) (index y)
    ...     | tri<  i≺j ¬i≡j ¬j>i
            = tri< (≡id refl i≺j)
                   (λ{ refl → ¬j>i i≺j })
                   λ{ (≺id y≺y) → 1+n≰n y≺y
                    ; (≡id _ j<i) → ¬j>i j<i }

    ...     | tri≈ ¬i≺j refl ¬j>i
            = tri≈ (λ{ (≺id x) → ¬x>y x
                     ; (≡id x x₁) → ¬j>i x₁ })
                   refl
                   λ{ (≺id x) → ¬x>y x
                    ; (≡id x x₁) → ¬j>i x₁ }

    ...     | tri> ¬i≺j ¬i≡j  j>i
            = tri> (λ{ (≺id x) → ¬x>y x
                     ; (≡id x x₁) → ¬i≺j x₁ })
                   (λ{ refl → ¬i≡j refl })
                   (≡id refl j>i)

    ≺-trichotomous x y
      | tri<  x≺y ¬x≡y ¬x>y
      = tri< (≺id x≺y)
             (λ z → ¬x≡y (cong id z))
             (λ{ (≺id y≺x)   → ¬x>y y≺x
               ; (≡id y≡x _) → ¬x≡y (sym y≡x) })

    ≺-trichotomous x y
      | tri> ¬x≺y ¬x≡y  x>y
      = tri> (λ{ (≺id x≺y)   → ¬x≺y x≺y
               ; (≡id x≡y _) → ¬x≡y x≡y })
             (λ z → ¬x≡y (cong id z))
             (≺id x>y)

module STO⟦TxOutputRef⟧ = Sets STO⟨TxOutputRef⟩

Set⟨TxOutputRef⟩ : Set
Set⟨TxOutputRef⟩ = ⟨Set⟩' (const ⊤)
  where open STO⟦TxOutputRef⟧

-------------------------------------------------------------------
-- Transaction inputs.

data _≺ᵢₙ_ : Rel TxInput 0ℓ where

  ≺out : ∀ {t t′ : TxInput}
    → outputRef t ≺ₒᵤₜ outputRef t′
      -----------------------------
    → t ≺ᵢₙ t′

  ≺val : ∀ {t t′ : TxInput}
    → outputRef t ≡ outputRef t′
    → validator t ≺ₛ validator t′
      ----------------------------------
    → t ≺ᵢₙ t′

  ≺red : ∀ {t t′ : TxInput}
    → outputRef t ≡ outputRef t′
    → validator t ≡ validator t′
    → redeemer t ≺ₛ redeemer t′
      ----------------------------------
    → t ≺ᵢₙ t′

STO⟨TxInput⟩ : IsStrictTotalOrder _≡_ _≺ᵢₙ_
STO⟨TxInput⟩ =
  record
    { isEquivalence = ≡-isEquivalence
    ; trans         = λ {i} {j} {k} → ≺-trans {i} {j} {k}
    ; compare       = ≺-trichotomous
    }

  where
    ≺-trans : Transitive _≺ᵢₙ_
    ≺-trans (≺out i<j) (≺out j<k)           = ≺out (sto-trans STO⟨TxOutputRef⟩ i<j j<k)
    ≺-trans (≺out i<j) (≺val refl j<k)      = ≺out i<j
    ≺-trans (≺out i<j) (≺red refl refl j<k) = ≺out i<j

    ≺-trans (≺val refl i<j) (≺out j<k)                       = ≺out j<k
    ≺-trans {i} {j} {k} (≺val refl i<j) (≺val refl j<k)      = ≺val refl
      (sto-trans STO⟨Script⟩ {validator i} {validator j} {validator k} i<j j<k)
    ≺-trans {i} {j} {k} (≺val refl i<j) (≺red refl refl j<k) = ≺val refl i<j

    ≺-trans (≺red refl refl i<j) (≺out j<k)                       = ≺out j<k
    ≺-trans (≺red refl refl i<j) (≺val refl j<k)                  = ≺val refl j<k
    ≺-trans {i} {j} {k} (≺red refl refl i<j) (≺red refl refl j<k) = ≺red refl refl
      (sto-trans STO⟨Script⟩ {redeemer i} {redeemer j} {redeemer k} i<j j<k )

    ≺-trichotomous : Trichotomous _≡_ _≺ᵢₙ_
    ≺-trichotomous x y with compare STO⟨TxOutputRef⟩ (outputRef x) (outputRef y)
    ... | tri≈ ¬a0 refl ¬c0
        with compare STO⟨Script⟩ (validator x) (validator y)
           | compare STO⟨Script⟩ (redeemer x)  (redeemer y)
    ...    | tri≈ ¬a refl ¬c | tri≈ ¬a′ refl ¬c′
           = tri≈ (λ{ (≺out c) → ¬c0 c ; (≺val _ c) → ¬c c ; (≺red _ _ c) → ¬c′ c })
                  refl
                  (λ{ (≺out c) → ¬c0 c ; (≺val _ c) → ¬c c ; (≺red _ _ c) → ¬c′ c })
    ...    | tri≈ ¬a refl ¬c | tri< a′  ¬b′  ¬c′
           = tri< (≺red refl refl a′)
                  (λ{ refl → ¬c′ a′ })
                  (λ{ (≺out c) → ¬c0 c ; (≺val _ c) → ¬c c ; (≺red _ _ c) → ¬c′ c })

    ...    | tri≈ ¬a refl ¬c | tri> ¬a′ ¬b′   c′
           = tri> (λ{ (≺out c) → ¬c0 c ; (≺val _ c) → ¬c c ; (≺red _ _ a) → ¬a′ a })
                  (λ{ refl → ¬b′ refl })
                  (≺red refl refl c′)
    ...    | tri< a  ¬b   ¬c | _
           = tri< (≺val refl a)
                  (λ{ refl → ¬c a })
                  (λ{ (≺out c) → ¬c0 c ; (≺val _ c) → ¬c c ; (≺red _ b _) → ¬b (sym b) })
    ...    | tri> ¬a ¬b    c | _
           = tri> (λ{ (≺out c) → ¬c0 c ; (≺val _ a) → ¬a a ; (≺red _ b  _) → ¬b b })
                  (λ{ refl → ¬b refl })
                  (≺val refl c)

    ≺-trichotomous x y
      | tri< a ¬b ¬c
      = tri< (≺out a)
             (λ{ refl → ¬c a })
             (λ{ (≺out c) → ¬c c ; (≺val b _) → ¬b (sym b) ; (≺red b _ _) → ¬b (sym b) })

    ≺-trichotomous x y
      | tri> ¬a ¬b c
      = tri> (λ{ (≺out a) → ¬a a ; (≺val b _) → ¬b b ; (≺red b _ _) → ¬b b })
             (λ{ refl → ¬a c })
             (≺out c)

module STO⟦TxInput⟧ = Sets STO⟨TxInput⟩

Set⟨TxInput⟩ : Set
Set⟨TxInput⟩ = ⟨Set⟩' (const ⊤)
  where open STO⟦TxInput⟧

