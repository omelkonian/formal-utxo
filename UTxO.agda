module UTxO where

open import Function
  using (const; _∘_; _on_; _∋_)
open import Level
  using (Level; 0ℓ)
open import Data.Bool
  using (Bool; true; false; T)
open import Data.Nat
  using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s; _<_; _>_)
open import Data.Nat.Properties
  using (<-trans; 1+n≰n; <-isStrictTotalOrder; _≟_; <-cmp)
open import Data.Unit
  using (⊤)
open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.Product
  using (_×_)
  renaming (_,_ to ⟨_,_⟩)
open import Data.List
  using (List; []; _∷_; map; boolFilter; zip; upTo; _++_; length; sum)
open import Data.String
  using (String)

import Data.AVL.Sets as Sets

open import Relation.Binary
  using (Tri; StrictTotalOrder; _⇒_; _=[_]⇒_)

import Data.List.Relation.Lex.Strict as StrictLex

import Relation.Binary.Construct.On as On
open import Data.Char as Char
  using (Char)
open import Data.String
  using ()
  renaming (toList to stringToList)
open import Agda.Builtin.Char
  using (Char)
  renaming (primCharToNat to →ℕ)

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open Eq
  using (_≡_; refl; sym; trans; cong; cong₂)
  renaming (isEquivalence to ≡-isEquivalence)

open import Relation.Nullary
  using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality.TrustMe
  using (trustMe)
open import Relation.Binary
  using ( IsStrictTotalOrder; Rel; Transitive; Trichotomous; tri≈; tri<; tri>)
open IsStrictTotalOrder
  using (compare)
  renaming (trans to sto-trans)

------------------------------------------------------------------------
-- List utilities

_<$>_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → List A → List B
_<$>_ = map

sumValues : ∀ {A : Set} → (A → ℕ) → List A → ℕ
sumValues f xs = sum (f <$> xs)
syntax sumValues f xs = Σ[ f ∈ xs ]

------------------------------------------------------------------------
-- Set utilities

module _
  {A : Set} {_<_  : Rel A 0ℓ} {A-sto : IsStrictTotalOrder _≡_ _<_}
  where

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

  _─_ : Set⟨A⟩ → Set⟨A⟩ → Set⟨A⟩
  xs ─ ys = fromList (boolFilter (λ x → x ∈? ys) (toList xs))

  _∪_ : Set⟨A⟩ → Set⟨A⟩ → Set⟨A⟩
  xs ∪ ys = fromList (toList xs ++ toList ys)

------------------------------------------------------------------------
-- Basic Tx definitions

Address : Set
Address = ℕ

infix 9 _♯
postulate
  _♯ : ∀ {ℓ : Level} {A : Set ℓ} → A → Address

Value : Set
Value = ℕ

Id : Set
Id = ℕ

record State : Set where
  field
    height : ℕ

Script : Set
Script = String

postulate
  ⟦_⟧ᵥ : Script → (∀ {R : Set} → State → R → Bool)
  ⟦_⟧ᵣ : Script → (∀ {R : Set} → State → R)

record TxOutput : Set where
  field
    address : Address
    value   : Value
open TxOutput

record TxOutputRef : Set where
  field
    id    : Id
    index : ℕ
open TxOutputRef

record TxInput : Set where
  field
    outputRef : TxOutputRef
    validator : Script
    redeemer  : Script
open TxInput

------------------------------------------------------------------------
-- Module definitions of finite sets

STO⟨ℕ⟩ : IsStrictTotalOrder _≡_ _<_
STO⟨ℕ⟩ = <-isStrictTotalOrder

Set⟨ℕ⟩ : Set
Set⟨ℕ⟩ = ⟨Set⟩' (const ⊤)
  where open Sets STO⟨ℕ⟩

-------------------------------------------------------------------
≺→ℕ-trans : Transitive (_<_ on →ℕ)
≺→ℕ-trans {i} {j} {k} i<j j<k = On.transitive →ℕ _<_ <-trans {i} {j} {k} i<j j<k

STO⟨Char⟩ : IsStrictTotalOrder _≡_ (_<_ on →ℕ)
STO⟨Char⟩ =
  record { isEquivalence = ≡-isEquivalence
         ; trans = λ {i} {j} {k} i≺j j≺k → ≺→ℕ-trans {i} {j} {k} i≺j j≺k
         ; compare = ≺-trichotomous
         }

  where
    -- should be in stdlib
    →ℕ-inj : ∀ {x y} → →ℕ x ≡ →ℕ y → x ≡ y
    →ℕ-inj _ = trustMe
      where open import Relation.Binary.PropositionalEquality.TrustMe

    ≺-trichotomous : Trichotomous _≡_ (_<_ on →ℕ)
    ≺-trichotomous x y with <-cmp (→ℕ x) (→ℕ y)
    ... | tri< a ¬b ¬c = tri< a (λ z → ¬b (cong →ℕ z)) ¬c
    ... | tri≈ ¬a b ¬c = tri≈ ¬a (→ℕ-inj b) ¬c
    ... | tri> ¬a ¬b c = tri> ¬a (λ z → ¬b (cong →ℕ z)) c

STO⟨Script⟩ : StrictTotalOrder _ _ _
STO⟨Script⟩ =
  On.strictTotalOrder
    (StrictLex.<-strictTotalOrder Char.strictTotalOrder)
    stringToList

open import Data.List.Relation.Pointwise using (Pointwise)
open import Data.String
  using ()
  renaming (primStringToList to →[]; primStringFromList to []→)
open import Data.List.Relation.Lex.Core using (Lex)

_≡ₛ_ : Rel Script 0ℓ
_≡ₛ_ = Pointwise (_≡_ on →ℕ) on →[]

_≺ₛ_ : Rel Script 0ℓ
_≺ₛ_ = Lex ⊥ (_≡_ on →ℕ) (_<_ on →ℕ) on →[]

isSTO⟨Script⟩ : IsStrictTotalOrder {A = Script} _≡ₛ_ _≺ₛ_
isSTO⟨Script⟩ = StrictTotalOrder.isStrictTotalOrder STO⟨Script⟩

STO⟨Scr⟩ : IsStrictTotalOrder _≡_ _≺ₛ_
STO⟨Scr⟩ =
  record { isEquivalence = ≡-isEquivalence
         ; trans = λ {i} {j} {k} i≺j j≺k → ≺-trans {i} {j} {k} i≺j j≺k
         ; compare = ≺-trichotomous
         }

  where
    open import Relation.Binary using (IsEquivalence; _Respects₂_)
    open import Data.Nat.Properties using (<-resp₂-≡)
    open import Data.String.Unsafe using (fromList∘toList)
    import Data.List.Relation.Pointwise as Pointwise

    ≺-trans : Transitive _≺ₛ_
    ≺-trans = StrictLex.<-transitive
      (On.isEquivalence →ℕ ≡-isEquivalence)
      (On.respects₂ →ℕ _<_ _≡_ <-resp₂-≡)
      (λ {i} {j} {k} i<j j<k → ≺→ℕ-trans {i} {j} {k} i<j j<k)

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
    ≺-trichotomous x y with compare isSTO⟨Script⟩ x y
    ... | tri< a ¬b ¬c = tri< a (λ{ refl → ¬c a }) ¬c
    ... | tri≈ ¬a b ¬c = tri≈ ¬a (help b) ¬c
    ... | tri> ¬a ¬b c = tri> ¬a (λ{ refl → ¬a c }) c

Set⟨Script⟩ : Set
Set⟨Script⟩ = ⟨Set⟩' (const ⊤)
  where open Sets STO⟨Scr⟩

-------------------------------------------------------------------

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

Set⟨TxOutputRef⟩ : Set
Set⟨TxOutputRef⟩ = ⟨Set⟩' (const ⊤)
  where open Sets STO⟨TxOutputRef⟩

-------------------------------------------------------------------

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
    ; trans         = λ {i} {j} {k} i≺j j≺k → ≺-trans {i} {j} {k} i≺j j≺k
    ; compare       = ≺-trichotomous
    }

  where
    ≺-trans : Transitive _≺ᵢₙ_
    ≺-trans (≺out i<j) (≺out j<k)           = ≺out (sto-trans STO⟨TxOutputRef⟩ i<j j<k)
    ≺-trans (≺out i<j) (≺val refl j<k)      = ≺out i<j
    ≺-trans (≺out i<j) (≺red refl refl j<k) = ≺out i<j

    ≺-trans (≺val refl i<j) (≺out j<k)
      = ≺out j<k
    ≺-trans {i} {j} {k} (≺val refl i<j) (≺val refl j<k)
      = ≺val refl (sto-trans {0ℓ} {0ℓ} {0ℓ} {String} {_≡_} {_≺ₛ_}
             STO⟨Scr⟩ {validator i} {validator j} {validator k} i<j j<k)
    ≺-trans {i} {j} {k} (≺val refl i<j) (≺red refl refl j<k)
      = ≺val refl i<j

    ≺-trans (≺red refl refl i<j) (≺out j<k) = ≺out j<k
    ≺-trans (≺red refl refl i<j) (≺val refl j<k) = ≺val refl j<k
    ≺-trans {i} {j} {k} (≺red refl refl i<j) (≺red refl refl j<k)
      = ≺red refl refl (sto-trans
             STO⟨Scr⟩ {redeemer i} {redeemer j} {redeemer k} i<j j<k )

    ≺-trichotomous : Trichotomous _≡_ _≺ᵢₙ_
    ≺-trichotomous x y with compare STO⟨TxOutputRef⟩ (outputRef x) (outputRef y)
    ... | tri≈ ¬a0 refl ¬c0
        with compare STO⟨Scr⟩ (validator x) (validator y)
           | compare STO⟨Scr⟩ (redeemer x)  (redeemer y)
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


Set⟨TxInput⟩ : Set
Set⟨TxInput⟩ = ⟨Set⟩' (const ⊤)
  where open Sets STO⟨TxInput⟩

-------------------------------------------------------------------

record Tx : Set where
  field
    inputs  : Set⟨TxInput⟩
    outputs : List TxOutput
    forge   : Value
    fee     : Value
open Tx

Ledger : Set
Ledger = List Tx

txInputs : Tx → List TxInput
txInputs tx = toList (inputs tx)
  where open Sets STO⟨TxInput⟩

module _ where
  open Sets STO⟨TxOutputRef⟩

  unspentOutputsTx : Tx → Set⟨TxOutputRef⟩
  unspentOutputsTx tx = fromList (mkOutputRef <$> indices (outputs tx))
    where
      mkOutputRef : ℕ → TxOutputRef
      mkOutputRef index = record { id = tx ♯; index = index }

      indices : ∀ {A : Set} → List A → List ℕ
      indices xs = upTo (length xs)

  spentOutputsTx : Tx → Set⟨TxOutputRef⟩
  spentOutputsTx tx = fromList (outputRef <$> txInputs tx)

  unspentOutputs : Ledger → Set⟨TxOutputRef⟩
  unspentOutputs []         = ∅
  unspentOutputs (tx ∷ txs) = (unspentOutputs txs ─ spentOutputsTx tx)
                            ∪ (unspentOutputsTx tx)

------------------------------------------------------------------------
-- Tx utilities

lookupTx : Ledger → TxOutputRef → Tx
lookupTx (t ∷ ts) out with t ♯ ≟ id out
... | yes _ = t
... | no  _ = lookupTx ts out
lookupTx [] _ = ⊥-elim impossible
  where postulate impossible : ⊥

lookupOutput : Ledger → TxOutputRef → TxOutput
lookupOutput l out = lookupOutputTx (outputs (lookupTx l out)) (index out)
  where
    lookupOutputTx : List TxOutput → ℕ → TxOutput
    lookupOutputTx (o ∷ os) zero    = o
    lookupOutputTx (_ ∷ os) (suc i) = lookupOutputTx os i
    lookupOutputTx []       _       = ⊥-elim impossible
      where postulate impossible : ⊥

lookupValue : Ledger → TxInput → Value
lookupValue l input = value (lookupOutput l (outputRef input))

------------------------------------------------------------------------
-- Properties

record IsValidTx (tx : Tx) (l : Ledger) : Set₁ where
  field
    hasValidReferences  :
      ∀[ i ∈ inputs tx ]
        outputRef i ∈ unspentOutputs l

    preservesValues     :
      forge tx + Σ[ lookupValue l ∈ txInputs tx ]
        ≡
      fee tx + Σ[ value ∈ outputs tx ]

    noDoubleSpending    :
      ∣ inputs tx ∣ ≡ length (outputRef <$> txInputs tx)

    allInputsValidate   : {R : Set} →
      ∀[ i ∈ inputs tx ]
        ∀ (st : State) →
          let redeemed  = ⟦ redeemer i ⟧ᵣ st
              validated = ⟦ validator i ⟧ᵥ st (R ∋ redeemed)
          in  T validated

    validateValidHashes :
      ∀[ i ∈ inputs tx ]
        (validator i) ♯ ≡ address (lookupOutput l (outputRef i))

