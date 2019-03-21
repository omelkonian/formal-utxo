{-# OPTIONS --allow-unsolved-metas #-}
open import Level    using (0ℓ)
open import Function using (_∘_; _∋_; flip)

open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (⊤; tt)
open import Data.Bool     using (Bool; T)
open import Data.Product  using (proj₁)
open import Data.Nat      using (ℕ; zero; suc; _+_; _<_; _≟_)
open import Data.Fin      using (Fin; toℕ; fromℕ≤)
open import Data.List     using (List; []; _∷_; _∷ʳ_; [_]; length; sum; map)
open import Data.List.Any using (Any)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Rel; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; setoid)

open import Category.Functor       using (RawFunctor)
open import Data.List.Categorical  renaming (functor to listFunctor)
open import Data.List.Membership.Propositional using (_∈_; mapWith∈)

open import Utilities.Lists
open import Data.TYPE using (𝕌; el; _≟ᵤ_)
open import Types

module UTxO (addresses : List Address) where

------------------------------------------------------------------------
-- Transactions.

record TxOutput : Set₁ where
  field
    value   : Value
    address : Index addresses

    Data       : 𝕌
    dataScript : State → el Data

open TxOutput public

runValidation : (i : TxInput) → (o : TxOutput) → D i ≡ Data o → State → Bool
runValidation i o refl st = validator i st (value o) (redeemer i st) (dataScript o st)

record Tx : Set₁ where

  field
    inputs  : List TxInput -- T0D0: Set⟨TxInput⟩
    outputs : List TxOutput
    forge   : Value
    fee     : Value

open Tx public

Ledger : Set₁
Ledger = List Tx

module _ where
  open SETₒ

  unspentOutputsTx : Tx → Set⟨TxOutputRef⟩
  unspentOutputsTx tx = fromList (map ((tx ♯) indexed-at_) (indices (outputs tx)))

  spentOutputsTx : Tx → Set⟨TxOutputRef⟩
  spentOutputsTx tx = fromList (map outputRef (inputs tx))

  unspentOutputs : Ledger → Set⟨TxOutputRef⟩
  unspentOutputs []         = ∅
  unspentOutputs (tx ∷ txs) = unspentOutputs txs ─ spentOutputsTx tx
                            ∪ unspentOutputsTx tx

------------------------------------------------------------------------
-- Tx utilities.

open import Data.List.Membership.Setoid (setoid Tx) using (find)

lookupTx : (l : Ledger)
         → (out : TxOutputRef)
         → Any (λ tx → tx ♯ ≡ id out) l
         → Tx
lookupTx l out ∃tx≡id = proj₁ (find ∃tx≡id)

lookupOutput : (l : Ledger)
             → (out : TxOutputRef)
             → (∃tx≡id : Any (λ tx → tx ♯ ≡ id out) l)
             → index out < length (outputs (lookupTx l out ∃tx≡id))
             → TxOutput
lookupOutput l out ∃tx≡id index≤len =
  outputs (lookupTx l out ∃tx≡id) ‼ (fromℕ≤ {index out} index≤len)

lookupValue : (l : Ledger)
            → (input : TxInput)
            → (∃tx≡id : Any (λ tx → tx ♯ ≡ id (outputRef input)) l)
            → index (outputRef input) <
                length (outputs (lookupTx l (outputRef input) ∃tx≡id))
            → Value
lookupValue l input ∃tx≡id index≤len =
  value (lookupOutput l (outputRef input) ∃tx≡id index≤len)

------------------------------------------------------------------------
-- Properties.

record IsValidTx (tx : Tx) (l : Ledger) : Set₁ where

  field

    validTxRefs :
      ∀ i → i ∈ inputs tx →
        Any (λ t → t ♯ ≡ id (outputRef i)) l

    validOutputIndices :
      ∀ i → (i∈ : i ∈ inputs tx) →
        index (outputRef i) <
          length (outputs (lookupTx l (outputRef i) (validTxRefs i i∈)))

    validOutputRefs :
      ∀ i → i ∈ inputs tx →
        outputRef i SETₒ.∈′ unspentOutputs l

    validDataScriptTypes :
      ∀ i → (i∈ : i ∈ inputs tx) →
        D i ≡ Data (lookupOutput l (outputRef i) (validTxRefs i i∈) (validOutputIndices i i∈))

    -----------------------------------------------------------------------------------------

    preservesValues :
      forge tx + sum (mapWith∈ (inputs tx) λ {i} i∈ →
                   lookupValue l i (validTxRefs i i∈) (validOutputIndices i i∈))
        ≡
      fee tx + Σ[ value ∈ outputs tx ]

    noDoubleSpending :
      SETₒ.noDuplicates (map outputRef (inputs tx))

    allInputsValidate : -- {_≈_ : Rel State 0ℓ} →
      ∀ i → (i∈ : i ∈ inputs tx) →
        let
          out : TxOutput
          out = lookupOutput l (outputRef i) (validTxRefs i i∈) (validOutputIndices i i∈)
        in
          ∀ (st : State) →
            T (runValidation i out (validDataScriptTypes i i∈) st)

    validateValidHashes :
      ∀ i → (i∈ : i ∈ inputs tx) →
        let
          out : TxOutput
          out = lookupOutput l (outputRef i) (validTxRefs i i∈) (validOutputIndices i i∈)
        in
          toℕ (address out) ≡ (validator i) ♯

open IsValidTx public

-- List notation for constructing valid ledgers.
data ValidLedger : Ledger → Set₁ where

  ∙_∶-_ : (t : Tx)
       → .(IsValidTx t [])
       → ValidLedger [ t ]

  _⊕_∶-_ : ∀ {l}
         → ValidLedger l
         → (t : Tx)
         → .(IsValidTx t l)
         → ValidLedger (t ∷ l)

infixl 5 _⊕_∶-_



-- Decidable procedure for IsValidTx.
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary using (Decidable)
open import Data.List.Relation.Unary.Any using (Any; any; here; there)
open import Data.List.Membership.Propositional using (_∈_)


∀? : ∀ {ℓ ℓ′} {A : Set ℓ}
     → (xs : List A)
     → {P : (x : A) → (x∈ : x ∈ xs) → Set ℓ′}
     → (∀ x → (x∈ : x ∈ xs) → Dec (P x x∈))
     → Dec (∀ x → (x∈ : x ∈ xs) → P x x∈)
∀? []       P? = yes λ _ ()
∀? (x ∷ xs) P?
  with ∀? xs (λ x′ x∈ → P? x′ (there x∈))
... | no ¬p = no λ p → ¬p (λ x′ x∈ → p x′ (there x∈))
... | yes p′
  with P? x (here refl)
... | no ¬p = no (λ p → ¬p (p x (here refl)))
... | yes p = yes (λ { x′ (here refl) → p
                     ; x′ (there x∈)  → p′ x′ x∈
                     })

open import Data.Nat using (_<?_)
open import Data.Bool.Properties using (T?)

postulate
  ∀state? : ∀ {ℓ} {P : State → Set ℓ}
          → (∀ st → Dec (P st))
          → Dec (∀ (st : State) → P st)

isValidTx? : ∀ (tx : Tx) → (l : Ledger) → Dec (IsValidTx tx l)
isValidTx? tx l
    -- validTxRefs
  with ∀? (inputs tx) λ i _ →
         any (λ t → t ♯  ≟ id (outputRef i)) l
... | no ¬p = no (¬p ∘ validTxRefs)
... | yes v₁
  -- validOutputIndices
  with ∀? (inputs tx) λ i i∈ →
       index (outputRef i) <? length (outputs (lookupTx l (outputRef i) (v₁ i i∈)))
... | no ¬p = no (¬p ∘ λ valid x x∈ → {!!})-- {!validOutputIndices!})
... | yes v₂
  -- validOutputRefs
  with ∀? (inputs tx) λ i _ →
         outputRef i SETₒ.∈? SETₒ.list (unspentOutputs l)
... | no ¬p = no (¬p ∘ validOutputRefs)
... | yes v₃
  -- validDataScriptTypes
  with ∀? (inputs tx) λ i i∈ →
         D i ≟ᵤ Data (lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈))
... | no ¬p  = no (¬p ∘ {!validDataScriptTypes!})
... | yes v₄
  -- preservesValues
   with forge tx + sum (mapWith∈ (inputs tx) λ {i} i∈ →
                   lookupValue l i (v₁ i i∈) (v₂ i i∈))
          ≟
        fee tx + Σ[ value ∈ outputs tx ]
... | no ¬p = no (¬p ∘ {!preservesValues!})
... | yes v₅
  -- noDoubleSpending
  with SETₒ.noDuplicates? (map outputRef (inputs tx))
... | no ¬p = no (¬p ∘ noDoubleSpending)
... | yes v₆
  -- allInputsValidate
  with ∀? (inputs tx) λ i i∈ →
         let
           out : TxOutput
           out = lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈)
         in
           ∀state? λ st →
             T? (runValidation i out (v₄ i i∈) st)
... | no ¬p = no (¬p ∘ {!allInputsValidate!})
... | yes v₇
  -- validateValidHashes
  with ∀? (inputs tx) λ i i∈ →
         let
           out : TxOutput
           out = lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈)
         in
           toℕ (address out) ≟ (validator i) ♯
... | no ¬p = no (¬p ∘ {!validateValidHashes!})
... | yes v₈ = yes (record
                      { validTxRefs = v₁
                      ; validOutputIndices = v₂
                      ; validOutputRefs = v₃
                      ; validDataScriptTypes = v₄
                      ; preservesValues = v₅
                      ; noDoubleSpending = v₆
                      ; allInputsValidate = v₇
                      ; validateValidHashes = v₈
                      })
