{-# OPTIONS --rewriting #-}
{- NB: REWRITE rules may be useful while deciding on something that requires them,
e.g. calls to postulated hash function _♯. -}
open import Function using (_∘_; _∋_; flip; _$_)

open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (⊤; tt)
open import Data.Bool     using (Bool; T)
open import Data.Bool.Properties using (T?)
open import Data.Product  using (proj₁; ∃; ∃-syntax; Σ; Σ-syntax; _,_)
open import Data.Nat      using (ℕ; zero; suc; _+_; _<_; _≟_; _<?_)
open import Data.Fin      using (Fin; toℕ; fromℕ≤)
open import Data.List     using (List; []; _∷_; _∷ʳ_; [_]; length; sum; map)
open import Data.List.Any using (Any)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Rel; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; setoid)

open import Category.Functor       using (RawFunctor)
open import Data.List.Categorical  renaming (functor to listFunctor)
open import Data.List.Membership.Propositional using (_∈_; mapWith∈)

open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary using (Decidable)
open import Data.List.Relation.Unary.Any using (Any; any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import UTxO.Types
open import Hashing.Base
open import Hashing.Types    using (_♯ᵢ)
open import Hashing.MetaHash using (_♯)

module UTxO.DecisionProcedure
  (Address : Set)
  (_♯ₐ : Hash Address)
  (_≟ₐ_ : Decidable {A = Address} _≡_)
  where


open import UTxO.Validity Address _♯ₐ _≟ₐ_

∀? : ∀ {ℓ ℓ′} {A : Set ℓ}
  → (xs : List A)
  → {P : (x : A) (x∈ : x ∈ xs) → Set ℓ′}
  → (∀ x → (x∈ : x ∈ xs) → Dec (P x x∈))
  → Dec (∀ x x∈ → P x x∈)
∀? []       P? = yes λ _ ()
∀? (x ∷ xs) P? with ∀? xs (λ x′ x∈ → P? x′ (there x∈))
... | no ¬p    = no λ p → ¬p (λ x′ x∈ → p x′ (there x∈))
... | yes p′   with P? x (here refl)
... | no ¬p    = no λ p → ¬p (p x (here refl))
... | yes p    = yes λ { x′ (here refl) → p
                       ; x′ (there x∈)  → p′ x′ x∈
                       }

∃? : ∀ {ℓ ℓ′} {A : Set ℓ}
  → (xs : List A)
  → {P : (x : A) (x∈ : x ∈ xs) → Set ℓ′}
  → (∀ x → (x∈ : x ∈ xs) → Dec (P x x∈))
  → Dec (∃[ x ] ∃ λ (x∈ : x ∈ xs) → P x x∈)
∃? []  P?               = no λ { (x , () , p) }
∃? (x ∷ xs) P?          with P? x (here refl)
... | yes p             = yes (x , here refl , p)
... | no ¬p             with ∃? xs (λ x′ x∈ → P? x′ (there x∈))
... | yes (x′ , x∈ , p) = yes (x′ , there x∈ , p)
... | no ¬pp            = no λ { (x′ , here refl , p) → ¬p p
                               ; (x′ , there x∈ , p) → ¬pp (x′ , x∈ , p)
                               }

validTxRefs? : ∀ (tx : Tx) (l : Ledger)
  → Dec (∀ i → i ∈ inputs tx → Any (λ t → t ♯ₜₓ ≡ id (outputRef i)) l)
validTxRefs? tx l =
  ∀? (inputs tx) λ i _ →
    any (λ t → t ♯ₜₓ ≟ id (outputRef i)) l

validOutputIndices? : ∀ (tx : Tx) (l : Ledger)
  → (v₁ : ∀ i → i ∈ inputs tx → Any (λ t → t ♯ₜₓ ≡ id (outputRef i)) l)
  → Dec (∀ i → (i∈ : i ∈ inputs tx) →
           index (outputRef i) < length (outputs (lookupTx l (outputRef i) (v₁ i i∈))))
validOutputIndices? tx l v₁ =
  ∀? (inputs tx) λ i i∈ →
    index (outputRef i) <? length (outputs (lookupTx l (outputRef i) (v₁ i i∈)))

validOutputRefs? : ∀ (tx : Tx) (l : Ledger)
  → Dec (∀ i → i ∈ inputs tx → outputRef i SETₒ.∈′ unspentOutputs l)
validOutputRefs? tx l =
  ∀? (inputs tx) λ i _ →
    outputRef i SETₒ.∈? SETₒ.list (unspentOutputs l)

validDataScriptTypes? : ∀ (tx : Tx) (l : Ledger)
  → (v₁ : ∀ i → i ∈ inputs tx → Any (λ t → t ♯ₜₓ ≡ id (outputRef i)) l)
  → (v₂ : ∀ i → (i∈ : i ∈ inputs tx) →
            index (outputRef i) < length (outputs (lookupTx l (outputRef i) (v₁ i i∈))))
  → Dec (∀ i → (i∈ : i ∈ inputs tx) →
           D i ≡ Data (lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈)))
validDataScriptTypes? tx l v₁ v₂ =
  ∀? (inputs tx) λ i i∈ →
    D i ≟ᵤ Data (lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈))

preservesValues? : ∀ (tx : Tx) (l : Ledger)
  → (v₁ : ∀ i → i ∈ inputs tx → Any (λ t → t ♯ₜₓ ≡ id (outputRef i)) l)
  → (v₂ : ∀ i → (i∈ : i ∈ inputs tx) →
            index (outputRef i) < length (outputs (lookupTx l (outputRef i) (v₁ i i∈))))
  → Dec (forge tx +ᶜ sumᶜ (mapWith∈ (inputs tx) λ {i} i∈ → lookupValue l i (v₁ i i∈) (v₂ i i∈))
           ≡
         fee tx +ᶜ sumᶜ (map value (outputs tx)))
preservesValues? tx l v₁ v₂ =
  forge tx +ᶜ sumᶜ (mapWith∈ (inputs tx) λ {i} i∈ → lookupValue l i (v₁ i i∈) (v₂ i i∈))
    ≟ᶜ
  fee tx +ᶜ sumᶜ (map value (outputs tx))

noDoubleSpending? : ∀ (tx : Tx) (l : Ledger)
  → Dec (SETₒ.Unique (map outputRef (inputs tx)))
noDoubleSpending? tx l =
  SETₒ.unique? (map outputRef (inputs tx))

allInputsValidate? : ∀ (tx : Tx) (l : Ledger)
  → (v₁ : ∀ i → i ∈ inputs tx → Any (λ t → t ♯ₜₓ ≡ id (outputRef i)) l)
  → (v₂ : ∀ i → (i∈ : i ∈ inputs tx) →
            index (outputRef i) < length (outputs (lookupTx l (outputRef i) (v₁ i i∈))))
  → (v₄ : ∀ i → (i∈ : i ∈ inputs tx) →
            D i ≡ Data (lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈)))
  → Dec (∀ i → (i∈ : i ∈ inputs tx) →
           let out = lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈)
               ptx = mkPendingTx l tx v₁ v₂
           in T (runValidation ptx i out (v₄ i i∈) (getState l)))
allInputsValidate? tx l v₁ v₂ v₄ =
  ∀? (inputs tx) λ i i∈ →
    let out = lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈)
        ptx = mkPendingTx l tx v₁ v₂
    in T? (runValidation ptx i out (v₄ i i∈) (getState l))

validateValidHashes? : ∀ (tx : Tx) (l : Ledger)
  → (v₁ : ∀ i → i ∈ inputs tx → Any (λ t → t ♯ₜₓ ≡ id (outputRef i)) l)
  → (v₂ : ∀ i → (i∈ : i ∈ inputs tx) →
            index (outputRef i) < length (outputs (lookupTx l (outputRef i) (v₁ i i∈))))
  → Dec (∀ i → (i∈ : i ∈ inputs tx) →
           let out : TxOutput
               out = lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈)
           in (address out) ♯ₐ ≡ (validator i) ♯)
validateValidHashes? tx l v₁ v₂ =
  ∀? (inputs tx) λ i i∈ →
    let out : TxOutput
        out = lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈)
    in (address out) ♯ₐ ≟ (validator i) ♯

forging? : ∀ (tx : Tx) (l : Ledger)
  → (v₁ : ∀ i → i ∈ inputs tx → Any (λ t → t ♯ₜₓ ≡ id (outputRef i)) l)
  → (v₂ : ∀ i → (i∈ : i ∈ inputs tx) →
            index (outputRef i) < length (outputs (lookupTx l (outputRef i) (v₁ i i∈))))
  → Dec (∀ c → c ∈ keys (forge tx) →
           ∃[ i ] ∃ λ (i∈ : i ∈ inputs tx) →
             let out = lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈)
             in (address out) ♯ₐ ≡ c)
forging? tx l v₁ v₂ =
  ∀? (keys (forge tx)) λ c _ →
    ∃? (inputs tx) λ i i∈ →
       let out = lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈)
       in (address out) ♯ₐ ≟ c

{-
isValidTx? : ∀ (tx : Tx) → (l : Ledger) → Dec (IsValidTx tx l)
isValidTx? tx l
  with validTxRefs? tx l
... | no ¬p = no (¬p ∘ validTxRefs)
... | yes v₁
  with validOutputIndices? tx l v₁
... | no ¬p = no λ valid → ¬p (λ v x → {!validOutputIndices valid!})
... | yes v₂
  with validOutputRefs? tx l
... | no ¬p = no (¬p ∘ validOutputRefs)
... | yes v₃
  with validDataScriptTypes? tx l v₁ v₂
... | no ¬p  = no (¬p ∘ {!validDataScriptTypes!})
... | yes v₄
   with preservesValues? tx l v₁ v₂
... | no ¬p = no (¬p ∘ {!preservesValues!})
... | yes v₅
  with noDoubleSpending? tx l
... | no ¬p = no (¬p ∘ noDoubleSpending)
... | yes v₆
  with allInputsValidate? tx l v₁ v₂ v₄
... | no ¬p = no (¬p ∘ {!allInputsValidate!})
... | yes v₇
  with validateValidHashes? tx l v₁ v₂
... | no ¬p = no (¬p ∘ {!validateValidHashes!})
... | yes v₈ = yes (record
                      { validTxRefs          = v₁
                      ; validOutputIndices   = v₂
                      ; validOutputRefs      = v₃
                      ; validDataScriptTypes = v₄
                      ; preservesValues      = v₅
                      ; noDoubleSpending     = v₆
                      ; allInputsValidate    = {!!}
                      ; validateValidHashes  = v₈
                      })
-}
