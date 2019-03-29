open import Function using (_∘_; _∋_; flip; _$_)

open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (⊤; tt)
open import Data.Bool     using (Bool; T)
open import Data.Bool.Properties using (T?)
open import Data.Product  using (proj₁; ∃; ∃-syntax; Σ; Σ-syntax)
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

open import Utilities.Lists
open import Data.TYPE using (𝕌; el; _≟ᵤ_)
open import Types
open import Currency

module DecisionProcedure (addresses : List Address) where

open import UTxO addresses


∀? : ∀ {ℓ ℓ′} {A : Set ℓ}
     → (xs : List A)
     → {P : (x : A) (x∈ : x ∈ xs) → Set ℓ′}
     → (∀ x → (x∈ : x ∈ xs) → Dec (P x x∈))
     → Dec (∀ x x∈ → P x x∈)
∀? []       P? = yes λ _ ()
∀? (x ∷ xs) P?
  with ∀? xs (λ x′ x∈ → P? x′ (there x∈))
... | no ¬p = no λ p → ¬p (λ x′ x∈ → p x′ (there x∈))
... | yes p′
  with P? x (here refl)
... | no ¬p = no λ p → ¬p (p x (here refl))
... | yes p = yes λ { x′ (here refl) → p
                    ; x′ (there x∈)  → p′ x′ x∈
                    }

validTxRefs? : ∀ (tx : Tx) (l : Ledger)
  → Dec (∀ i → i ∈ inputs tx → Any (λ t → t ♯ ≡ id (outputRef i)) l)
validTxRefs? tx l =
  ∀? (inputs tx) λ i _ →
    any (λ t → t ♯ ≟ id (outputRef i)) l

validOutputIndices? : ∀ (tx : Tx) (l : Ledger)
  → (v₁ : ∀ i → i ∈ inputs tx → Any (λ t → t ♯ ≡ id (outputRef i)) l)
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
  → (v₁ : ∀ i → i ∈ inputs tx → Any (λ t → t ♯ ≡ id (outputRef i)) l)
  → (v₂ : ∀ i → (i∈ : i ∈ inputs tx) →
            index (outputRef i) < length (outputs (lookupTx l (outputRef i) (v₁ i i∈))))
  → Dec (∀ i → (i∈ : i ∈ inputs tx) →
           D i ≡ Data (lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈)))
validDataScriptTypes? tx l v₁ v₂ =
  ∀? (inputs tx) λ i i∈ →
    D i ≟ᵤ Data (lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈))

-- preservesValues? : ∀ (tx : Tx) (l : Ledger)
--   → (v₁ : ∀ i → i ∈ inputs tx → Any (λ t → t ♯ ≡ id (outputRef i)) l)
--   → (v₂ : ∀ i → (i∈ : i ∈ inputs tx) →
--             index (outputRef i) < length (outputs (lookupTx l (outputRef i) (v₁ i i∈))))
--   → Dec (forge tx +ᶜ sumᶜ (mapWith∈ (inputs tx) λ {i} i∈ →
--                              lookupValue l i (v₁ i i∈) (v₂ i i∈))
--            ≡
--          fee tx +ᶜ sumᶜ (map value (outputs tx)))
-- preservesValues? tx l v₁ v₂ =
--   forge tx +ᶜ sumᶜ (mapWith∈ (inputs tx) λ {i} i∈ →
--                       lookupValue l i (v₁ i i∈) (v₂ i i∈))
--     ≟ -- NB: no decidable equality for AVL trees
--   fee tx +ᶜ sumᶜ (map value (outputs tx))

noDoubleSpending? : ∀ (tx : Tx) (l : Ledger)
  → Dec (SETₒ.noDuplicates (map outputRef (inputs tx)))
noDoubleSpending? tx l =
  SETₒ.noDuplicates? (map outputRef (inputs tx))

allInputsValidate? : ∀ (tx : Tx) (l : Ledger)
  → (v₁ : ∀ i → i ∈ inputs tx → Any (λ t → t ♯ ≡ id (outputRef i)) l)
  → (v₂ : ∀ i → (i∈ : i ∈ inputs tx) →
            index (outputRef i) < length (outputs (lookupTx l (outputRef i) (v₁ i i∈))))
  → (v₄ : ∀ i → (i∈ : i ∈ inputs tx) →
            D i ≡ Data (lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈)))
  → ∀ (st : State) -- NB: cannot completely decide the proposition, hence the lifting of the ∀
  → Dec (∀ i → (i∈ : i ∈ inputs tx) →
           let
             out = lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈)
             ptx = mkPendingTx l tx v₁ v₂
           in
             T (runValidation ptx i out (v₄ i i∈) st))
allInputsValidate? tx l v₁ v₂ v₄ st =
  ∀? (inputs tx) λ i i∈ →
    let
      out = lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈)
      ptx = mkPendingTx l tx v₁ v₂
    in
      T? (runValidation ptx i out (v₄ i i∈) st)

validateValidHashes? : ∀ (tx : Tx) (l : Ledger)
  → (v₁ : ∀ i → i ∈ inputs tx → Any (λ t → t ♯ ≡ id (outputRef i)) l)
  → (v₂ : ∀ i → (i∈ : i ∈ inputs tx) →
            index (outputRef i) < length (outputs (lookupTx l (outputRef i) (v₁ i i∈))))
  → Dec (∀ i → (i∈ : i ∈ inputs tx) →
           let
             out : TxOutput
             out = lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈)
           in
             toℕ (address out) ≡ (validator i) ♯)
validateValidHashes? tx l v₁ v₂ =
  ∀? (inputs tx) λ i i∈ →
    let
      out : TxOutput
      out = lookupOutput l (outputRef i) (v₁ i i∈) (v₂ i i∈)
    in
      toℕ (address out) ≟ (validator i) ♯

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
  with allInputsValidate? tx l v₁ v₂ v₄ (record {height = 0})
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

{-
_→-dec_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → Dec A → Dec B → Dec (A → B)
_     →-dec yes y  =  yes (λ _ → y)
no ¬x →-dec _      =  yes (λ x → ⊥-elim (¬x x))
yes x →-dec no ¬y  =  no (λ f → ¬y (f x))

_→?_ : ∀ {A : Set} {B : A → Set}
     → Dec A
     → (∀ a → Dec (B a))
     → Dec ((a : A) → B a)
yes a →? b? with b? a
... | yes p = yes (λ a₁ → {!!})
... | no ¬p = no (λ b → ¬p (b a))
no ¬a →? _ = yes (λ a → ⊥-elim (¬a a))

∀state? : ∀ {ℓ} {P : State → Set ℓ}
        → (∀ st → Dec (P st))
        → Dec (∀ (st : State) → P st)
∀state? P?
  with P? (record { height = 0 })
... | no ¬p = no λ p → ¬p (p (record { height = 0 }))
... | yes p = yes (λ { record { height = 0 } → p ; record { height = (suc n) } → {!!} })
-}
