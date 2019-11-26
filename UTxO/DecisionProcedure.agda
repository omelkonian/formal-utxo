open import Function using (_∘_; _∋_; flip; _$_)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (Bool; T)
open import Data.Product using (proj₁; ∃; ∃-syntax; Σ; Σ-syntax; _,_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _<_; _≟_; _<?_)
open import Data.Fin     using (Fin; toℕ; fromℕ≤)
open import Data.List    using (List; []; _∷_; _∷ʳ_; [_]; length; sum; map)

open import Data.Bool.Properties using (T?)

open import Data.List.Membership.Propositional            using (_∈_; mapWith∈)
open import Data.List.Relation.Unary.Any                  using (Any; any; here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

open import Relation.Nullary                      using (Dec; ¬_; yes; no)
open import Relation.Nullary.Decidable            using (True; toWitness)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; setoid)

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types    using (_♯ᵢ)
open import UTxO.Hashing.MetaHash using (_♯)
open import UTxO.Types

module UTxO.DecisionProcedure
  (Address : Set)
  (_♯ₐ : Hash Address)
  (_≟ₐ_ : Decidable {A = Address} _≡_)
  where

open import UTxO.Ledger      Address _♯ₐ _≟ₐ_
open import UTxO.TxUtilities Address _♯ₐ _≟ₐ_
open import UTxO.Hashing.Tx  Address _♯ₐ _≟ₐ_ using (_♯ₜₓ)
open import UTxO.Validity    Address _♯ₐ _≟ₐ_

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
  → Dec (Unique (map outputRef (inputs tx)))
noDoubleSpending? tx l =
  SETₒ.unique? (map outputRef (inputs tx))

allInputsValidate? : ∀ (tx : Tx) (l : Ledger)
  → Dec (∀ i → (i∈ : i ∈ inputs tx) →
           T (runValidation (getState l) i))
allInputsValidate? tx l =
  ∀? (inputs tx) λ i i∈ →
    T? (runValidation (getState l) i)

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

infixl 5 _⊕_
_⊕_ : ∀ {l}
  → ValidLedger l
  → (tx : Tx)
  → {p₁ : True (validTxRefs? tx l)}
  → {p₂ : True (validOutputIndices? tx l (toWitness p₁))}
  → {p₃ : True (validOutputRefs? tx l)}
  → {p₄ : True (preservesValues? tx l (toWitness p₁) (toWitness p₂))}
  → {p₅ : True (noDoubleSpending? tx l)}
  → {p₆ : True (allInputsValidate? tx l)}
  → {p₇ : True (validateValidHashes? tx l (toWitness p₁) (toWitness p₂))}
  → ValidLedger (tx ∷ l)
(vl ⊕ tx) {p₁ = p₁} {p₂} {p₃} {p₄} {p₅} {p₆} {p₇}
  = vl ⊕ tx ∶- record { validTxRefs          = toWitness p₁
                      ; validOutputIndices   = toWitness p₂
                      ; validOutputRefs      = toWitness p₃
                      ; preservesValues      = toWitness p₄
                      ; noDoubleSpending     = toWitness p₅
                      ; allInputsValidate    = toWitness p₆
                      ; validateValidHashes  = toWitness p₇ }
