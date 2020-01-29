open import Function using (_∘_; _∋_; flip; _$_)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (Bool; T)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ-syntax; map₁)
open import Data.Maybe using (Maybe;nothing;just;_>>=_) renaming (map to _<$>_)
open import Relation.Nullary using (yes;no)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Nat     using (ℕ; zero; suc; _+_; _<_) renaming (_≟_ to _≟ℕ_)
open import Data.Fin     using (Fin; toℕ; fromℕ<)
open import Data.Maybe   using (nothing;maybe)
open import Data.List    using (List; []; _∷_; length; map; _++_; filter)

open import Data.List.Membership.Propositional            using (_∈_; mapWith∈; find)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁻; ∈-filter⁻)
open import Data.List.Relation.Unary.Any as Any           using (Any; here; there)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists using (indices; _‼_)

open import UTxO.Hashing.Base
open import UTxO.Hashing.MetaHash using (_♯)

module UTxO.TxUtilities
  (Address : Set)
  (_♯ₐ : Hash Address)
  (_≟ₐ_ : Decidable {A = Address} _≡_)
  where

open import UTxO.Value      Address _♯ₐ _≟ₐ_
open import UTxO.Types      Address _♯ₐ _≟ₐ_
open import UTxO.Ledger     Address _♯ₐ _≟ₐ_
open import UTxO.Hashing.Tx Address _♯ₐ _≟ₐ_
open import UTxO.Hashing.Types Address _♯ₐ _≟ₐ_


record UTXO : Set where
  field
    outRef   : TxOutputRef
    out      : TxOutput
    prevTx   : Tx

open UTXO public

utxo : Ledger → List UTXO
utxo []       = []
utxo (tx ∷ l) = filter ((SETₒ._∉? map outputRef (inputs tx)) ∘ outRef) (utxo l)
             ++ mapWith∈ (outputs tx) λ {out} out∈ →
                  record { outRef   = (tx ♯ₜₓ) indexed-at toℕ (Any.index out∈)
                         ; out      = out
                         ; prevTx   = tx }

mapWith∈-∀ : ∀ {A B : Set} {xs : List A}  {f : ∀ {x : A} → x ∈ xs → B} {P : B → Set}
  → (∀ {x} x∈ → P (f {x} x∈))
  → (∀ {y} → y ∈ mapWith∈ xs f → P y)
mapWith∈-∀ {xs = x ∷ xs} ∀P {y} (here px)  rewrite px = ∀P (Any.here refl)
mapWith∈-∀ {xs = x ∷ xs} ∀P {y} (there y∈) = mapWith∈-∀ (∀P ∘ Any.there) y∈

∈utxo⇒outRef≡ : ∀ {u l}
  → u ∈ utxo l
  → prevTx u ∈ l
  × Σ[ out∈ ∈ (out u ∈ outputs (prevTx u)) ]
      outRef u ≡ ((prevTx u) ♯ₜₓ) indexed-at toℕ (Any.index out∈)
∈utxo⇒outRef≡ {l = tx ∷ l} u∈
  with ∈-++⁻ (filter ((SETₒ._∉? map outputRef (inputs tx)) ∘ outRef) (utxo l)) u∈
... | inj₁ u∈ˡ = map₁ there (∈utxo⇒outRef≡ (proj₁ (∈-filter⁻ ((SETₒ._∉? map outputRef (inputs tx)) ∘ outRef) u∈ˡ)))
... | inj₂ u∈ʳ = (mapWith∈-∀ {P = λ u → prevTx u ∈ (tx ∷ l)
                                      × Σ[ out∈ ∈ (out u ∈ outputs (prevTx u)) ]
                                          outRef u ≡ ((prevTx u) ♯ₜₓ) indexed-at toℕ (Any.index out∈)}
                             (λ x∈ → here refl , x∈ , refl))
                             u∈ʳ

---

lookupTx : (l : Ledger)
         → (out : TxOutputRef)
         → Any (λ tx → tx ♯ₜₓ ≡ id out) l
         → Tx
lookupTx l out ∃tx≡id = proj₁ (find ∃tx≡id)


-- similar to `getSpentOutput` in the spec

lookupOutput : (l : Ledger)
             → (out : TxOutputRef)
             → (∃tx≡id : Any (λ tx → tx ♯ₜₓ ≡ id out) l)
             → index out < length (outputs (lookupTx l out ∃tx≡id))
             → TxOutput
lookupOutput l out ∃tx≡id index≤len =
  outputs (lookupTx l out ∃tx≡id) ‼ (fromℕ< {index out} index≤len)

lookupValue : (l : Ledger)
            → (input : TxInput)
            → (∃tx≡id : Any (λ tx → tx ♯ₜₓ ≡ id (outputRef input)) l)
            → index (outputRef input) <
                length (outputs (lookupTx l (outputRef input) ∃tx≡id))
            → Quantities --Value
lookupValue l input ∃tx≡id index≤len =
  value (lookupOutput l (outputRef input) ∃tx≡id index≤len)

--------------------------------------------------------------------------------------
-- Pending transactions (i.e. parts of the transaction being passed to a validator).

mkPendingTxOut : TxOutput → PendingTxOutput
mkPendingTxOut txOut =
  record
    { value         = value txOut
    ; validatorHash = (address txOut) ♯ₐ
    ; dataHash      = dataHash txOut
    }

-- toℕ ∘ Any.index 
∈toIndex : {X : Set}{x : X}{xs : List X} → x ∈ xs → ℕ
∈toIndex (here px) = 0
∈toIndex (there p) = suc (∈toIndex p)

mkPendingTxIn : (l : Ledger)
              → (input : TxInput)
              → (∃tx≡id : Any (λ tx → tx ♯ₜₓ ≡ id (outputRef input)) l)
              → index (outputRef input) < length (outputs (lookupTx l (outputRef input) ∃tx≡id))
              → PendingTxInput
mkPendingTxIn l txIn ∃tx index< =
  record
    { validatorHash = (validator txIn) ♯
    ; dataHash      = dataHash txOut
    ; redeemerHash  = (redeemer txIn) ♯ᵈ
    ; value         = value txOut
    }
    where
      txOut = lookupOutput l (outputRef txIn) ∃tx index<

mkPendingTx : (l : Ledger)
            → (tx : Tx)
            → (i : TxInput)
            → i ∈ inputs tx
            → (v₁ : ∀ i → i ∈ inputs tx → Any (λ t → t ♯ₜₓ ≡ id (outputRef i)) l)
            → (∀ i → (i∈ : i ∈ inputs tx) →
                 index (outputRef i) < length (outputs (lookupTx l (outputRef i) (v₁ i i∈))))
            → PendingTx
mkPendingTx l tx i i∈ v₁ v₂ =
   record
     { inputInfo     = mapWith∈ (inputs tx) λ {i} i∈ → mkPendingTxIn l i (v₁ i i∈) (v₂ i i∈)
     ; thisInput     = ∈toIndex i∈
     ; outputInfo    = map mkPendingTxOut (outputs tx)
     ; dataWitnesses = [] --map (λ o → ((dataVal o) ♯ᵈ) , dataVal o) (outputs tx)    -- FIX ME
     -- ^ this info needs to come from outside if only datahashes are
     -- present in outputs
     ; txHash        = tx ♯ₜₓ
     ; fee           = fee tx
     ; forge         = forge tx
     ; range         = range tx }


-- auxiliary functions (from spec)

_⟨_⟩ : Ledger → TxOutputRef → Maybe Tx
[] ⟨ txo ⟩ = nothing
(tx ∷ l) ⟨ txo ⟩ with id txo ≟ℕ (tx ♯ₜₓ)
(tx ∷ l) ⟨ txo ⟩ | yes p = just tx
(tx ∷ l) ⟨ txo ⟩ | no ¬p = l ⟨ txo ⟩

_[_] : {X : Set} → List X → ℕ → Maybe X
[]       [ n     ] = nothing
(x ∷ xs) [ zero  ] = just x
(x ∷ xs) [ suc n ] = xs [ n ]

open import Data.List.Relation.Unary.All          using (All)

-- this version of `All` also provides access to to the position in the list
data AllN {X : Set}(P : X → ℕ → Set) : List X → Set where
  []  : AllN P []
  _∷_ : ∀ {x xs}(px : P x 0) → AllN (λ x n → P x (suc n)) xs → AllN P (x ∷ xs)

test : AllN (λ i n → i ≡ n) (0 ∷ 1 ∷ 2 ∷ [])
test = refl ∷ refl ∷ refl ∷ []

getSpentOutput : TxInput → Ledger → Maybe TxOutput
getSpentOutput i l =
  outputs <$> (l ⟨ outputRef i ⟩) >>= (_[ index (outputRef i) ])

toInputInfo : Ledger → TxInput → PendingTxInput
toInputInfo l i = record
  { validatorHash = (validator i) ♯
  ; dataHash = (dataVal i) ♯ᵈ
  ; redeemerHash = (redeemer i) ♯ᵈ
  ; value = maybe value [] (getSpentOutput i l) 
  }

toPendingTx : Ledger → Tx → ℕ → PendingTx
toPendingTx l tx i = record
  { inputInfo = map (toInputInfo l) (inputs tx)
  ; thisInput = i
  ; outputInfo = map mkPendingTxOut (outputs tx)
  ; range = range tx
  ; dataWitnesses = [] -- FIXME
  ; txHash = tx ♯ₜₓ
  ; fee = fee tx
  ; forge = forge tx
  }
