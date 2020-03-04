{-# OPTIONS --allow-unsolved-metas #-}
module UTxO.TxUtilities where

open import Function using (_∘_; _∋_; flip; _$_)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (Bool; T)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ-syntax; map₁)
open import Data.Maybe using (Maybe; nothing; _>>=_)
  renaming (just to pure; map to _<$>_)
open import Relation.Nullary using (yes;no)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Nat     using (ℕ; zero; suc; _+_; _<_)
  renaming (_≟_ to _≟ℕ_)
open import Data.Fin     using (Fin; toℕ; fromℕ<)
open import Data.Maybe   using (nothing;maybe)
open import Data.List    using (List; []; _∷_; length; map; _++_; filter; lookup)

open import Data.List.Membership.Propositional            using (_∈_; mapWith∈; find)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁻; ∈-filter⁻)
open import Data.List.Relation.Unary.Any as Any           using (Any; here; there)
open import Data.List.Relation.Unary.All                  using (All)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists

open import UTxO.Hashing.Base
open import UTxO.Value
open import UTxO.Types
open import UTxO.Hashing.Types

record UTXO : Set where
  field
    outRef   : TxOutputRef
    out      : TxOutput
    prevTx   : Tx

open UTXO public

utxo : Ledger → List UTXO
utxo []       = []
utxo (tx ∷ l) = filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)
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
  with ∈-++⁻ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) u∈
... | inj₁ u∈ˡ = map₁ there (∈utxo⇒outRef≡ (proj₁ (∈-filter⁻ ((SETₒ._∉? outputRefs tx) ∘ outRef) u∈ˡ)))
... | inj₂ u∈ʳ = (mapWith∈-∀ {P = λ u → prevTx u ∈ (tx ∷ l)
                                      × Σ[ out∈ ∈ (out u ∈ outputs (prevTx u)) ]
                                          outRef u ≡ ((prevTx u) ♯ₜₓ) indexed-at toℕ (Any.index out∈)}
                             (λ x∈ → here refl , x∈ , refl))
                             u∈ʳ

--------------------------------------------------------------------------------------
-- Pending transactions (i.e. parts of the transaction being passed to a validator).

-- auxiliary functions (from spec)

_⟨_⟩ : Ledger → TxOutputRef → Maybe Tx
[] ⟨ txo ⟩ = nothing
(tx ∷ l) ⟨ txo ⟩ with id txo ≟ℕ (tx ♯ₜₓ)
(tx ∷ l) ⟨ txo ⟩ | yes p = pure tx
(tx ∷ l) ⟨ txo ⟩ | no ¬p = l ⟨ txo ⟩

_[_] : {X : Set} → List X → ℕ → Maybe X
[]       [ n     ] = nothing
(x ∷ xs) [ zero  ] = pure x
(x ∷ xs) [ suc n ] = xs [ n ]

getSpentOutputRef : TxOutputRef → Ledger → Maybe TxOutput
getSpentOutputRef oRef l =
  outputs <$> (l ⟨ oRef ⟩) >>= _[ index oRef ]

getSpentOutput : TxInput → Ledger → Maybe TxOutput
getSpentOutput i l = getSpentOutputRef (outputRef i) l

utxo-[] : ∀ {l u}
  → u ∈ utxo l
  → l ⟨ outRef u ⟩ ≡ pure (prevTx u)
utxo-[] {l = tx ∷ l} {u} u∈
  with ∈-++⁻ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) u∈
... | inj₁ u∈ˡ
    = {!!}
--   with id (outRef u) ≟ℕ (tx ♯ₜₓ)
-- ... | yes p′ = {!!}
-- ... | no  _
--   with ∈-filter⁻ ((SETₒ._∉? outputRefs tx) ∘ outRef) {v = u} {xs = utxo l} u∈ˡ
-- ... | u∈ˡ′ , p
--     = utxo-getSpent {l = l} u∈ˡ′
... | inj₂ u∈ʳ
  with id (outRef u) ≟ℕ (tx ♯ₜₓ)
... | no ¬p = {!!}
... | yes id≡
  with outputs tx [ index (outRef u) ]
... | nothing = {!!}
... | pure x
    = {!!} -- mapWith∈-∀ (λ x∈ → refl) u∈ʳ

utxo-⟨⟩ : ∀ {l u}
  → u ∈ utxo l
  → outputs (prevTx u) [ index (outRef u) ] ≡ pure (out u)
utxo-⟨⟩ {l} {u} u∈ = {!!}


utxo-getSpent : ∀ {l u}
  → u ∈ utxo l
  → getSpentOutputRef (outRef u) l ≡ pure (out u)
utxo-getSpent {l} {u} u∈
  rewrite utxo-[] {l} {u} u∈
        | utxo-⟨⟩ {l} {u} u∈
        = refl

--   with ∈-++⁻ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) u∈
-- ... | inj₁ u∈ˡ
--   = {!!}
-- --   with id (outRef u) ≟ℕ (tx ♯ₜₓ)
-- -- ... | yes p′ = {!!}
-- -- ... | no  _
-- --   with ∈-filter⁻ ((SETₒ._∉? outputRefs tx) ∘ outRef) {v = u} {xs = utxo l} u∈ˡ
-- -- ... | u∈ˡ′ , p
-- --     = utxo-getSpent {l = l} u∈ˡ′
-- ... | inj₂ u∈ʳ
--   with id (outRef u) ≟ℕ (tx ♯ₜₓ)
-- ... | no ¬p = {!!}
-- ... | yes id≡
--   with outputs tx [ index (outRef u) ]
-- ... | nothing = {!!}
-- ... | pure x
--     = {!!} -- mapWith∈-∀ (λ x∈ → refl) u∈ʳ

--

mkOutputInfo : TxOutput → OutputInfo
mkOutputInfo txOut = record
  { value         = value txOut
  ; validatorHash = address txOut
  ; dataHash      = dataHash txOut }

mkInputInfo : Ledger → TxInput → InputInfo
mkInputInfo l i = record
  { outputRef     = outputRef i
  ; validatorHash = (validator i) ♯
  ; dataHash      = (dataVal i) ♯ᵈ
  ; redeemerHash  = (redeemer i) ♯ᵈ
  ; value         = maybe value [] (getSpentOutput i l) }

mkTxInfo : Ledger → Tx → TxInfo
mkTxInfo l tx = record
  { inputInfo  = map (mkInputInfo l) (inputs tx)
  ; outputInfo = map mkOutputInfo (outputs tx)
  ; range      = range tx
  ; fee        = fee tx
  ; forge      = forge tx }

toPendingTx : Ledger → (tx : Tx) → Index (inputs tx) → PendingTx
toPendingTx l tx i = record
  { thisInput = ‼-map {xs = inputs tx} {f = mkInputInfo l} i
  ; txInfo    = mkTxInfo l tx }

ptx-‼ : ∀ {l tx i} {i∈ : i ∈ inputs tx} →
  let ptx = toPendingTx l tx (Any.index i∈)
  in  (TxInfo.inputInfo (txInfo ptx) ‼ thisInput ptx) ≡ mkInputInfo l i
ptx-‼ {l = l} {i∈ = i∈} rewrite map-‼ {f = mkInputInfo l} i∈ = refl
