module UTxO.TxUtilities where

open import Level          using (0ℓ)
open import Function       using (_∘_; _∋_; flip; _$_)
open import Category.Monad using (RawMonad)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (Bool; T)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ-syntax; map₁)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (yes;no)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Nat     using (ℕ; zero; suc; _+_; _<_)
  renaming (_≟_ to _≟ℕ_)
open import Data.Fin     using (Fin; toℕ; fromℕ<)
open import Data.Maybe   using (nothing;maybe)
open import Data.List    using (List; []; _∷_; length; map; _++_; filter; lookup)

import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List.Membership.Propositional                       using (_∈_; mapWith∈; find)
open import Data.List.Membership.Propositional.Properties            using (∈-map⁻; ∈-++⁻; ∈-filter⁻)
open import Data.List.Relation.Unary.Any as Any                      using (Any; here; there)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong)

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

mkUtxo : ∀ {out} tx → out ∈ outputs tx → UTXO
outRef (mkUtxo tx out∈)   = (tx ♯ₜₓ) indexed-at toℕ (Any.index out∈)
out    (mkUtxo {out} _ _) = out
prevTx (mkUtxo tx _ )     = tx

utxo : Ledger → List UTXO
utxo []       = []
utxo (tx ∷ l) = filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)
             ++ mapWith∈ (outputs tx) (mkUtxo tx)

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
(tx ∷ l) ⟨ txo ⟩
  with id txo ≟ℕ tx ♯ₜₓ
... | yes _ = just tx
... | no  _ = l ⟨ txo ⟩

utxo-outRef↔prevTx : ∀ {u l}
  → u ∈ utxo l
  → id (outRef u) ≡ prevTx u ♯ₜₓ
utxo-outRef↔prevTx {u} {l} u∈
  rewrite proj₂ (proj₂ (∈utxo⇒outRef≡ {u} {l} u∈))
        = refl

utxo-∈ʳ : ∀ {u tx}
  → u ∈ mapWith∈ (outputs tx) (mkUtxo tx)
  → tx ≡ prevTx u
utxo-∈ʳ {u} {tx} = mapWith∈-∀ {P = (tx ≡_) ∘ prevTx} λ _ → refl

utxo-≢ : ∀ {l u tx}
  → u ∈ utxo (tx ∷ l)
  → id (outRef u) ≢ tx ♯ₜₓ
  → u ∈ utxo l
utxo-≢ {l} {u} {tx} u∈ ¬p
  with ∈-++⁻ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) u∈
... | inj₁ u∈ˡ
    = proj₁ (∈-filter⁻ ((SETₒ._∉? outputRefs tx) ∘ outRef) {v = u} {xs = utxo l} u∈ˡ)
... | inj₂ u∈ʳ
    = ⊥-elim (¬p (trans (utxo-outRef↔prevTx {u} {tx ∷ l} u∈) (sym (cong _♯ₜₓ (utxo-∈ʳ {u} {tx} u∈ʳ)))))

utxo-[] : ∀ {l u}
  → u ∈ utxo l
  → l ⟨ outRef u ⟩ ≡ just (prevTx u)
utxo-[] {l = tx ∷ l} {u} u∈
  with id (outRef u) ≟ℕ tx ♯ₜₓ
... | yes p
  rewrite injective♯ₜₓ {x = prevTx u} {y = tx} (trans (sym (utxo-outRef↔prevTx {u} {tx ∷ l} u∈)) p)
    = refl
... | no ¬p = utxo-[] {l} (utxo-≢ {l} {u} {tx} u∈ ¬p)

_⟦_⟧ : {X : Set} → List X → ℕ → Maybe X
_⟦_⟧ = _⁉_

utxo-⟨⟩ : ∀ {l u}
  → u ∈ utxo l
  → outputs (prevTx u) ⟦ index (outRef u) ⟧ ≡ just (out u)
utxo-⟨⟩ {tx ∷ l} {u} u∈
  with ∈-++⁻ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) u∈
... | inj₁ u∈ˡ
    = utxo-⟨⟩ {l} {u} (proj₁ (∈-filter⁻ ((SETₒ._∉? outputRefs tx) ∘ outRef) {v = u} {xs = utxo l} u∈ˡ))
... | inj₂ u∈ʳ
    = mapWith∈-∀ {P = λ u → outputs (prevTx u) ⟦ index (outRef u) ⟧ ≡ just (out u)}
                 (λ x∈ → trans (sym (‼→⁉ {xs = outputs tx} {ix = Any.index x∈})) (cong just (‼-index x∈))) u∈ʳ

getSpentOutputRef : Ledger → TxOutputRef → Maybe TxOutput
getSpentOutputRef l oRef =
  outputs <$> (l ⟨ oRef ⟩) >>= _⟦ index oRef ⟧

getSpentOutput : Ledger → TxInput → Maybe TxOutput
getSpentOutput l i = getSpentOutputRef l (outputRef i)

utxo-getSpent : ∀ {l u}
  → u ∈ utxo l
  → getSpentOutputRef l (outRef u) ≡ just (out u)
utxo-getSpent {l} {u} u∈
  rewrite utxo-[] {l} {u} u∈
        | utxo-⟨⟩ {l} {u} u∈
        = refl

--

mkOutputInfo : TxOutput → OutputInfo
mkOutputInfo txOut = record
  { value         = value txOut
  ; validatorHash = address txOut
  ; datumHash     = datumHash txOut }

mkInputInfo : Ledger → TxInput → InputInfo
mkInputInfo l i = record
  { outputRef     = outputRef i
  ; validatorHash = (validator i) ♯
  ; datumHash     = (datum i) ♯ᵈ
  ; redeemerHash  = (redeemer i) ♯ᵈ
  ; value         = maybe value [] (getSpentOutput l i) }

mkTxInfo : Ledger → Tx → TxInfo
mkTxInfo l tx = record
  { inputInfo      = map (mkInputInfo l) (inputs tx)
  ; outputInfo     = map mkOutputInfo (outputs tx)
  ; datumWitnesses = datumWitnesses tx
  ; range          = range tx
  ; fee            = fee tx
  ; policies       = map _♯ (policies tx)
  ; forge          = forge tx }

toPendingTx : Ledger → (tx : Tx) → Index (inputs tx) → PendingTx
toPendingTx l tx i = record
  { this   = ‼-map {xs = inputs tx} {f = mkInputInfo l} i
  ; txInfo = mkTxInfo l tx }

toPendingMPS : Ledger → Tx → HashId → PendingMPS
toPendingMPS l tx i = record
  { this   = i
  ; txInfo = mkTxInfo l tx }

ptx-‼ : ∀ {l tx i} {i∈ : i ∈ inputs tx} →
  let ptx = toPendingTx l tx (Any.index i∈)
  in  (TxInfo.inputInfo (txInfo ptx) ‼ this ptx) ≡ mkInputInfo l i
ptx-‼ {l = l} {i∈ = i∈} rewrite map-‼ {f = mkInputInfo l} i∈ = refl
