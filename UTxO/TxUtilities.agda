module UTxO.TxUtilities where

open import Data.List.Properties
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-filter⁻)

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Set'
open import Prelude.ToN
-- open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Monad

open import UTxO.Hashing
open import UTxO.Value
open import UTxO.Types

record UTXO : Set where
  field
    outRef   : TxOutputRef
    out      : TxOutput
    prevTx   : Tx

open UTXO public

mkUtxo : ∀ {out} tx → out ∈ outputs tx → UTXO
outRef (mkUtxo tx out∈)   = (tx ♯ₜₓ) indexed-at toℕ (L.Any.index out∈)
out    (mkUtxo {out} _ _) = out
prevTx (mkUtxo tx _ )     = tx

utxo : Ledger → List UTXO
utxo []       = []
utxo (tx ∷ l) = filter ((_∉? outputRefs tx) ∘ outRef) (utxo l)
             ++ mapWith∈ (outputs tx) (mkUtxo tx)

open ≡-Reasoning

map-out≡ : ∀ tx → map out (mapWith∈ (outputs tx) (mkUtxo tx)) ≡ outputs tx
map-out≡ tx =
  begin map out (mapWith∈ (outputs tx) (mkUtxo tx)) ≡⟨ map∘mapWith∈ {xs = outputs tx} {f = out} {g = mkUtxo tx} ⟩
        mapWith∈ (outputs tx) (out ∘ mkUtxo tx)     ≡⟨⟩
        mapWith∈ (outputs tx) (λ {o} _ → o)         ≡⟨ mapWith∈-id {xs = outputs tx} ⟩
        outputs tx                                  ∎

∑utxo≥∑out : ∀ tx l → T $ ∑ (utxo $ tx ∷ l) (value ∘ out) ≥ᶜ ∑ (outputs tx) value
∑utxo≥∑out tx l
  rewrite ∑-++ {xs = filter ((_∉? outputRefs tx) ∘ outRef) (utxo l)}
               {ys = mapWith∈ (outputs tx) (mkUtxo tx)} {fv = value ∘ out}
        = ≥ᶜ-+ᶜ {x = ∑ (filter ((_∉? outputRefs tx) ∘ outRef) (utxo l)) (value ∘ out)}
                {y = ∑ (mapWith∈ (outputs tx) (mkUtxo tx)) (value ∘ out)}
                {z = ∑ (outputs tx) value}
                (≥ᶜ-refl′ ∑≡)
  where
    ∑≡ : ∑ (mapWith∈ (outputs tx) (mkUtxo tx)) (value ∘ out) ≡ ∑ (outputs tx) value
    ∑≡ rewrite map-compose {g = value} {f = out} (mapWith∈ (outputs tx) (mkUtxo tx))
             | map-out≡ tx
             = refl

∈utxo⇒outRef≡ : ∀ {u l}
  → u ∈ utxo l
  → prevTx u ∈ l
  × Σ[ out∈ ∈ (out u ∈ outputs (prevTx u)) ]
      outRef u ≡ ((prevTx u) ♯ₜₓ) indexed-at toℕ (L.Any.index out∈)
∈utxo⇒outRef≡ {l = tx ∷ l} u∈
  with ∈-++⁻ (filter ((_∉? outputRefs tx) ∘ outRef) (utxo l)) u∈
... | inj₁ u∈ˡ = map₁ there (∈utxo⇒outRef≡ (proj₁ (∈-filter⁻ ((_∉? outputRefs tx) ∘ outRef) u∈ˡ)))
... | inj₂ u∈ʳ = (mapWith∈-∀ {P = λ u → prevTx u ∈ (tx ∷ l)
                                      × Σ[ out∈ ∈ (out u ∈ outputs (prevTx u)) ]
                                          outRef u ≡ ((prevTx u) ♯ₜₓ) indexed-at toℕ (L.Any.index out∈)}
                             (λ x∈ → here refl , x∈ , refl))
                             u∈ʳ


--------------------------------------------------------------------------------------
-- Pending transactions (i.e. parts of the transaction being passed to a validator).

-- auxiliary functions (from spec)

_⟨_⟩ : Ledger → TxOutputRef → Maybe Tx
[] ⟨ or ⟩ = nothing
(tx ∷ l) ⟨ or ⟩
  with hid or ≟ tx ♯ₜₓ
... | yes _ = just tx
... | no  _ = l ⟨ or ⟩

⟨⟩≡just : ∀ {l or tx}
  → l ⟨ or ⟩ ≡ just tx
  → hid or ≡ tx ♯ₜₓ
⟨⟩≡just {l = []}              ()
⟨⟩≡just {l = tx′ ∷ l}{or}{tx} eq
  with hid or ≟ tx′ ♯ₜₓ | eq
... | yes refl | refl = refl
... | no  _    | eq′  = ⟨⟩≡just {l}{or}{tx} eq′

utxo-outRef↔prevTx : ∀ {u l}
  → u ∈ utxo l
  → hid (outRef u) ≡ prevTx u ♯ₜₓ
utxo-outRef↔prevTx {u} {l} u∈
  rewrite proj₂ (proj₂ (∈utxo⇒outRef≡ {u} {l} u∈))
        = refl

utxo-∈ʳ : ∀ {u tx}
  → u ∈ mapWith∈ (outputs tx) (mkUtxo tx)
  → tx ≡ prevTx u
utxo-∈ʳ {u} {tx} = mapWith∈-∀ {P = (tx ≡_) ∘ prevTx} λ _ → refl

utxo-≢ : ∀ {l u tx}
  → u ∈ utxo (tx ∷ l)
  → hid (outRef u) ≢ tx ♯ₜₓ
  → u ∈ utxo l
utxo-≢ {l} {u} {tx} u∈ ¬p
  with ∈-++⁻ (filter ((_∉? outputRefs tx) ∘ outRef) (utxo l)) u∈
... | inj₁ u∈ˡ
    = proj₁ (∈-filter⁻ ((_∉? outputRefs tx) ∘ outRef) {v = u} {xs = utxo l} u∈ˡ)
... | inj₂ u∈ʳ
    = ⊥-elim (¬p (trans (utxo-outRef↔prevTx {u} {tx ∷ l} u∈) (sym (cong _♯ₜₓ (utxo-∈ʳ {u} {tx} u∈ʳ)))))

utxo-[] : ∀ {l u}
  → u ∈ utxo l
  → l ⟨ outRef u ⟩ ≡ just (prevTx u)
utxo-[] {l = tx ∷ l} {u} u∈
  with hid (outRef u) ≟ tx ♯ₜₓ
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
  with ∈-++⁻ (filter ((_∉? outputRefs tx) ∘ outRef) (utxo l)) u∈
... | inj₁ u∈ˡ
    = utxo-⟨⟩ {l} {u} (proj₁ (∈-filter⁻ ((_∉? outputRefs tx) ∘ outRef) {v = u} {xs = utxo l} u∈ˡ))
... | inj₂ u∈ʳ
    = mapWith∈-∀ {P = λ u → outputs (prevTx u) ⟦ index (outRef u) ⟧ ≡ just (out u)}
                 (λ x∈ → trans (sym (‼→⁉ {xs = outputs tx} {ix = L.Any.index x∈})) (cong just (‼-index x∈))) u∈ʳ

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

utxo-getSpentᵛ : ∀ {l u i}
  → u ∈ utxo l
  → outRef u ≡ outputRef i
  → (value <$> getSpentOutput l i) ≡ just (value $ out u)
utxo-getSpentᵛ {l} {u} {i} u∈ refl = cong (_<$>_ value) (utxo-getSpent {l} {u} u∈)
-- BUG: `cong (value <$>_)` leads to unresolved instances...

--

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
  ; outputInfo     = outputs tx
  ; datumWitnesses = datumWitnesses tx
  ; range          = range tx
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

--

ptx-‼ : ∀ {l tx i} {i∈ : i ∈ inputs tx} →
  let ptx = toPendingTx l tx (L.Any.index i∈)
  in  (TxInfo.inputInfo (txInfo ptx) ‼ this ptx) ≡ mkInputInfo l i
ptx-‼ {l = l} {i∈ = i∈} rewrite map-‼ {f = mkInputInfo l} i∈ = refl

∑₁ᶜ : ∀ {H : Value → Set} → List (∃ H) → Value
∑₁ᶜ = flip ∑ proj₁

∑ᵥ : List TxOutput → Value
∑ᵥ = flip ∑ value

outRef∈txi : ∀ {tx l o}
  → o ∈ map InputInfo.outputRef (TxInfo.inputInfo $ mkTxInfo l tx)
  → o ∈ outputRefs tx
outRef∈txi {tx}{l}{o} o∈ with inputs tx | o∈
... | []     | ()
... | i ∷ is | here refl = here refl
... | i ∷ is | there o∈′ = there (outRef∈txi {tx = record tx {inputs = is}}{l} o∈′)

lookup-⟨⟩ : ∀ {tx l i}
  → Is-just (getSpentOutput l i)
  → hid (outputRef i) ≡ tx ♯ₜₓ
    ----------------------------
  → l ⟨ outputRef i ⟩ ≡ just tx
lookup-⟨⟩ {tx}{l}{i@(record{outputRef = or})} getSpent≡ id≡
  with l       | getSpent≡
... | []       | ()
... | tx′ ∷ l′ | getSpent≡′
  with hid or ≟ tx′ ♯ₜₓ
... | yes refl
  rewrite injective♯ₜₓ {x = tx′} {y = tx} id≡
    = refl
... | no _
    = lookup-⟨⟩ {tx}{l′}{i} getSpent≡′ id≡

lookup-⟦⟧ : ∀ {tx l i o}
  → Is-just (getSpentOutput l i)
  → hid (outputRef i) ≡ tx ♯ₜₓ
  → outputs tx ⟦ index (outputRef i) ⟧ ≡ just o
    -------------------------------------------
  → getSpentOutput l i ≡ just o
lookup-⟦⟧ {tx = tx}{l}{i}{o} vvh id≡ p rewrite lookup-⟨⟩ {tx = tx}{l}{i} vvh id≡ = p

postulate
  -- Assume that datumWitnesses have been constructed properly.
  -- T0D0: remove datumWitnesses and keep datums immediately in outputs
  wits♯ : ∀ {txi d♯ d}
    → (d♯ , d) ∈ TxInfo.datumWitnesses txi
    → d♯ ≡ d ♯ᵈ

lookupDatum≡ : ∀ {A : Set} {{_ : IsData A}} {x : A} {d♯ : HashId} {txi : TxInfo} {wits : List (HashId × DATA)}
  → TxInfo.datumWitnesses txi ≡ wits
  → (lookupDatum d♯ wits >>= fromData) ≡ just x
  → d♯ ≡ toData x ♯ᵈ
lookupDatum≡ {x = x}{d♯}{txi}{[]}             _    ()
lookupDatum≡ {x = x}{d♯}{txi}{(h , d) ∷ wits} wits≡ eq
  with d♯ ≟ h
... | yes p
  rewrite filter-accept ((d♯ ≟_) ∘ proj₁) {x = h , d} {xs = wits} p
    = begin d♯          ≡⟨ p ⟩
            h           ≡⟨ wits♯ {txi}{h}{d} (subst ((h , d) ∈_) (sym wits≡) (here refl)) ⟩
            d ♯ᵈ        ≡⟨ cong (_♯ᵈ) (from-inj _ _ eq) ⟩
            toData x ♯ᵈ ∎
... | no ¬p
  rewrite filter-reject ((d♯ ≟_) ∘ proj₁) {x = h , d} {xs = wits} ¬p
    = lookupDatum≡ {x = x}{d♯}{record txi {datumWitnesses = wits}}{wits} refl eq
