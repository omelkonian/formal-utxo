open import Data.List.Membership.Propositional.Properties
  using (find∘map; ∈-map⁻; ∈-map⁺; ∈-filter⁻; ∈-filter⁺; ∈-++⁻; ∈-++⁺ʳ; ∈-++⁺ˡ)

open import Prelude.Init
open import Prelude.General
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Set'
open import Prelude.ToN
open import Prelude.Bifunctor
open import Prelude.Applicative

open import UTxO.Hashing
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.Validity
open import UTxO.TxUtilities
open import StateMachine.Base

open InputInfo
open TxInfo

module Bisimulation.Completeness
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open CEM {sm = sm}
open import StateMachine.Properties {sm = sm}
open import Bisimulation.Base       {sm = sm}

completeness : ∀ {s tx l} {vtx : IsValidTx tx l} {vl : ValidLedger l} {vl′ : ValidLedger (tx ∷ l)}
  → vl —→[ tx ∶- vtx ] vl′
  → vl ~ s
    --------------------------------------
  → (∃[ i ] ∃[ s′ ] ∃[ tx≡ ]
      ( s —→[ i ] (s′ , tx≡)
      × (vl′ ~ s′)
      × (verifyTx l tx tx≡ ≡ true)))
  ⊎ (vl′ ~ s)
completeness {s} {tx} {l} {vtx} {vl} {vl′} vl→vl′ vl~s
  with view-~ {l} {s} {vl} vl~s
... | prevTx , v , prevOut∈ , u∈ , _ , prev∈utxo , getSpent≡ , threadToken≡
  with (prevTx ♯ₜₓ) indexed-at (toℕ (L.Any.index prevOut∈)) ∈? outputRefs tx
... | no prev∉
    = inj₂ (∈-map⁺ (datumHash ∘ out)
             (∈-filter⁺ ((_≟ true) ∘ (_≥ᶜ threadₛₘ) ∘ value ∘ out)
               (∈-filter⁺ ((𝕍 ≟_) ∘ address ∘ out)
                 (∈-++⁺ˡ (∈-filter⁺ ((_∉? outputRefs tx) ∘ outRef) {x = u} {xs = utxo l}
                   u∈ prev∉)) refl)
               threadToken≡))
      where o    = record { address = 𝕍; datumHash = toData s ♯ᵈ; value = v }
            u    = record { prevTx = prevTx; out = o; outRef = (prevTx ♯ₜₓ) indexed-at (toℕ (L.Any.index prevOut∈)) }
... | yes prev∈
  with ∈-map⁻ outputRef prev∈
... | txIn , txIn∈ , refl
    = inj₁ (STEP (validate≡ {ptx = ptx} (L.All.lookup (allInputsValidate vtx) (x∈→ix∈ txIn∈))))
  where
    ptx = toPendingTx l tx (L.Any.index txIn∈)
    txi = txInfo ptx
    di  = redeemer txIn
    ds  = toData s

    vvh : (𝕍 ≡ validator txIn ♯) × (ds ≡ datum txIn)
    vvh = map₂ injective♯ᵈ
        $ Any-just getSpent≡ (L.All.lookup (validateValidHashes vtx) txIn∈)

    validate≡ : ∀ {ptx : PendingTx}
       → T (runValidation ptx txIn)
       → T (validatorₛₘ ptx di ds)
    validate≡ p rewrite getSpent≡
                      | ♯-injective (sym $ proj₁ vvh)
                      | sym (proj₂ vvh)
                      = p

    STEP :
        T (validatorₛₘ ptx di ds)
         ------------------------------------
      → ∃[ i ] ∃[ s′ ] ∃[ tx≡ ]
          ( (stepₛₘ s i ≡ pure (s′ , tx≡))
          × (vl′ ~ s′)
          × (verifyTx l tx tx≡ ≡ true) )
    STEP eq
      with T-validator {di} {s} {ptx} eq
    ... | i , s′ , tx≡ , step≡ , outsOK≡ , verify≡ , prop≡
        = i , s′ , tx≡ , step≡ , vl′~s′ , verify≡
      where
        vl′~s′ : vl′ ~ s′
        vl′~s′
          with T-propagates {ptx} prop≡
        ... | vin≥ , vout≥
          with T-outputsOK {l} {tx} {di} {ds} {s′} {txIn} {txIn∈} outsOK≡
        ... | o , o∈ , out≡ , refl , refl , refl
          with mapWith∈⁺ {x = o} {xs = outputs tx}
                         {f = λ {out} out∈ → record { outRef   = (tx ♯ₜₓ) indexed-at toℕ (L.Any.index out∈)
                                                    ; out      = out
                                                    ; prevTx   = tx }} o∈
        ... | u , u∈ , refl
            = ∈-map⁺ (datumHash ∘ out) {x = u}
                (∈-filter⁺ ((_≟ true) ∘ (_≥ᶜ threadₛₘ) ∘ value ∘ out)
                  (∈-filter⁺ ((𝕍 ≟_) ∘ address ∘ out) {x = u} {xs = utxo (tx ∷ l)}
                    (∈-++⁺ʳ (filter ((_∉? outputRefs tx) ∘ outRef) (utxo l)) u∈)
                    (proj₁ vvh))
                  vout≥)
