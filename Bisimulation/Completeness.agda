open import Level          using (0ℓ)
open import Function       using (_∘_; case_of_; _$_)
open import Category.Monad using (RawMonad)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (Bool; T; true; false; if_then_else_; not; _∧_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax; proj₁; proj₂; map₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Maybe   using (Maybe; fromMaybe; just; nothing; maybe′)
open import Data.Fin     using (Fin; toℕ; fromℕ<)
  renaming (suc to fsuc; zero to fzero)
open import Data.Nat     using (ℕ; _<_; z≤n; s≤s; _+_)
  renaming (_≟_ to _≟ℕ_)
open import Data.List    using (List; []; _∷_; [_]; map; length; filter; null; lookup)

open import Data.Bool.Properties  using (T?)
  renaming (_≟_ to _≟𝔹_)
open import Data.Maybe.Properties using (just-injective)
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Unary.All as All using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs   using ([]; _∷_)
open import Data.List.Membership.Propositional  using (_∈_; _∉_; find; mapWith∈)
open import Data.List.Membership.Propositional.Properties
  using (find∘map; ∈-map⁻; ∈-map⁺; ∈-filter⁻; ∈-filter⁺; ∈-++⁻; ∈-++⁺ʳ; ∈-++⁺ˡ)

import Data.Maybe.Relation.Unary.Any as M

open import Relation.Nullary                            using (¬_; yes; no)
open import Relation.Nullary.Decidable                  using (⌊_⌋; toWitness)
open import Relation.Binary                             using (Decidable)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; cong; trans; sym; inspect)
  renaming ([_] to ≡[_])
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Prelude.General
open import Prelude.Lists

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
  with (prevTx ♯ₜₓ) indexed-at (toℕ (Any.index prevOut∈)) SETₒ.∈? outputRefs tx
... | no prev∉
    = inj₂ (∈-map⁺ (datumHash ∘ out)
             (∈-filter⁺ ((_≟𝔹 true) ∘ (_≥ᶜ threadₛₘ) ∘ value ∘ out)
               (∈-filter⁺ ((𝕍 ≟ℕ_) ∘ address ∘ out)
                 (∈-++⁺ˡ (∈-filter⁺ ((SETₒ._∉? outputRefs tx) ∘ outRef) {x = u} {xs = utxo l}
                   u∈ prev∉)) refl)
               threadToken≡))
      where o    = record { address = 𝕍; datumHash = toData s ♯ᵈ; value = v }
            u    = record { prevTx = prevTx; out = o; outRef = (prevTx ♯ₜₓ) indexed-at (toℕ (Any.index prevOut∈)) }
... | yes prev∈
  with ∈-map⁻ outputRef prev∈
... | txIn , txIn∈ , refl
    = inj₁ (STEP (validate≡ {ptx = ptx} (All.lookup (allInputsValidate vtx) (x∈→ix∈ txIn∈))))
  where
    ptx = toPendingTx l tx (Any.index txIn∈)
    txi = txInfo ptx
    di  = redeemer txIn
    ds  = toData s

    vvh : (𝕍 ≡ validator txIn ♯) × (ds ≡ datum txIn)
    vvh = map₂ injective♯ᵈ
        $ Any-just getSpent≡ (All.lookup (validateValidHashes vtx) txIn∈)

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
                         {f = λ {out} out∈ → record { outRef   = (tx ♯ₜₓ) indexed-at toℕ (Any.index out∈)
                                                    ; out      = out
                                                    ; prevTx   = tx }} o∈
        ... | u , u∈ , refl
            = ∈-map⁺ (datumHash ∘ out) {x = u}
                (∈-filter⁺ ((_≟𝔹 true) ∘ (_≥ᶜ threadₛₘ) ∘ value ∘ out)
                  (∈-filter⁺ ((𝕍 ≟ℕ_) ∘ address ∘ out) {x = u} {xs = utxo (tx ∷ l)}
                    (∈-++⁺ʳ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) u∈)
                    (proj₁ vvh))
                  vout≥)
