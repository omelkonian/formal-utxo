open import Function using (_∘_; case_of_)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (Bool; T; true; false; if_then_else_; not; _∧_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Maybe   using (Maybe; fromMaybe; nothing; maybe′)
  renaming (just to pure; ap to _<*>_) -- to use idiom brackets
open import Data.Fin     using (Fin; toℕ; fromℕ<)
  renaming (suc to fsuc; zero to fzero)
open import Data.Nat     using (ℕ; _<_; z≤n; s≤s; _+_)
  renaming (_≟_ to _≟ℕ_)
open import Data.List    using (List; []; _∷_; [_]; map; length; filter; null; lookup)

open import Data.Bool.Properties  using (T?)
open import Data.Maybe.Properties using (just-injective)

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
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import Prelude.General
open import Prelude.Lists

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.Validity
open import UTxO.TxUtilities
open import StateMachine.Base

open InputInfo
open OutputInfo
open TxInfo
open PendingTx

module Bisimulation.Completeness
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open import Bisimulation.Base {sm = sm}

completeness : ∀ {s tx l} {vtx : IsValidTx tx l} {vl : ValidLedger l} {vl′ : ValidLedger (tx ∷ l)}
  → vl —→[ tx ∶- vtx ] vl′
  → vl ~ s
    --------------------------------------
  → (∃[ i ] ∃[ s′ ] ∃[ tx≡ ]
      ( s —→[ i ] (s′ , tx≡)
      × (finalₛₘ s′ ≡ false → vl′ ~ s′)
      × (verifyTx l tx tx≡ ≡ true)))
  ⊎ (vl′ ~ s)
completeness {s} {tx} {l} {vtx} {vl} {vl′} vl→vl′ vl~s
  with view-~ {l} {s} {vl} vl~s
... | prevTx , v , prevOut∈ , u∈ , _ , prev∈utxo , getSpent≡
  with (prevTx ♯ₜₓ) indexed-at (toℕ (Any.index prevOut∈)) SETₒ.∈? outputRefs tx
... | no  prev∉
    = inj₂ (∈-map⁺ (dataHash ∘ out)
             (∈-filter⁺ ((𝕍 ≟ℕ_) ∘ address ∘ out)
               (∈-++⁺ˡ (∈-filter⁺ ((SETₒ._∉? outputRefs tx) ∘ outRef) {x = u} {xs = utxo l}
                 u∈ prev∉)) refl))
      where oRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈)
            o    = record { address = 𝕍; dataHash = toData s ♯ᵈ; value = v }
            u    = record { prevTx = prevTx; out = o; outRef = oRef }

... | yes prev∈
  with ∈-map⁻ outputRef prev∈
... | txIn , txIn∈ , refl
    = inj₁ (STEP (validate≡ {ptx = ptx} (All.lookup (allInputsValidate vtx) (x∈→ix∈ txIn∈))))
  where
    ptx = toPendingTx l tx (Any.index txIn∈)
    di  = redeemer txIn
    ds  = toData s

    valTxIn≡ : (validator txIn ♯) ≡ 𝕍
    valTxIn≡
      with All.lookup (validateValidHashes vtx) txIn∈
    ... | vvh≡
      rewrite getSpent≡
      with vvh≡
    ... | M.just (val♯≡ , _)
      rewrite val♯≡
        = refl

    data≡ : dataVal txIn ≡ ds
    data≡
      with All.lookup (validateValidHashes vtx) txIn∈
    ... | vvh≡
      rewrite getSpent≡
      with vvh≡
    ... | M.just (_ , ds♯≡)
      rewrite injective♯ᵈ {x = ds} {y = dataVal txIn} ds♯≡
        = refl

    validate≡ : ∀ {ptx : PendingTx}
       → T (runValidation ptx txIn)
       → T (validatorₛₘ ptx di ds)
    validate≡ p rewrite getSpent≡
                      | ♯-injective valTxIn≡
                      | data≡
                      = p

    STEP :
        T (validatorₛₘ ptx di ds)
         ------------------------------------
      → ∃[ i ] ∃[ s′ ] ∃[ tx≡ ]
          ( (stepₛₘ s i ≡ pure (s′ , tx≡))
          × (finalₛₘ s′ ≡ false → vl′ ~ s′)
          × (verifyTx l tx tx≡ ≡ true) )
    STEP eq
      rewrite from∘to s
      with ⦇ stepₛₘ (pure s) (fromData di) ⦈
         | inspect (λ x → ⦇ stepₛₘ (pure s) x ⦈) (fromData di)
         | eq
    ... | nothing | _        | ()
    ... | pure r  | ≡[ eq′ ] | _
      with fromData {A = I} di
    ... | nothing = ⊥-elim (ap-nothing {m = maybe′ (pure ∘ stepₛₘ) nothing (pure s)} eq′)
    ... | pure i
      with stepₛₘ s i | inspect (stepₛₘ s) i | eq
    ... | nothing         | _          | ()
    ... | pure (s′ , tx≡) | ≡[ step≡ ] | _
      rewrite step≡
      with verifyTxInfo (txInfo ptx) tx≡ | inspect (verifyTxInfo (txInfo ptx)) tx≡ | eq
    ... | false | _ | eq²
        = ⊥-elim (∧-falseʳ eq²)
    ... | true  | ≡[ verify≡ ] | _
      with finalₛₘ s′ | inspect finalₛₘ s′
    ... | true  | ≡[ final≡ ]
        = i , s′ , tx≡ , step≡ , (λ ¬fin → ⊥-elim (⊥-bool (final≡ , ¬fin))) , verify≡
    ... | false | _
      with getContinuingOutputs ptx | inspect getContinuingOutputs ptx
    ... | (o ∷ []) | ≡[ out≡ ]
      rewrite ptx-‼ {l = l} {tx = tx} {i∈ = txIn∈}
      with ∈-filter⁻ (((validator txIn) ♯ ≟ℕ_) ∘ OutputInfo.validatorHash)
                     {v = o} {xs = map mkOutputInfo (outputs tx)} (singleton→∈ (_ , out≡))
    ... | o∈ , refl
      with ∈-map⁻ mkOutputInfo o∈
    ... | o′ , o′∈ , refl
      with dataHash o′ ≟ℕ toData s′ ♯ᵈ | eq
    ... | no ¬p    | ()
    ... | yes refl | _
        = i , s′ , tx≡ , step≡ , (λ _ → helper) , verify≡
        where
          helper : toData s′ ♯ᵈ ∈ (map (dataHash ∘ out) ∘ filter ((𝕍 ≟ℕ_) ∘ address ∘ out)) (utxo (tx ∷ l))
          helper
            with mapWith∈⁺ {B = UTXO} {x = o′} {xs = outputs tx}
                           {f = λ {out} out∈ → record { outRef   = (tx ♯ₜₓ) indexed-at toℕ (Any.index out∈)
                                                      ; out      = out
                                                      ; prevTx   = tx }}
                           o′∈
          ... | u , u∈ , refl
              = ∈-map⁺ (dataHash ∘ out) {x = u}
                  (∈-filter⁺ ((𝕍 ≟ℕ_) ∘ address ∘ out) {x = u} {xs = utxo (tx ∷ l)}
                    (∈-++⁺ʳ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) u∈)
                      (sym valTxIn≡))
