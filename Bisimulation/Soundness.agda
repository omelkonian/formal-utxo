open import Function using (_∘_)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (Bool; T; true; false)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Fin     using (toℕ)
  renaming (zero to fzero)
open import Data.Maybe   using (nothing)
  renaming (just to pure; ap to _<*>_) -- to use idiom brackets
open import Data.Nat     using (ℕ; _<_)
  renaming (_≟_ to _≟ℕ_)
open import Data.List    using ([]; _∷_; [_]; filter)

open import Data.List.Relation.Unary.Any as Any           using (here)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-filter⁺; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.AllPairs             using ([]; _∷_)
open import Data.List.Relation.Unary.All                  using ([]; _∷_)

import Data.Maybe.Relation.Unary.Any as M

open import Relation.Nullary                      using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities hiding (prevTx)
open import UTxO.Validity
open import StateMachine.Base

open InputInfo
open OutputInfo
open PendingTx

module Bisimulation.Soundness
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open import Bisimulation.Base {sm = sm}

soundness : ∀ {s i s′ tx≡ l} {vl : ValidLedger l}
  → finalₛₘ s′ ≡ false
  → s —→[ i ] (s′ , tx≡)
  → (vl~s : vl ~ s)
  → Satisfiable {vl = vl} tx≡ vl~s
    --------------------------------
  → ∃[ tx ] ∃[ vtx ] ∃[ vl′ ]
      ( vl —→[ tx ∶- vtx ] vl′
      × vl′ ~ s′
      × (verifyTx l tx tx≡ ≡ true) )

soundness {s} {i} {s′} {tx≡} {l} {vl} final≡ s→s′ vl~s sat@(range∋ , sp≥ , frg≡)
-- *** Due to Agda bug, see https://github.com/personal-practice/agda/blob/master/bugs/With.agda
--   with view-~ {vl = vl} vl~s
-- ... | prevTx , v , prevOut∈ , u∈ , prev∈ , prev∈utxo , getSpent≡
  = tx , vtx , vl′ , vl→vl′ , vl′~s′ , verify≡
  where
    -- *** Manually deconstructing here instead
    view = view-~ {vl = vl} vl~s
    prevTx = proj₁ view
    v = (proj₁ ∘ proj₂) view
    prevOut∈ = (proj₁ ∘ proj₂ ∘ proj₂) view
    u∈ = (proj₁ ∘ proj₂ ∘ proj₂ ∘ proj₂) view
    prev∈ = (proj₁ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂) view
    prev∈utxo = (proj₁ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂) view
    getSpent≡ = (proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂) view

    tx′ : Σ[ tx ∈ Tx ] (verifyTx l tx tx≡ ≡ true)
    tx′ = mkTx {l} {s} {s′} {i} {vl} {vl~s} tx≡ sat

    tx      = proj₁ tx′
    verify≡ = proj₂ tx′

    --

    prevOut   = s —→ v at sm
    prevTxRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈)
    forge′    = forge tx

    --

    ptx = toPendingTx l tx fzero

    ptxOut : OutputInfo
    OutputInfo.value         ptxOut = forge′ +ᶜ v
    OutputInfo.validatorHash ptxOut = 𝕍
    OutputInfo.dataHash      ptxOut = (toData s′) ♯ᵈ

    state≡ : ⦇ stepₛₘ (fromData (toData s)) (fromData (toData i)) ⦈ ≡ pure (pure (s′ , tx≡))
    state≡ rewrite from∘to s | from∘to i | s→s′ = refl

    outs≡ : getContinuingOutputs ptx ≡ [ ptxOut ]
    outs≡ rewrite ≟-refl _≟ℕ_ 𝕍 = refl

    validate≡ : T (validatorₛₘ ptx (toData i) (toData s))
    validate≡ rewrite state≡
                    | final≡
                    | outs≡
                    | ≟-refl _≟ℕ_ (toData s′ ♯ᵈ)
                    | verify≡
                    = tt
    --

    txIn = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈) ←— (i , s) , sm

    vvh : M.Any ((𝕍 ≡_) ∘ address) (getSpentOutput txIn l)
    vvh rewrite getSpent≡ = M.just refl

    vtx : IsValidTx tx l
    withinInterval      vtx with range≡ tx≡
    ... | nothing = tt
    ... | pure _  rewrite range∋ = tt
    validOutputRefs     vtx = prev∈utxo ∷ []
    preservesValues     vtx rewrite getSpent≡ = M.just (sym (0+x≡x {x = forge′ +ᶜ v}))
    noDoubleSpending    vtx = [] ∷ []
    allInputsValidate   vtx = validate≡ ∷ []
    validateValidHashes vtx = vvh ∷ []
    forging             vtx with forge≡ tx≡
    ... | nothing = []
    ... | pure _  rewrite frg≡ = here vvh ∷ []

    vl′ : ValidLedger (tx ∷ l)
    vl′ = vl ⊕ tx ∶- vtx

    vl→vl′ : vl —→[ tx ∶- vtx ] vl′
    vl→vl′ = refl

    vl′~s′ : vl′ ~ s′
    vl′~s′ =
      ∈-map⁺ (dataHash ∘ out)
        (∈-filter⁺ ((_≟ℕ 𝕍) ∘ address ∘ out)
          (∈-++⁺ʳ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) (here refl))
          refl)
