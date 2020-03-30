open import Level          using (0ℓ)
open import Function       using (_∘_; _$_; case_of_)
open import Category.Monad using (RawMonad)

open import Data.Unit    using (tt)
open import Data.Bool    using (true; false)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax; proj₁; proj₂; map₁)
open import Data.Fin     using (toℕ)
  renaming (zero to fzero)
open import Data.Maybe   using (just; nothing; maybe)
open import Data.Nat     using ()
  renaming (_≟_ to _≟ℕ_)
open import Data.List    using (List; []; _∷_; [_]; filter; map)

open import Data.Bool.Properties using (T?)
  renaming (_≟_ to _≟𝔹_)

open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-filter⁺; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any as Any           using (Any; here; there)
import Data.List.Relation.Unary.Any.Properties as AnyP
open import Data.List.Relation.Unary.All as All           using (All; []; _∷_; all)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.List.Relation.Unary.AllPairs             using ([]; _∷_)

import Data.Maybe.Relation.Unary.Any as M
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Relation.Nullary           using (¬_)
open import Relation.Nullary.Decidable using (toWitness; ⌊_⌋; True)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; cong; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Prelude.General
open import Prelude.Lists

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities hiding (prevTx)
open import UTxO.Validity
open import StateMachine.Base

open InputInfo
open OutputInfo

module Bisimulation.Soundness
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open CEM {sm = sm}
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

soundness {s} {i} {s′} {tx≡} {l} {vl} final≡ s→s′ vl~s sat@(range∋ , sp≥ , apv)
-- *** Due to Agda bug, see https://github.com/personal-practice/agda/blob/master/bugs/With.agda
--   with mkTx {l} {s} {s′} {i} {vl} {vl~s} tx≡ sat
-- ... | tx , verify≡
--   with view-~ {vl = vl} vl~s
-- ... | prevTx , v , prevOut∈ , u∈ , prev∈ , prev∈utxo , getSpent≡ , threadToken≡
  = tx , vtx , vl′ , vl→vl′ , vl′~s′ , verify≡
  where
    -- *** Manually deconstructing here instead
    view         = view-~ {vl = vl} vl~s
    prevTx       = proj₁ view
    v            = (proj₁ ∘ proj₂) view
    prevOut∈     = (proj₁ ∘ proj₂ ∘ proj₂) view
    u∈           = (proj₁ ∘ proj₂ ∘ proj₂ ∘ proj₂) view
    prev∈        = (proj₁ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂) view
    prev∈utxo    = (proj₁ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂) view
    getSpent≡    = (proj₁ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂) view
    threadToken≡ = (proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ proj₂) view

    tx′ : Σ[ tx ∈ Tx ] (verifyTx l tx tx≡ ≡ true)
    tx′     = mkTx {l} {s} {s′} {i} {vl} {vl~s} tx≡ sat
    tx      = proj₁ tx′
    verify≡ = proj₂ tx′

    -- *** Constants

    prevOut   = s —→ v
    prevTxRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈)
    txIn      = prevTxRef ←— (i , s)
    forge′    = forge tx

    di  = toData i
    ds  = toData s
    ds′ = toData s′

    txOut : TxOutput
    txOut = record
      { value     = forge′ +ᶜ v
      ; address   = 𝕍
      ; datumHash = ds′ ♯ᵈ }

    ptx    = toPendingTx l tx fzero
    txi    = txInfo ptx
    ptxIn  = mkInputInfo l txIn
    ptxOut = mkOutputInfo txOut

    -- *** Valididty

    vtx : IsValidTx tx l
    withinInterval      vtx
      with range≡ tx≡
    ... | nothing = tt
    ... | just _  rewrite range∋ = tt

    validOutputRefs     vtx (here refl) = prev∈utxo
    validOutputRefs     vtx (there ())

    preservesValues     vtx
      rewrite getSpent≡
            = M.just (x+ᶜy+ᶜ0≡0+ᶜx+ᶜy+0 {x = forge′} {y = v})

    noDoubleSpending    vtx = [] ∷ []

    allInputsValidate   vtx = true⇒T validate≡ ∷ []
      where
        runStep≡ : join ⦇ stepₛₘ (fromData ds) (fromData di) ⦈ ≡ just (s′ , tx≡)
        runStep≡ rewrite from∘to s | from∘to i | s→s′ = refl

        thisVal≡ : thisValidator ptx ≡ 𝕍
        thisVal≡ = cong InputInfo.validatorHash (ptx-‼ {l} {tx} {txIn} {here refl})

        inputs≡ : inputsAt 𝕍 txi ≡ [ ptxIn ]
        inputs≡ = filter-singleton {P? = (𝕍 ≟ℕ_) ∘ InputInfo.validatorHash} (≟-refl _≟ℕ_ 𝕍)

        outputs≡ : outputsAt 𝕍 txi ≡ [ ptxOut ]
        outputs≡ = filter-singleton {P? = (𝕍 ≟ℕ_) ∘ OutputInfo.validatorHash} (≟-refl _≟ℕ_ 𝕍)

        getCont≡ : getContinuingOutputs ptx ≡ [ ptxOut ]
        getCont≡ =
          -- rewrite thisVal≡ | inputs≡
          begin
            getContinuingOutputs ptx
          ≡⟨⟩
            outputsAt (thisValidator ptx) txi
          ≡⟨ cong (λ x → outputsAt x txi) thisVal≡ ⟩
            outputsAt 𝕍 txi
          ≡⟨ outputs≡ ⟩
            [ ptxOut ]
          ∎

        outputsOK≡ : outputsOK ptx di ds s′ ≡ true
        outputsOK≡ rewrite final≡ | getCont≡ | ≟-refl _≟ℕ_ (ds′ ♯ᵈ) = refl

        valueAtⁱ≡ : valueAtⁱ 𝕍 txi ≡ v
        valueAtⁱ≡ =
          -- rewrite ≟-refl _≟ℕ_ 𝕍 | getSpent≡ = sum-single {v = v}
          begin
            valueAtⁱ 𝕍 txi
          ≡⟨⟩
            (sumᶜ ∘ map InputInfo.value) (inputsAt 𝕍 txi)
          ≡⟨ cong (sumᶜ ∘ map InputInfo.value) inputs≡ ⟩
            sumᶜ [ InputInfo.value ptxIn ]
          ≡⟨ sum-single ⟩
             maybe value [] (getSpentOutput l txIn)
          ≡⟨ cong (maybe value []) getSpent≡ ⟩
             v
          ∎

        valueAtᵒ≡ : valueAtᵒ 𝕍 txi ≡ forge′ +ᶜ v
        valueAtᵒ≡ =
          -- rewrite ≟-refl _≟ℕ_ 𝕍 | getSpent≡ = sum-single {v = forge′ +ᶜ v}
          begin
            (sumᶜ ∘ map OutputInfo.value ∘ outputsAt 𝕍) txi
          ≡⟨ cong (sumᶜ ∘ map OutputInfo.value) outputs≡ ⟩
             sumᶜ [ OutputInfo.value ptxOut ]
          ≡⟨ sum-single ⟩
             forge′ +ᶜ v
          ∎

        propagates≡ : propagates threadₛₘ ptx ≡ true
        propagates≡ = subst P (sym valueAtⁱ≡) threadToken≡
                ∧-× subst P (sym valueAtᵒ≡) P_v
          where
            P : Value → Set
            P = λ v → (v ≥ᶜ threadₛₘ) ≡ true

            P_v : P (forge′ +ᶜ v)
            P_v = T⇒true (≥ᶜ-+ᶜ {x = forge′} {y = v} {z = threadₛₘ} (true⇒T threadToken≡))

        validate≡ : validatorₛₘ ptx di ds ≡ true
        validate≡ = do-pure runStep≡ (outputsOK≡ ∧-× verify≡ ∧-× propagates≡)


    allPoliciesValidate vtx = apv tx

    validateValidHashes vtx = vvh ∷ []
      where
        vvh : M.Any (λ o → (address o ≡ 𝕍) × (datumHash o ≡ ds ♯ᵈ)) (getSpentOutput l txIn)
        vvh rewrite getSpent≡ = M.just (refl , refl)

    forging             vtx with
      forge≡ tx≡
    ... | nothing = []
    ... | just xs = All-Any-helper {xs = xs}
      where
        All-Any-helper : ∀ {xs : List (MonetaryPolicy × SubValue)}
          → All (λ c → Any ((c ≡_) ∘ _♯) (map proj₁ xs))
                (map proj₁ (map (map₁ _♯) xs))
        All-Any-helper {xs = xs}
          rewrite map-proj₁-map₁ {xs = xs} {f = _♯}
                = AllP.map⁺ $ All.map AnyP.map⁺ All-Any-refl

    vl′ : ValidLedger (tx ∷ l)
    vl′ = vl ⊕ tx ∶- vtx

    vl→vl′ : vl —→[ tx ∶- vtx ] vl′
    vl→vl′ = refl

    vl′~s′ : vl′ ~ s′
    vl′~s′ =
      ∈-map⁺ (datumHash ∘ out)
        (∈-filter⁺ ((_≟𝔹 true) ∘ (_≥ᶜ threadₛₘ) ∘ value ∘ out)
          (∈-filter⁺ ((𝕍 ≟ℕ_) ∘ address ∘ out)
            (∈-++⁺ʳ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) (here refl))
            refl)
          (T⇒true (≥ᶜ-+ᶜ {x = forge tx} {y = v} {z = threadₛₘ} (true⇒T threadToken≡))))
