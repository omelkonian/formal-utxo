open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-filter⁺; ∈-++⁺ʳ)

open import Prelude.Init
open import Prelude.General
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Membership
open import Prelude.ToN
open import Prelude.Bifunctor
open import Prelude.Applicative
open import Prelude.Monad

open import UTxO.Hashing
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities hiding (prevTx)
open import UTxO.Validity
open import StateMachine.Base

open InputInfo

module Bisimulation.Soundness
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open CEM {sm = sm}
open import Bisimulation.Base {sm = sm}
open ≡-Reasoning

soundness : ∀ {s i s′ tx≡ l} {vl : ValidLedger l}
--  → finalₛₘ s′ ≡ false
  → s —→[ i ] (s′ , tx≡)
  → (vl~s : vl ~ s)
  → Satisfiable {vl = vl} tx≡ vl~s
    --------------------------------
  → ∃[ tx ] ∃[ vtx ] ∃[ vl′ ]
      ( vl —→[ tx ∶- vtx ] vl′
      × vl′ ~ s′
      × (verifyTx l tx tx≡ ≡ true) )

soundness {s} {i} {s′} {tx≡} {l} {vl} {- final≡ -} s→s′ vl~s sat@(range∋ , sp≥ , apv)
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
    prevTxRef = (prevTx ♯ₜₓ) indexed-at toℕ (L.Any.index prevOut∈)
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

    ptx   = toPendingTx l tx 0F
    txi   = txInfo ptx
    ptxIn = mkInputInfo l txIn

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
            = M.Any.just (x+ᶜy+ᶜ0≡x+ᶜy+0 {x = forge′} {y = v})

    noDoubleSpending    vtx = [] ∷ []

    allInputsValidate   vtx = true⇒T validate≡ ∷ []
      where
        runStep≡ : join ⦇ stepₛₘ (fromData ds) (fromData di) ⦈ ≡ just (s′ , tx≡)
        runStep≡ rewrite from∘to s | from∘to i | s→s′ = refl

        thisVal≡ : thisValidator ptx ≡ 𝕍
        thisVal≡ = cong InputInfo.validatorHash (ptx-‼ {l} {tx} {txIn} {here refl})

        inputs≡ : inputsAt 𝕍 txi ≡ [ ptxIn ]
        inputs≡ = filter-singleton {P? = (𝕍 ≟_) ∘ InputInfo.validatorHash} (≟-refl 𝕍)

        outputs≡ : outputsAt 𝕍 txi ≡ [ txOut ]
        outputs≡ = filter-singleton {P? = (𝕍 ≟_) ∘ address} (≟-refl 𝕍)

        getCont≡ : getContinuingOutputs ptx ≡ [ txOut ]
        getCont≡ =
          -- rewrite thisVal≡ | inputs≡
          begin
            getContinuingOutputs ptx
          ≡⟨⟩
            outputsAt (thisValidator ptx) txi
          ≡⟨ cong (λ x → outputsAt x txi) thisVal≡ ⟩
            outputsAt 𝕍 txi
          ≡⟨ outputs≡ ⟩
            [ txOut ]
          ∎

        outputsOK≡ : outputsOK ptx di ds s′ ≡ true
        outputsOK≡ rewrite {- final≡ | -} getCont≡ | ≟-refl (ds′ ♯ᵈ) = refl

        valueAtⁱ≡ : valueAtⁱ 𝕍 txi ≡ v
        valueAtⁱ≡ =
          -- rewrite ≟-refl 𝕍 | getSpent≡ = sum-single {v = v}
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
          -- rewrite ≟-refl 𝕍 | getSpent≡ = sum-single {v = forge′ +ᶜ v}
          begin
            (sumᶜ ∘ map value ∘ outputsAt 𝕍) txi
          ≡⟨ cong (sumᶜ ∘ map value) outputs≡ ⟩
             sumᶜ [ value txOut ]
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
        vvh : M.Any.Any (λ o → (address o ≡ 𝕍) × (datumHash o ≡ ds ♯ᵈ)) (getSpentOutput l txIn)
        vvh rewrite getSpent≡ = M.Any.just (refl , refl)

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
                = L.All.map⁺ $ L.All.map L.Any.map⁺ All-Any-refl

    vl′ : ValidLedger (tx ∷ l)
    vl′ = vl ⊕ tx ∶- vtx

    vl→vl′ : vl —→[ tx ∶- vtx ] vl′
    vl→vl′ = refl

    vl′~s′ : vl′ ~ s′
    vl′~s′ =
      ∈-map⁺ (datumHash ∘ out)
        (∈-filter⁺ ((_≟ true) ∘ (_≥ᶜ threadₛₘ) ∘ value ∘ out)
          (∈-filter⁺ ((𝕍 ≟_) ∘ address ∘ out)
            (∈-++⁺ʳ (filter ((_∉? outputRefs tx) ∘ outRef) (utxo l)) (here refl))
            refl)
          (T⇒true (≥ᶜ-+ᶜ {x = forge tx} {y = v} {z = threadₛₘ} (true⇒T threadToken≡))))
