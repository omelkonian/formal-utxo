open import Function using (_∘_; case_of_)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (Bool; T; true; false; if_then_else_; not)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Maybe   using (Maybe; fromMaybe; nothing; maybe′)
  renaming (just to pure; ap to _<*>_) -- to use idiom brackets
open import Data.Fin     using (Fin; toℕ; fromℕ<)
  renaming (suc to fsuc; zero to fzero)
open import Data.Nat     using (ℕ; _<_; z≤n; s≤s; _+_)
  renaming (_≟_ to _≟ℕ_)
open import Data.List    using (List; []; _∷_; [_]; map; length; filter; null)

open import Data.Bool.Properties  using (T?)
open import Data.Maybe.Properties using (just-injective)

open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Membership.Propositional  using (_∈_; _∉_; find; mapWith∈)
open import Data.List.Membership.Propositional.Properties
  using (find∘map; ∈-map⁻; ∈-map⁺; ∈-filter⁻; ∈-filter⁺; ∈-++⁻; ∈-++⁺ʳ; ∈-++⁺ˡ)
open import Data.List.Relation.Unary.AllPairs   using ([]; _∷_)
open import Data.List.Relation.Unary.All        using ([]; _∷_)

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
open import UTxO.Hashing.MetaHash
open import UTxO.Types hiding (I)
open import StateMachine.Base

open PendingTxInput
open PendingTxOutput
open PendingTx

module Bisimulation.Completeness
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open import Bisimulation.Base {sm = sm}

completeness : ∀ {s tx l} {vtx : IsValidTx tx l} {vl : ValidLedger l} {vl′ : ValidLedger (tx ∷ l)}
  → vl —→[ tx ∶- vtx ] vl′
  → vl ~ s
    ----------------------------------------------
  → (∃[ i ] ∃[ s′ ] ∃[ tx≡ ]
      ( s —→[ i ] (s′ , tx≡)
      × (¬ (T (finalₛₘ s′)) → vl′ ~ s′) ) )
  ⊎ (vl′ ~ s)
completeness {s} {tx} {l} {vtx} {vl} {vl′} vl→vl′ vl~s
  with view-~ {l} {s} {vl} vl~s
... | u , u∈ , _ , refl , refl , prevOut∈ , refl , _
  with ((prevTx u) ♯ₜₓ) indexed-at (toℕ (Any.index prevOut∈)) SETₒ.∈? map outputRef (inputs tx)
... | no  prev∉
  rewrite sym (from∘to s)
    = inj₂ (∈-map⁺ (fromData ∘ dataVal ∘ out)
             (∈-filter⁺ ((_≟ℕ 𝕍) ∘ address ∘ out)
               (∈-++⁺ˡ (∈-filter⁺ ((SETₒ._∉? map outputRef (inputs tx)) ∘ outRef) {x = u} {xs = utxo l}
                 u∈ prev∉)) refl))
... | yes prev∈
  with ∈-map⁻ outputRef prev∈
... | txIn , txIn∈ , refl
  with validateValidHashes vtx txIn txIn∈
... | addr≡val
    = inj₁ (STEP (validate≡ {ptx = ptx} (allInputsValidate vtx txIn txIn∈)))
  where
    prevTxRef = ((prevTx u) ♯ₜₓ) indexed-at (toℕ (Any.index prevOut∈))
    prevOut    = s —→ $ (value (out u)) at sm

    v₁ = validTxRefs vtx
    v₂ = validOutputIndices vtx

    ∃tx≡id : Any (λ tx′ → tx′ ♯ₜₓ ≡ id prevTxRef) l
    ∃tx≡id = v₁ txIn txIn∈

    proj₁∘find∘♯ : ∀ {l : Ledger} {tx₂ : Tx}
      → (any≡ : Any (λ tx₁ → tx₁ ♯ₜₓ ≡ tx₂ ♯ₜₓ) l)
      → proj₁ (find any≡)
      ≡ tx₂
    proj₁∘find∘♯ (here px)  = injective♯ₜₓ px
    proj₁∘find∘♯ (there x∈) = proj₁∘find∘♯ x∈

    lookupPrevTx≡ : lookupTx l prevTxRef ∃tx≡id
                  ≡ prevTx u
    lookupPrevTx≡ = proj₁∘find∘♯ ∃tx≡id

    len<′ : index prevTxRef < length (outputs (lookupTx l prevTxRef ∃tx≡id))
    len<′ = v₂ txIn txIn∈

    len< : index prevTxRef < length (outputs (prevTx u))
    len< = toℕ< (Any.index prevOut∈)

    out′ = lookupOutput l (outputRef txIn) ∃tx≡id len<′

    lookupOutput≡ : out′
                  ≡ prevOut
    lookupOutput≡ = trans h₁ h₂
      where
        h₁ : (outputs (lookupTx l prevTxRef ∃tx≡id) ‼ (fromℕ< len<′))
           ≡ (outputs (prevTx u) ‼ (fromℕ< len<))
        h₁ = ‼-fromℕ<-≡ len<′ len< (cong outputs lookupPrevTx≡)

        h₂ : (outputs (prevTx u) ‼ (fromℕ< len<))
           ≡ prevOut
        h₂ rewrite ‼-fromℕ<∘toℕ< {xs = outputs (prevTx u)} (Any.index prevOut∈)
                 | ‼-index prevOut∈
                 = refl

    valTxIn≡ : ((validator txIn) ♯) ≡ 𝕍
    valTxIn≡ = trans (sym addr≡val) (addr≡)
      where
        addr≡ : address out′ ≡ 𝕍
        addr≡ rewrite lookupOutput≡ = refl


    ptx = mkPendingTx l tx txIn txIn∈ v₁ v₂
    di  = redeemer txIn
    ds  = toData s

    validate≡ : ∀ {ptx : PendingTx}
       → T (runValidation ptx txIn out′)
       → T (validatorₛₘ ptx di ds)
    validate≡ p rewrite lookupOutput≡ | ♯-injective valTxIn≡ = p

    STEP :
        T (validatorₛₘ ptx di (toData s))
         -------------------------------------------------------------
      → ∃[ i ] ∃[ s′ ] ∃[ tx≡ ]
          ( (stepₛₘ s i ≡ pure (s′ , tx≡))
          × ( ¬ (T (finalₛₘ s′))
            → pure s′ ∈ ( map (fromData ∘ dataVal ∘ out)
                        ∘ filter ((_≟ℕ 𝕍) ∘ address ∘ out)
                        ) (utxo (tx ∷ l))))
    STEP eq
      rewrite from∘to s
      with ⦇ stepₛₘ (pure s) (fromData di) ⦈
         | inspect (λ x → ⦇ stepₛₘ (pure s) x ⦈) (fromData di)
         | eq
    ... | nothing | _        | ()
    ... | pure r  | ≡[ eq′ ] | eq²
      with fromData {A = I} di | eq′
    ... | nothing | eq″ = ⊥-elim (ap-nothing {m = maybe′ (pure ∘ stepₛₘ) nothing (pure s)} eq″)
    ... | pure i  | eq″
      with stepₛₘ s i | inspect (stepₛₘ s) i | eq
    ... | nothing         | _          | ()
    ... | pure (s′ , tx≡) | ≡[ step≡ ] | _
      rewrite step≡
      with finalₛₘ s′
         | inspect finalₛₘ s′
         | getContinuingOutputs (mkPendingTx l tx txIn txIn∈ v₁ v₂)
         | inspect getContinuingOutputs (mkPendingTx l tx txIn txIn∈ v₁ v₂)
    ... | true  | ≡[ final≡ ] | []       | _
        = i , s′ , tx≡ , step≡ , λ ¬fin → ⊥-elim (¬fin (true⇒T final≡))
    ... | false | ≡[ final≡ ] | (o ∷ []) | ≡[ out≡ ]
      with findData (PendingTxOutput.dataHash o) (mkPendingTx l tx txIn txIn∈ v₁ v₂)
         | inspect (findData (PendingTxOutput.dataHash o)) (mkPendingTx l tx txIn txIn∈ v₁ v₂)
         | eq
    ... | nothing | _          | ()
    ... | pure ds | ≡[ find≡ ] | eq₂
      with ds ≟ᵈ toData s′ | eq₂
    ... | no ¬p    | ()
    ... | yes refl | _
      with singleton→∈ (_ , out≡)
    ... | o∈₀
      with ∈-filter⁻ ((_≟ℕ (validator txIn) ♯) ∘ PendingTxOutput.validatorHash)
                     {v = o} {xs = map mkPendingTxOut (outputs tx)}
                     o∈₀
    ... | o∈ , val≡′
      with ∈-map⁻ mkPendingTxOut o∈
    ... | o′ , o′∈ , f≡
        = i , s′ , tx≡ , step≡ , λ _ → helper
        where
          data♯≡ : PendingTxOutput.dataHash o ≡ (dataVal o′) ♯ᵈ
          data♯≡ = cong PendingTxOutput.dataHash f≡

          find≡′ : findData ((dataVal o′) ♯ᵈ) ((mkPendingTx l tx txIn txIn∈ v₁ v₂)) ≡ pure (toData s′)
          find≡′ rewrite sym data♯≡ = find≡

          fromData≡ : dataVal o′ ≡ toData s′
          fromData≡
            rewrite sym (from∘to s′)
            with ∈-map⁻ proj₂ (singleton→∈ (toMaybe-≡ find≡′))
          ... | x , x∈ , x≡
            with ∈-filter⁻ ((_≟ℕ (dataVal o′) ♯ᵈ) ∘ proj₁) {xs = PendingTx.dataWitnesses (mkPendingTx l tx txIn txIn∈ v₁ v₂)} x∈
          ... | y∈ , y≡
            with ∈-map⁻ (λ o → ((dataVal o) ♯ᵈ) , dataVal o) y∈
          ... | _ , _ , refl
              = trans (sym (injective♯ᵈ y≡)) (sym x≡)

          val♯≡ : PendingTxOutput.validatorHash o ≡ (validator txIn) ♯
          val♯≡ rewrite val≡′ = refl

          addr≡ : address o′ ≡ (validator txIn) ♯
          addr≡ rewrite sym val♯≡ = sym (cong PendingTxOutput.validatorHash f≡)

          helper : pure s′ ∈ ( map (fromData ∘ dataVal ∘ out)
                             ∘ filter ((_≟ℕ 𝕍) ∘ address ∘ out)
                             ) (utxo (tx ∷ l))
          helper
            rewrite sym (from∘to s′)
                  | sym fromData≡
            with mapWith∈⁺ {B = UTXO} {x = o′} {xs = outputs tx}
                           {f = λ {out} out∈ → record { outRef   = (tx ♯ₜₓ) indexed-at toℕ (Any.index out∈)
                                                      ; out      = out
                                                      ; prevTx   = tx }}
                           o′∈
          ... | u , u∈ , refl
              = ∈-map⁺ (fromData ∘ dataVal ∘ out) {x = u}
                  (∈-filter⁺ ((_≟ℕ 𝕍) ∘ address ∘ out) {x = u} {xs = utxo (tx ∷ l)}
                    (∈-++⁺ʳ (filter ((SETₒ._∉? map outputRef (inputs tx)) ∘ outRef) (utxo l)) u∈)
                      (trans addr≡ valTxIn≡))
