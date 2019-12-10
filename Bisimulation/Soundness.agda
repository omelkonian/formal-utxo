open import Function using (_∘_; case_of_)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (Bool; T; true; false; if_then_else_; not)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Maybe   using (Maybe; fromMaybe; nothing)
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

module Bisimulation.Soundness
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open import Bisimulation.Base {sm = sm}

soundness : ∀ {s i s′ tx≡ l} {vl : ValidLedger l}
  → ¬ (T (finalₛₘ s′))
  → s —→[ i ] (s′ , tx≡)
  → vl ~ s
  → l -compliesTo- tx≡

    --------------------------

  → ∃[ tx ] ∃[ vtx ] ∃[ vl′ ]
      ( vl —→[ tx ∶- vtx ] vl′
      × vl′ ~ s′ )
soundness {s} {i} {s′} {ptx≡} {l} {vl} ¬fin s→s′ vl~s range∋l
  with view-~ {l} {s} {vl} vl~s
... | u@(record { out = record {value = v} ; prevTx = prevTx }) , u∈ , prevTx∈ , _ , _ , prevOut∈ , _ , prev∈utxo
  = tx , vtx , vl′ , vl→vl′ , vl′~s′
  where
    final≡ : finalₛₘ s′ ≡ false
    final≡ with finalₛₘ s′
    ... | true  = ⊥-elim (¬fin tt)
    ... | false = refl

    prevTx♯∈ : Any (λ tx → tx ♯ₜₓ ≡ prevTx ♯ₜₓ) l
    prevTx♯∈ = Any.map (cong _♯ₜₓ ∘ sym) prevTx∈

    prevOut   = s —→ $ v at sm
    prevTxRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈)
    forge′    = fromMaybe ($ 0) (forge≡ ptx≡)
    range′    = fromMaybe (-∞ ⋯ +∞) (range≡ ptx≡)


    tx′ : Σ[ tx ∈ Tx ] (verifyTx tx ptx≡ ≡ true)
    tx′ = constraint ptx≡ record { inputs =  [ prevTxRef ←— i , sm ]
                                 ; outputs = [ s′ —→ $ (v + forge′) at sm ]
                                 ; forge   = $ 0
                                 ; fee     = $ 0
                                 ; range   = -∞ ⋯ +∞ }

    tx      = proj₁ tx′
    verify≡ = proj₂ tx′

    lookupPrevTx≡ : lookupTx l prevTxRef prevTx♯∈ ≡ prevTx
    lookupPrevTx≡
      rewrite find∘map {Q = λ tx → tx ♯ₜₓ ≡ prevTx ♯ₜₓ} prevTx∈ (cong _♯ₜₓ ∘ sym)
            | proj₁∘find prevTx∈
            = refl

    len< : index prevTxRef < length (outputs (lookupTx l prevTxRef prevTx♯∈))
    len< rewrite lookupPrevTx≡ = toℕ< (Any.index prevOut∈)

    lookupPrevOutput≡ : lookupOutput l prevTxRef prevTx♯∈ len< ≡ prevOut
    lookupPrevOutput≡
      rewrite lookupPrevTx≡
            | ‼-fromℕ<∘toℕ< {xs = outputs prevTx} (Any.index prevOut∈)
            | ‼-index prevOut∈
            = refl

    v₀ : ∀ i → i ∈ inputs tx → Any (λ t → t ♯ₜₓ ≡ id (outputRef i)) l
    v₀ _ (here refl) = prevTx♯∈

    v₁ : ∀ i → (i∈ : i ∈ inputs tx) → index (outputRef i) < length (outputs (lookupTx l (outputRef i) (v₀ i i∈)))
    v₁ _ (here refl) = len<

    ptx = mkPendingTx l tx (prevTxRef ←— i , sm) (here refl) v₀ v₁

    ptxOut : PendingTxOutput
    value         ptxOut = v + forge′
    validatorHash ptxOut = 𝕍
    dataHash      ptxOut = (toData s′) ♯ᵈ

    state≡ : ⦇ stepₛₘ (fromData (toData s)) (fromData (toData i)) ⦈ ≡ pure (pure (s′ , ptx≡))
    state≡ rewrite from∘to s | from∘to i | s→s′ = refl

    outs≡ : getContinuingOutputs ptx ≡ [ ptxOut ]
    outs≡ rewrite ≟-refl _≟ℕ_ 𝕍 = refl

    findData≡ : findData (PendingTxOutput.dataHash ptxOut) ptx ≡ pure (toData s′)
    findData≡ rewrite ≟-refl _≟ℕ_ ((toData s′)♯ᵈ) = refl

    validate≡ : mkValidator sm ptx (toData i) (toData s) ≡ true
    validate≡ rewrite state≡ | outs≡ | findData≡ | ≟-refl _≟ᵈ_ (toData s′) | final≡ | verify≡ = refl

    vtx : IsValidTx tx l
    validTxRefs         vtx = v₀
    validOutputIndices  vtx = v₁
    validOutputRefs     vtx _ (here refl) = prev∈utxo
    preservesValues     vtx rewrite lookupPrevOutput≡ = (x+y+0≡y+x+0 (fromMaybe ($ 0) (forge≡ ptx≡)) v)
    noDoubleSpending    vtx = [] ∷ []
    allInputsValidate   vtx _ (here refl) rewrite lookupPrevOutput≡ | validate≡ = tt
    validateValidHashes vtx _ (here refl) rewrite lookupPrevOutput≡ = refl
    validInterval       vtx = range∋l

    vl′ : ValidLedger (tx ∷ l)
    vl′ = vl ⊕ tx ∶- vtx

    vl→vl′ : vl —→[ tx ∶- vtx ] vl′
    vl→vl′ = refl

    vl′~s′ : vl′ ~ s′
    vl′~s′ rewrite sym (from∘to s′)
         = ∈-map⁺ (fromData ∘ dataVal ∘ out)
             (∈-filter⁺ ((_≟ℕ 𝕍) ∘ address ∘ out)
               (∈-++⁺ʳ (filter ((SETₒ._∉? map outputRef (inputs tx)) ∘ outRef) (utxo l)) (here refl)) refl)
