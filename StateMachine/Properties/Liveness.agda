module StateMachine.Properties.Liveness where

open import Function using (_∘_; case_of_)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (Bool; T; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Maybe   using (Maybe; fromMaybe; nothing)
  renaming (just to pure; ap to _<*>_) -- to use idiom brackets
open import Data.Fin     using (Fin; toℕ; fromℕ<)
  renaming (suc to fsuc; zero to fzero)
open import Data.Nat     using (ℕ; _<_; z≤n; s≤s; _+_)
  renaming (_≟_ to _≟ℕ_)
open import Data.List    using (List; []; _∷_; [_]; map; length; filter; null)

open import Data.Bool.Properties using (T?)

open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Membership.Propositional  using (_∈_; find; mapWith∈)
open import Data.List.Membership.Propositional.Properties  using (find∘map)
open import Data.List.Relation.Unary.AllPairs   using ([]; _∷_)
open import Data.List.Relation.Unary.All        using ([]; _∷_)

open import Relation.Nullary                            using (¬_; yes; no)
open import Relation.Nullary.Decidable                  using (⌊_⌋; toWitness)
open import Relation.Binary                             using (Decidable)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; trans; sym; inspect)
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

liveness : ∀ {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
             {s : S} {i : I} {s′ : S} {l : Ledger}
             {prevTx : Tx} {v : Value} {ptx≡ : TxConstraints}

    -- `s —→[i] s′` constitutes a valid transition in the state machine
  → step sm s i ≡ pure (s′ , ptx≡)

    -- if we are moving to a final state, make sure no value is carried around
  → (T (isFinal sm s′) → (v ≡ 0) × (forge≡ ptx≡ ≡ nothing))

    -- existing ledger is valid
  → (vl : ValidLedger l)
  → l -compliesTo- ptx≡

    -- previous output is an element of previous transaction
  → (prevOut∈prevTx : s —→ $ v at sm ∈ outputs prevTx)

  → let prevTxRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈prevTx)
        txIn      = prevTxRef ←— i , sm
        v′        = v + fromMaybe ($ 0) (forge≡ ptx≡)
    in

    -- previous unspent output
    prevTxRef SETₒ.∈′ unspentOutputs l

    ---------------------------------------------------------------------------------------

  → ∃[ tx ](
      -- (1) new transaction is valid
      Σ[ vtx ∈ IsValidTx tx l ]
      -- (2) it contains the source state in its inputs, using the state machine's validator
      Σ[ i∈  ∈ (txIn ∈ inputs tx) ]
        let ptx = mkPendingTx l tx txIn i∈ (validTxRefs vtx) (validOutputIndices vtx) in
      -- (3) it contains the target state in its outputs
           (¬ T (isFinal sm s′) → s′ —→ $ v′ at sm ∈ outputs tx)
      -- (4) it satisfied the constraints imposed by the state machine
         × T (verifyPtx ptx ptx≡))

liveness {S} {I} {sm} {s} {i} {s′} {l} {prevTx} {v} {ptx≡} step≡ val≡ vl range∋l prevOut∈prevTx prev∈utxo
  with isFinal sm s′ | inspect (isFinal sm) s′
... | true | ≡[ final≡ ]
    = tx , vtx , here refl , (λ ¬fin → ⊥-elim (¬fin tt)) , true⇒T verify≡
  where
    𝕍 = (mkValidator sm) ♯
    prevTxRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈prevTx)
    prevOut   = s —→ $ v at sm
    forge′    = fromMaybe ($ 0) (forge≡ ptx≡)
    range′    = fromMaybe (-∞ ⋯ +∞) (range≡ ptx≡)

    tx′ : Σ[ tx ∈ Tx ] (verifyTx tx ptx≡ ≡ true)
    tx′ = constraint ptx≡ record { inputs =  [ prevTxRef ←— i , sm ]
                                 ; outputs = []
                                 ; forge   = $ 0
                                 ; fee     = $ 0
                                 ; range   = -∞ ⋯ +∞ }

    tx      = proj₁ tx′
    verify≡ = proj₂ tx′

    prevTx∈ : prevTx ∈ l
    prevTx∈ = tx♯∈⇒tx∈ prev∈utxo

    prevTx♯∈ : Any (λ tx → tx ♯ₜₓ ≡ prevTx ♯ₜₓ) l
    prevTx♯∈ = Any.map (cong _♯ₜₓ ∘ sym) prevTx∈

    lookupPrevTx≡ : lookupTx l prevTxRef prevTx♯∈ ≡ prevTx
    lookupPrevTx≡
      rewrite find∘map {Q = λ tx → tx ♯ₜₓ ≡ prevTx ♯ₜₓ} prevTx∈ (cong _♯ₜₓ ∘ sym)
            | proj₁∘find prevTx∈
            = refl

    len< : index prevTxRef < length (outputs (lookupTx l prevTxRef prevTx♯∈))
    len< rewrite lookupPrevTx≡ = toℕ< (Any.index prevOut∈prevTx)

    lookupPrevOutput≡ : lookupOutput l prevTxRef prevTx♯∈ len< ≡ prevOut
    lookupPrevOutput≡
      rewrite lookupPrevTx≡
            | ‼-fromℕ<∘toℕ< {xs = outputs prevTx} (Any.index prevOut∈prevTx)
            | ‼-index prevOut∈prevTx
            = refl

    state≡ : ⦇ step (pure sm) (fromData (toData s)) (fromData (toData i)) ⦈ ≡ pure (pure (s′ , ptx≡))
    state≡ rewrite from∘to s | from∘to i | step≡ = refl

    vtx : IsValidTx tx l
    validTxRefs         vtx _ (here refl) = prevTx♯∈
    validOutputIndices  vtx _ (here refl) = len<
    validOutputRefs     vtx _ (here refl) = prev∈utxo
    preservesValues     vtx rewrite lookupPrevOutput≡ | final≡ | proj₁ (val≡ tt) | proj₂ (val≡ tt) = refl
    noDoubleSpending    vtx = [] ∷ []
    allInputsValidate   vtx _ (here refl) rewrite lookupPrevOutput≡ | state≡ | final≡ | verify≡ = tt
    validateValidHashes vtx _ (here refl) rewrite lookupPrevOutput≡ = refl
    validInterval       vtx = range∋l
... | false | ≡[ final≡ ]
    = tx , vtx , here refl , (λ _ → here refl) , true⇒T verify≡
  where
    𝕍  = (mkValidator sm) ♯

    prevTxRef : TxOutputRef
    prevTxRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈prevTx)

    prevOut : TxOutput
    prevOut = s —→ $ v at sm

    forge′ : Value
    forge′ = fromMaybe ($ 0) (forge≡ ptx≡)

    range′ : SlotRange
    range′ = fromMaybe (-∞ ⋯ +∞) (range≡ ptx≡)

    tx′ : Σ[ tx ∈ Tx ] (verifyTx tx ptx≡ ≡ true)
    tx′ = constraint ptx≡ record { inputs =  [ prevTxRef ←— i , sm ]
                                 ; outputs = [ s′ —→ $ (v + forge′) at sm ]
                                 ; forge   = $ 0
                                 ; fee     = $ 0
                                 ; range   = -∞ ⋯ +∞ }

    tx      = proj₁ tx′
    verify≡ = proj₂ tx′

    prevTx∈ : prevTx ∈ l
    prevTx∈ = tx♯∈⇒tx∈ prev∈utxo

    prevTx♯∈ : Any (λ tx → tx ♯ₜₓ ≡ prevTx ♯ₜₓ) l
    prevTx♯∈ = Any.map (cong _♯ₜₓ ∘ sym) prevTx∈

    lookupPrevTx≡ : lookupTx l prevTxRef prevTx♯∈ ≡ prevTx
    lookupPrevTx≡
      rewrite find∘map {Q = λ tx → tx ♯ₜₓ ≡ prevTx ♯ₜₓ} prevTx∈ (cong _♯ₜₓ ∘ sym)
            | proj₁∘find prevTx∈
            = refl

    len< : index prevTxRef < length (outputs (lookupTx l prevTxRef prevTx♯∈))
    len< rewrite lookupPrevTx≡ = toℕ< (Any.index prevOut∈prevTx)

    lookupPrevOutput≡ : lookupOutput l prevTxRef prevTx♯∈ len< ≡ prevOut
    lookupPrevOutput≡
      rewrite lookupPrevTx≡
            | ‼-fromℕ<∘toℕ< {xs = outputs prevTx} (Any.index prevOut∈prevTx)
            | ‼-index prevOut∈prevTx
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

    state≡ : ⦇ step (pure sm) (fromData (toData s)) (fromData (toData i)) ⦈ ≡ pure (pure (s′ , ptx≡))
    state≡ rewrite from∘to s | from∘to i | step≡ = refl

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
