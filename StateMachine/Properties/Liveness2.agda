module StateMachine.Properties.Liveness2 where

open import Function using (_∘_; case_of_)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (Bool; T; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Maybe   using (Maybe)
  renaming (just to pure; ap to _<*>_) -- to use idiom brackets
open import Data.Fin     using (Fin; toℕ; fromℕ<)
  renaming (suc to fsuc; zero to fzero)
open import Data.Nat     using (ℕ; _<_; z≤n; s≤s)
  renaming (_≟_ to _≟ℕ_)
open import Data.List    using (List; []; _∷_; [_]; map; length; filter; null)

open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Membership.Propositional  using (_∈_; find; mapWith∈)
open import Data.List.Membership.Propositional.Properties  using (find∘map)
open import Data.List.Relation.Unary.AllPairs   using ([]; _∷_)
open import Data.List.Relation.Unary.All        using ([]; _∷_)

open import Relation.Nullary                            using (¬_; yes; no)
open import Relation.Nullary.Decidable                  using (⌊_⌋)
open import Relation.Binary                             using (Decidable)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; trans; sym; inspect)
  renaming ([_] to ≡[_])
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import Prelude.Lists

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Hashing.MetaHash
open import UTxO.Types hiding (I)
open import StateMachine.Base

open PendingTxInput
open PendingTxOutput
open PendingTx

liveness′ : ∀ {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
              {s : S} {i : I} {s′ : S} {l : Ledger}
              {prevTx : Tx} {v : Value}

    -- `s —→[i] s′` constitutes a valid transition in the state machine
  → step sm s i ≡ pure s′

    -- we are not moving to a final state
  → isFinal sm s′ ≡ false

    -- existing ledger is valid
  → (vl : ValidLedger l)

    -- previous output is an element of previous transaction
  → (prevOut∈prevTx : s —→ $ v at sm ∈ outputs prevTx)

  → let prevTxRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈prevTx) in

    -- previous unspent output
    prevTxRef SETₒ.∈′ unspentOutputs l

    ---------------------------------------------------------------------------------------

  → ∃[ tx ]
       ( -- (1) new transaction is valid
         IsValidTx tx l
         -- (2) it contains the source state in its inputs, using the state machine's validator
       × (prevTxRef ←— i , sm ∈ inputs tx)
         -- (3) it contains the target state in its outputs
       × (s′ —→ $ v at sm ∈ outputs tx)
       )

liveness′ {S} {I} {sm} {s} {i} {s′} {l} {prevTx} {v} step≡ final≡ vl prevOut∈prevTx prev∈utxo
  = tx , vtx , here refl , here refl
  where
    ds  = toData s
    di  = toData i
    ds′ = toData s′
    𝕍  = (mkValidator sm) ♯

    prevTxRef : TxOutputRef
    prevTxRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈prevTx)

    prevOut : TxOutput
    value   prevOut = v
    address prevOut = 𝕍
    dataVal prevOut = ds

    tx : Tx
    inputs  tx = [ prevTxRef ←— i , sm ]
    outputs tx = [ s′ —→ $ v at sm ]
    forge   tx = $ 0
    fee     tx = $ 0

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
    value         ptxOut = v
    validatorHash ptxOut = 𝕍
    dataHash      ptxOut = ds′ ♯ᵈ

    state≡ : ⦇ step (pure sm) (fromData ds) (fromData di) ⦈ ≡ pure (pure s′)
    state≡ rewrite from∘to s | from∘to i | step≡ = refl

    outs≡ : getContinuingOutputs ptx ≡ [ ptxOut ]
    outs≡ rewrite ≟ℕ-refl {𝕍} = refl

    findData≡ : findData (PendingTxOutput.dataHash ptxOut) ptx ≡ pure ds′
    findData≡ rewrite ≟ℕ-refl {ds′ ♯ᵈ} = refl

    validate≡ : mkValidator sm ptx di ds ≡ true
    validate≡ rewrite state≡ | outs≡ | findData≡ | ≟ᵈ-refl {ds′} | final≡ = refl

    vtx : IsValidTx tx l
    validTxRefs         vtx = v₀
    validOutputIndices  vtx = v₁
    validOutputRefs     vtx _ (here refl) = prev∈utxo
    preservesValues     vtx rewrite lookupPrevOutput≡ = refl
    noDoubleSpending    vtx = [] ∷ []
    allInputsValidate   vtx _ (here refl) rewrite lookupPrevOutput≡ | validate≡ = tt
    validateValidHashes vtx _ (here refl) rewrite lookupPrevOutput≡ = refl
