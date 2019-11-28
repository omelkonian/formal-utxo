module StateMachine.Properties.Liveness where

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
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; sym; inspect)
  renaming ([_] to ≡[_])
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import Prelude.Lists

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Hashing.MetaHash
open import UTxO.Types hiding (I)
open import StateMachine.Base

Address = HashId

open import UTxO.Ledger      Address (λ x → x) _≟ℕ_
open import UTxO.TxUtilities Address (λ x → x) _≟ℕ_
open import UTxO.Hashing.Tx  Address (λ x → x) _≟ℕ_
open import UTxO.Validity    Address (λ x → x) _≟ℕ_

liveness : ∀ {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
             {s : S} {i : I} {s′ : S} {l : Ledger}
             {prevTx : Tx} {v : Value}

    -- `s —→[i] s′` constitutes a valid transition in the state machine
  → step sm s i ≡ pure s′

    -- if we are moving to a final state, make sure no value is carried around
  → (T (isFinal sm s′) → v ≡ 0)

    -- existing ledger is valid
  → (vl : ValidLedger l)

    -- previous output is an element of previous transaction
  → (prevOut∈prevTx : record {value = v; address = (mkValidator sm) ♯; dataVal = toData s} ∈ outputs prevTx)

  → let prevTxRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈prevTx) in

    -- previous unspent output
    prevTxRef ∈ SETₒ.list (unspentOutputs l)

    ---------------------------------------------------------------------------------------

  → ∃[ tx ]
       ( -- (1) new transaction is valid
         IsValidTx tx l
         -- (2) it contains the source state in its inputs, using the state machine's validator
       × Any (λ i → (outputRef i ≡ prevTxRef) × ((validator i) ♯ ≡ (mkValidator sm) ♯)) (inputs tx)
         -- (3) it contains the target state in its outputs
       × (¬ T (isFinal sm s′) → Any ((_≡ pure s′) ∘ fromData ∘ dataVal) (outputs tx))
       )

liveness {S} {I} {sm} {s} {i} {s′} {l} {prevTx} {v} step≡ val≡ vl prevOut∈prevTx prev∈utxo
  with isFinal sm s′ | inspect (isFinal sm) s′
... | true | ≡[ final≡ ] = tx , vtx , here (refl , refl) , λ ¬fin → ⊥-elim (¬fin tt)
  where
    𝕍  = (mkValidator sm) ♯

    -- Create a transaction input.
    _at_←—_ : Tx → ℕ → I → TxInput
    outputRef (t at i ←— _) = (t ♯ₜₓ) indexed-at i
    redeemer  (_ at _ ←— d) = toData d
    validator (_ at _ ←— _) = mkValidator sm

    -- Create a transaction output.
    _—→_at_ : S → Value → Address → TxOutput
    value   (_ —→ v at _) = v
    address (_ —→ _ at a) = a
    dataVal (d —→ _ at _) = toData d

    prevTxRef : TxOutputRef
    prevTxRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈prevTx)

    j = index prevTxRef

    prevOut : TxOutput
    prevOut = record {value = v; address = 𝕍; dataVal = toData s}

    tx : Tx
    inputs  tx = [ prevTx at j ←— i ]
    outputs tx = []
    forge   tx = $0
    fee     tx = $0

    prevTx∈ : prevTx ∈ l
    prevTx∈ = tx♯∈⇒tx∈ prev∈utxo

    prevTx♯∈ : Any (λ tx → tx ♯ₜₓ ≡ prevTx ♯ₜₓ) l
    prevTx♯∈ = Any.map (cong _♯ₜₓ ∘ sym) prevTx∈

    prevTx′ = lookupTx l prevTxRef prevTx♯∈

    lookupPrevTx≡ : lookupTx l prevTxRef prevTx♯∈ ≡ prevTx
    lookupPrevTx≡
      rewrite find∘map {Q = λ tx → tx ♯ₜₓ ≡ prevTx ♯ₜₓ} prevTx∈ (cong _♯ₜₓ ∘ sym)
            | proj₁∘find prevTx∈
            = refl

    len<′ : index prevTxRef < length (outputs prevTx)
    len<′ = toℕ< (Any.index prevOut∈prevTx)

    len< : index prevTxRef < length (outputs prevTx′)
    len< rewrite lookupPrevTx≡ = len<′

    lookupPrevOutput≡ : lookupOutput l prevTxRef prevTx♯∈ len< ≡ prevOut
    lookupPrevOutput≡
      rewrite lookupPrevTx≡
            | ‼-fromℕ<∘toℕ< {xs = outputs prevTx} (Any.index prevOut∈prevTx)
            | ‼-index prevOut∈prevTx
            = refl

    lookupValue≡ : lookupValue l (prevTx at j ←— i) prevTx♯∈ len< ≡ v
    lookupValue≡ rewrite lookupPrevOutput≡ = refl

    addr≡′ : address (lookupOutput l prevTxRef prevTx♯∈ len<) ≡ 𝕍
    addr≡′ rewrite lookupPrevOutput≡ = refl

    v₀ :
      ∀ i → i ∈ inputs tx →
        Any (λ t → t ♯ₜₓ ≡ id (outputRef i)) l
    v₀ _ (here refl) = prevTx♯∈
    v₀ _ (there ())

    v₁ :
      ∀ i → (i∈ : i ∈ inputs tx) →
        index (outputRef i) < length (outputs (lookupTx l (outputRef i) (v₀ i i∈)))
    v₁ _ (here refl) = len<
    v₁ _ (there ())

    i′ = prevTx at j ←— i
    out = lookupOutput l prevTxRef prevTx♯∈ len<
    ptx = mkPendingTx l tx i′ (here refl) v₀ v₁

    ds  = toData s
    di  = toData i
    ds′ = toData s′

    ptxIn : PendingTxInput
    ptxIn = record { validatorHash = 𝕍
                   ; dataHash      = ds ♯ᵈ
                   ; redeemerHash  = di ♯ᵈ
                   ; value         = v }

    dataVal≡ : dataVal out ≡ ds
    dataVal≡ rewrite lookupPrevOutput≡ = refl

    value≡ : value out ≡ v
    value≡ rewrite lookupPrevOutput≡ = refl

    ptxIn≡ : mkPendingTxIn l i′ (v₀ i′ (here refl)) (v₁ i′ (here refl))
            ≡ ptxIn
    ptxIn≡ =
        -- rewrite dataVal≡ | value≡ = refl
        begin
        mkPendingTxIn l i′ (v₀ i′ (here refl)) (v₁ i′ (here refl))
        ≡⟨⟩
        record { validatorHash = 𝕍
                ; dataHash      = (dataVal out) ♯ᵈ
                ; redeemerHash  = di ♯ᵈ
                ; value         = value out
                }
        ≡⟨ cong (λ x → record { validatorHash = 𝕍
                            ; dataHash      = x ♯ᵈ
                            ; redeemerHash  = di ♯ᵈ
                            ; value         = value out
                            }) dataVal≡
                ⟩
        record { validatorHash = 𝕍
                ; dataHash      = ds ♯ᵈ
                ; redeemerHash  = di ♯ᵈ
                ; value         = value out
                }
        ≡⟨ cong (λ x → record { validatorHash = 𝕍
                            ; dataHash      = ds ♯ᵈ
                            ; redeemerHash  = di ♯ᵈ
                            ; value         = x
                            }) value≡
                ⟩
        record { validatorHash = 𝕍
                ; dataHash      = ds ♯ᵈ
                ; redeemerHash  = di ♯ᵈ
                ; value         = v
                }
        ≡⟨⟩
        ptxIn
        ∎

    ptxIn≡′ : mapWith∈ (inputs tx) (λ {i} i∈ → mkPendingTxIn l i (v₀ i i∈) (v₁ i i∈))
            ≡ [ ptxIn ]
    ptxIn≡′ rewrite ptxIn≡ = refl

    ptx≡ : ptx ≡ record { inputInfo     = [ ptxIn ]
                        ; thisInput     = ptxIn
                        ; outputInfo    = []
                        ; dataWitnesses = []
                        ; txHash        = tx ♯ₜₓ
                        ; fee           = $0
                        ; forge         = $0 }
    ptx≡ =
        -- rewrite ptxIn≡′ | ptxIn≡ = refl
      begin
        ptx
      ≡⟨⟩
        record { inputInfo      = mapWith∈ [ i′ ] (λ {i} i∈ → mkPendingTxIn l i (v₀ i i∈) (v₁ i i∈))
                ; thisInput     = mkPendingTxIn l i′ (v₀ i′ (here refl)) (v₁ i′ (here refl))
                ; outputInfo    = []
                ; dataWitnesses = []
                ; txHash        = tx ♯ₜₓ
                ; fee           = $0
                ; forge         = $0 }
      ≡⟨ cong (λ x → record { inputInfo     = x
                            ; thisInput     = mkPendingTxIn l i′ (v₀ i′ (here refl)) (v₁ i′ (here refl))
                            ; outputInfo    = []
                            ; dataWitnesses = []
                            ; txHash        = tx ♯ₜₓ
                            ; fee           = $0
                            ; forge         = $0 }) ptxIn≡′ ⟩
        record { inputInfo     = [ ptxIn ]
               ; thisInput     = mkPendingTxIn l i′ (v₀ i′ (here refl)) (v₁ i′ (here refl))
               ; outputInfo    = []
               ; dataWitnesses = []
               ; txHash        = tx ♯ₜₓ
               ; fee           = $0
               ; forge         = $0 }
      ≡⟨ cong (λ x → record { inputInfo     = [ ptxIn ]
                            ; thisInput     = x
                            ; outputInfo    = []
                            ; dataWitnesses = []
                            ; txHash        = tx ♯ₜₓ
                            ; fee           = $0
                            ; forge         = $0 }) ptxIn≡ ⟩
        record { inputInfo     = [ ptxIn ]
               ; thisInput     = ptxIn
               ; outputInfo    = []
               ; dataWitnesses = []
               ; txHash        = tx ♯ₜₓ
               ; fee           = $0
               ; forge         = $0 }
      ∎

    state′≡ : ⦇ step (pure sm) (fromData ds) (fromData di) ⦈ ≡ pure (pure s′)
    state′≡ rewrite from∘to s | from∘to i | step≡ = refl

    validate≡ : mkValidator sm ptx di ds ≡ true
    validate≡
      rewrite state′≡
            | final≡
            = refl

    v₃ :
      forge tx +ᶜ sumᶜ [ lookupValue l (prevTx at j ←— i) prevTx♯∈ len< ]
        ≡
      fee tx +ᶜ sumᶜ (map value [])
    v₃ rewrite lookupValue≡ | final≡ | val≡ tt = refl

    val :
      let
        i   = prevTx at j ←— i
        out = lookupOutput l prevTxRef prevTx♯∈ len<
        ptx = mkPendingTx l tx i (here refl) v₀ v₁
      in
       T (runValidation ptx i out)
    val rewrite lookupPrevOutput≡ | validate≡ = tt

    vtx : IsValidTx tx l
    validTxRefs         vtx = v₀
    validOutputIndices  vtx = v₁
    validOutputRefs     vtx = λ{ i (here refl) → prev∈utxo
                               ; _ (there ()) }
    preservesValues     vtx = v₃
    noDoubleSpending    vtx = [] ∷ []
    allInputsValidate   vtx = λ{ i (here refl) → val
                               ; _ (there ()) }
    validateValidHashes vtx = λ{ i (here refl) → addr≡′
                               ; _ (there ()) }

... | false | ≡[ final≡ ] = tx , vtx , here (refl , refl) , λ _ → here (from∘to s′)
  where
    𝕍  = (mkValidator sm) ♯

    -- Create a transaction input.
    _at_←—_ : Tx → ℕ → I → TxInput
    outputRef (t at i ←— _) = (t ♯ₜₓ) indexed-at i
    redeemer  (_ at _ ←— d) = toData d
    validator (_ at _ ←— _) = mkValidator sm

    -- Create a transaction output.
    _—→_at_ : S → Value → Address → TxOutput
    value   (_ —→ v at _) = v
    address (_ —→ _ at a) = a
    dataVal (d —→ _ at _) = toData d

    prevTxRef : TxOutputRef
    prevTxRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈prevTx)

    j = index prevTxRef

    prevOut : TxOutput
    prevOut = record {value = v; address = 𝕍; dataVal = toData s}

    tx : Tx
    inputs  tx = [ prevTx at j ←— i ]
    outputs tx = [ s′ —→ $ v at 𝕍 ]
    forge   tx = $0
    fee     tx = $0

    prevTx∈ : prevTx ∈ l
    prevTx∈ = tx♯∈⇒tx∈ prev∈utxo

    prevTx♯∈ : Any (λ tx → tx ♯ₜₓ ≡ prevTx ♯ₜₓ) l
    prevTx♯∈ = Any.map (cong _♯ₜₓ ∘ sym) prevTx∈

    prevTx′ = lookupTx l prevTxRef prevTx♯∈

    lookupPrevTx≡ : lookupTx l prevTxRef prevTx♯∈ ≡ prevTx
    lookupPrevTx≡
      rewrite find∘map {Q = λ tx → tx ♯ₜₓ ≡ prevTx ♯ₜₓ} prevTx∈ (cong _♯ₜₓ ∘ sym)
            | proj₁∘find prevTx∈
            = refl

    len<′ : index prevTxRef < length (outputs prevTx)
    len<′ = toℕ< (Any.index prevOut∈prevTx)

    len< : index prevTxRef < length (outputs prevTx′)
    len< rewrite lookupPrevTx≡ = len<′

    lookupPrevOutput≡ : lookupOutput l prevTxRef prevTx♯∈ len< ≡ prevOut
    lookupPrevOutput≡
      rewrite lookupPrevTx≡
            | ‼-fromℕ<∘toℕ< {xs = outputs prevTx} (Any.index prevOut∈prevTx)
            | ‼-index prevOut∈prevTx
            = refl

    lookupValue≡ : lookupValue l (prevTx at j ←— i) prevTx♯∈ len< ≡ v
    lookupValue≡ rewrite lookupPrevOutput≡ = refl

    addr≡′ : address (lookupOutput l prevTxRef prevTx♯∈ len<) ≡ 𝕍
    addr≡′ rewrite lookupPrevOutput≡ = refl

    v₀ :
      ∀ i → i ∈ inputs tx →
        Any (λ t → t ♯ₜₓ ≡ id (outputRef i)) l
    v₀ _ (here refl) = prevTx♯∈
    v₀ _ (there ())

    v₁ :
      ∀ i → (i∈ : i ∈ inputs tx) →
        index (outputRef i) < length (outputs (lookupTx l (outputRef i) (v₀ i i∈)))
    v₁ _ (here refl) = len<
    v₁ _ (there ())

    i′ = prevTx at j ←— i
    out = lookupOutput l prevTxRef prevTx♯∈ len<
    ptx = mkPendingTx l tx i′ (here refl) v₀ v₁

    ds  = toData s
    di  = toData i
    ds′ = toData s′

    ptxIn : PendingTxInput
    ptxIn = record { validatorHash = 𝕍
                    ; dataHash      = ds ♯ᵈ
                    ; redeemerHash  = di ♯ᵈ
                    ; value         = v }

    dataVal≡ : dataVal out ≡ ds
    dataVal≡ rewrite lookupPrevOutput≡ = refl

    value≡ : value out ≡ v
    value≡ rewrite lookupPrevOutput≡ = refl

    ptxIn≡ : mkPendingTxIn l i′ (v₀ i′ (here refl)) (v₁ i′ (here refl))
            ≡ ptxIn
    ptxIn≡ =
        -- rewrite dataVal≡ | value≡ = refl
      begin
        mkPendingTxIn l i′ (v₀ i′ (here refl)) (v₁ i′ (here refl))
      ≡⟨⟩
        record { validatorHash = 𝕍
                ; dataHash      = (dataVal out) ♯ᵈ
                ; redeemerHash  = di ♯ᵈ
                ; value         = value out
                }
      ≡⟨ cong (λ x → record { validatorHash = 𝕍
                            ; dataHash      = x ♯ᵈ
                            ; redeemerHash  = di ♯ᵈ
                            ; value         = value out
                            }) dataVal≡
                ⟩
        record { validatorHash = 𝕍
                ; dataHash      = ds ♯ᵈ
                ; redeemerHash  = di ♯ᵈ
                ; value         = value out
                }
      ≡⟨ cong (λ x → record { validatorHash = 𝕍
                            ; dataHash      = ds ♯ᵈ
                            ; redeemerHash  = di ♯ᵈ
                            ; value         = x
                            }) value≡
                ⟩
        record { validatorHash = 𝕍
                ; dataHash      = ds ♯ᵈ
                ; redeemerHash  = di ♯ᵈ
                ; value         = v
                }
      ≡⟨⟩
        ptxIn
        ∎

    ptxIn≡′ : mapWith∈ (inputs tx) (λ {i} i∈ → mkPendingTxIn l i (v₀ i i∈) (v₁ i i∈))
            ≡ [ ptxIn ]
    ptxIn≡′ rewrite ptxIn≡ = refl

    ptxOut : PendingTxOutput
    ptxOut = record {value = v; validatorHash = 𝕍; dataHash = ds′ ♯ᵈ}

    ptx≡ : ptx ≡ record { inputInfo     = [ ptxIn ]
                        ; thisInput     = ptxIn
                        ; outputInfo    = [ ptxOut ]
                        ; dataWitnesses = [ ds′ ♯ᵈ , ds′ ]
                        ; txHash        = tx ♯ₜₓ
                        ; fee           = $0
                        ; forge         = $0 }
    ptx≡ =
        -- rewrite ptxOut≡ | ptxIn≡′ | ptxIn≡ = refl
      begin
        ptx
      ≡⟨⟩
        record { inputInfo     = mapWith∈ [ i′ ] (λ {i} i∈ → mkPendingTxIn l i (v₀ i i∈) (v₁ i i∈))
                ; thisInput     = mkPendingTxIn l i′ (v₀ i′ (here refl)) (v₁ i′ (here refl))
                ; outputInfo    = [ ptxOut ]
                ; dataWitnesses = [ ds′ ♯ᵈ , ds′ ]
                ; txHash        = tx ♯ₜₓ
                ; fee           = $0
                ; forge         = $0 }
      ≡⟨ cong (λ x → record { inputInfo     = x
                            ; thisInput     = mkPendingTxIn l i′ (v₀ i′ (here refl)) (v₁ i′ (here refl))
                            ; outputInfo    = [ ptxOut ]
                            ; dataWitnesses = [ ds′ ♯ᵈ , ds′ ]
                            ; txHash        = tx ♯ₜₓ
                            ; fee           = $0
                            ; forge         = $0 }) ptxIn≡′ ⟩
        record { inputInfo     = [ ptxIn ]
                ; thisInput     = mkPendingTxIn l i′ (v₀ i′ (here refl)) (v₁ i′ (here refl))
                ; outputInfo    = [ ptxOut ]
                ; dataWitnesses = [ ds′ ♯ᵈ , ds′ ]
                ; txHash        = tx ♯ₜₓ
                ; fee           = $0
                ; forge         = $0 }
      ≡⟨ cong (λ x → record { inputInfo     = [ ptxIn ]
                            ; thisInput     = x
                            ; outputInfo    = [ ptxOut ]
                            ; dataWitnesses = [ ds′ ♯ᵈ , ds′ ]
                            ; txHash        = tx ♯ₜₓ
                            ; fee           = $0
                            ; forge         = $0 }) ptxIn≡ ⟩
        record { inputInfo     = [ ptxIn ]
                ; thisInput     = ptxIn
                ; outputInfo    = [ ptxOut ]
                ; dataWitnesses = [ ds′ ♯ᵈ , ds′ ]
                ; txHash        = tx ♯ₜₓ
                ; fee           = $0
                ; forge         = $0 }
      ∎

    state′≡ : ⦇ step (pure sm) (fromData ds) (fromData di) ⦈ ≡ pure (pure s′)
    state′≡ rewrite from∘to s | from∘to i | step≡ = refl

    outs≡ : getContinuingOutputs ptx ≡ [ ptxOut ]
    outs≡ rewrite ≟ℕ-refl {𝕍} = refl

    findData≡ : findData (PendingTxOutput.dataHash ptxOut) ptx ≡ pure ds′
    findData≡ rewrite ≟ℕ-refl {ds′ ♯ᵈ} = refl

    validate≡ : mkValidator sm ptx di ds ≡ true
    validate≡
      rewrite state′≡
            | outs≡
            | findData≡
            | ≟ᵈ-refl {ds′}
            | final≡
            = refl

    val :
      let
        i   = prevTx at j ←— i
        out = lookupOutput l prevTxRef prevTx♯∈ len<
        ptx = mkPendingTx l tx i (here refl) v₀ v₁
      in
       T (runValidation ptx i out)
    val rewrite lookupPrevOutput≡ | validate≡ = tt

    vtx : IsValidTx tx l
    validTxRefs         vtx = v₀
    validOutputIndices  vtx = v₁
    validOutputRefs     vtx = λ{ i (here refl) → prev∈utxo
                               ; _ (there ()) }
    preservesValues     vtx rewrite lookupValue≡ = refl
    noDoubleSpending    vtx = [] ∷ []
    allInputsValidate   vtx = λ{ i (here refl) → val
                               ; _ (there ()) }
    validateValidHashes vtx = λ{ i (here refl) → addr≡′
                               ; _ (there ()) }

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
  → (prevOut∈prevTx : record {value = v; address = (mkValidator sm) ♯; dataVal = toData s} ∈ outputs prevTx)

  → let prevTxRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈prevTx) in

    -- previous unspent output
    prevTxRef ∈ SETₒ.list (unspentOutputs l)

    ---------------------------------------------------------------------------------------

  → ∃[ tx ]
       ( -- (1) new transaction is valid
         IsValidTx tx l
         -- (2) it contains the source state in its inputs, using the state machine's validator
       × Any (λ i → (outputRef i ≡ prevTxRef) × ((validator i) ♯ ≡ (mkValidator sm) ♯)) (inputs tx)
         -- (3) it contains the target state in its outputs
       × Any ((_≡ pure s′) ∘ fromData ∘ dataVal) (outputs tx)
       )

liveness′ {S} {I} {sm} {s} {i} {s′} {l} {prevTx} {v} step≡ final≡ vl prevOut∈prevTx prev∈utxo
  = tx , vtx , here (refl , refl) , here (from∘to s′)
  where
    𝕍  = (mkValidator sm) ♯

    -- Create a transaction input.
    _at_←—_ : Tx → ℕ → I → TxInput
    outputRef (t at i ←— _) = (t ♯ₜₓ) indexed-at i
    redeemer  (_ at _ ←— d) = toData d
    validator (_ at _ ←— _) = mkValidator sm

    -- Create a transaction output.
    _—→_at_ : S → Value → Address → TxOutput
    value   (_ —→ v at _) = v
    address (_ —→ _ at a) = a
    dataVal (d —→ _ at _) = toData d

    prevTxRef : TxOutputRef
    prevTxRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈prevTx)

    j = index prevTxRef

    prevOut : TxOutput
    prevOut = record {value = v; address = 𝕍; dataVal = toData s}

    tx : Tx
    inputs  tx = [ prevTx at j ←— i ]
    outputs tx = [ s′ —→ $ v at 𝕍 ]
    forge   tx = $0
    fee     tx = $0

    prevTx∈ : prevTx ∈ l
    prevTx∈ = tx♯∈⇒tx∈ prev∈utxo

    prevTx♯∈ : Any (λ tx → tx ♯ₜₓ ≡ prevTx ♯ₜₓ) l
    prevTx♯∈ = Any.map (cong _♯ₜₓ ∘ sym) prevTx∈

    prevTx′ = lookupTx l prevTxRef prevTx♯∈

    lookupPrevTx≡ : lookupTx l prevTxRef prevTx♯∈ ≡ prevTx
    lookupPrevTx≡
      rewrite find∘map {Q = λ tx → tx ♯ₜₓ ≡ prevTx ♯ₜₓ} prevTx∈ (cong _♯ₜₓ ∘ sym)
            | proj₁∘find prevTx∈
            = refl

    len<′ : index prevTxRef < length (outputs prevTx)
    len<′ = toℕ< (Any.index prevOut∈prevTx)

    len< : index prevTxRef < length (outputs prevTx′)
    len< rewrite lookupPrevTx≡ = len<′

    lookupPrevOutput≡ : lookupOutput l prevTxRef prevTx♯∈ len< ≡ prevOut
    lookupPrevOutput≡
      rewrite lookupPrevTx≡
            | ‼-fromℕ<∘toℕ< {xs = outputs prevTx} (Any.index prevOut∈prevTx)
            | ‼-index prevOut∈prevTx
            = refl

    lookupValue≡ : lookupValue l (prevTx at j ←— i) prevTx♯∈ len< ≡ v
    lookupValue≡ rewrite lookupPrevOutput≡ = refl

    addr≡′ : address (lookupOutput l prevTxRef prevTx♯∈ len<) ≡ 𝕍
    addr≡′ rewrite lookupPrevOutput≡ = refl

    v₀ :
      ∀ i → i ∈ inputs tx →
        Any (λ t → t ♯ₜₓ ≡ id (outputRef i)) l
    v₀ _ (here refl) = prevTx♯∈
    v₀ _ (there ())

    v₁ :
      ∀ i → (i∈ : i ∈ inputs tx) →
        index (outputRef i) < length (outputs (lookupTx l (outputRef i) (v₀ i i∈)))
    v₁ _ (here refl) = len<
    v₁ _ (there ())

    i′  = prevTx at j ←— i
    out = lookupOutput l prevTxRef prevTx♯∈ len<
    ptx = mkPendingTx l tx i′ (here refl) v₀ v₁

    ds  = toData s
    di  = toData i
    ds′ = toData s′

    ptxIn : PendingTxInput
    ptxIn = record { validatorHash = 𝕍
                   ; dataHash      = ds ♯ᵈ
                   ; redeemerHash  = di ♯ᵈ
                   ; value         = v }

    dataVal≡ : dataVal out ≡ ds
    dataVal≡ rewrite lookupPrevOutput≡ = refl

    value≡ : value out ≡ v
    value≡ rewrite lookupPrevOutput≡ = refl

    ptxIn≡ : mkPendingTxIn l i′ (v₀ i′ (here refl)) (v₁ i′ (here refl))
            ≡ ptxIn
    ptxIn≡ =
        -- rewrite dataVal≡ | value≡ = refl
      begin
        mkPendingTxIn l i′ (v₀ i′ (here refl)) (v₁ i′ (here refl))
      ≡⟨⟩
        record { validatorHash = 𝕍
                ; dataHash      = (dataVal out) ♯ᵈ
                ; redeemerHash  = di ♯ᵈ
                ; value         = value out
                }
      ≡⟨ cong (λ x → record { validatorHash = 𝕍
                            ; dataHash      = x ♯ᵈ
                            ; redeemerHash  = di ♯ᵈ
                            ; value         = value out
                            }) dataVal≡
                ⟩
        record { validatorHash = 𝕍
                ; dataHash      = ds ♯ᵈ
                ; redeemerHash  = di ♯ᵈ
                ; value         = value out
                }
      ≡⟨ cong (λ x → record { validatorHash = 𝕍
                            ; dataHash      = ds ♯ᵈ
                            ; redeemerHash  = di ♯ᵈ
                            ; value         = x
                            }) value≡
                ⟩
        record { validatorHash = 𝕍
                ; dataHash      = ds ♯ᵈ
                ; redeemerHash  = di ♯ᵈ
                ; value         = v
                }
      ≡⟨⟩
        ptxIn
        ∎

    ptxIn≡′ : mapWith∈ (inputs tx) (λ {i} i∈ → mkPendingTxIn l i (v₀ i i∈) (v₁ i i∈))
            ≡ [ ptxIn ]
    ptxIn≡′ rewrite ptxIn≡ = refl

    ptxOut : PendingTxOutput
    ptxOut = record {value = v; validatorHash = 𝕍; dataHash = ds′ ♯ᵈ}

    ptx≡ : ptx ≡ record { inputInfo     = [ ptxIn ]
                        ; thisInput     = ptxIn
                        ; outputInfo    = [ ptxOut ]
                        ; dataWitnesses = [ ds′ ♯ᵈ , ds′ ]
                        ; txHash        = tx ♯ₜₓ
                        ; fee           = $0
                        ; forge         = $0 }
    ptx≡ =
        -- rewrite ptxOut≡ | ptxIn≡′ | ptxIn≡ = refl
      begin
        ptx
      ≡⟨⟩
        record { inputInfo     = mapWith∈ [ i′ ] (λ {i} i∈ → mkPendingTxIn l i (v₀ i i∈) (v₁ i i∈))
                ; thisInput     = mkPendingTxIn l i′ (v₀ i′ (here refl)) (v₁ i′ (here refl))
                ; outputInfo    = [ ptxOut ]
                ; dataWitnesses = [ ds′ ♯ᵈ , ds′ ]
                ; txHash        = tx ♯ₜₓ
                ; fee           = $0
                ; forge         = $0 }
      ≡⟨ cong (λ x → record { inputInfo     = x
                            ; thisInput     = mkPendingTxIn l i′ (v₀ i′ (here refl)) (v₁ i′ (here refl))
                            ; outputInfo    = [ ptxOut ]
                            ; dataWitnesses = [ ds′ ♯ᵈ , ds′ ]
                            ; txHash        = tx ♯ₜₓ
                            ; fee           = $0
                            ; forge         = $0 }) ptxIn≡′ ⟩
        record { inputInfo     = [ ptxIn ]
                ; thisInput     = mkPendingTxIn l i′ (v₀ i′ (here refl)) (v₁ i′ (here refl))
                ; outputInfo    = [ ptxOut ]
                ; dataWitnesses = [ ds′ ♯ᵈ , ds′ ]
                ; txHash        = tx ♯ₜₓ
                ; fee           = $0
                ; forge         = $0 }
      ≡⟨ cong (λ x → record { inputInfo     = [ ptxIn ]
                            ; thisInput     = x
                            ; outputInfo    = [ ptxOut ]
                            ; dataWitnesses = [ ds′ ♯ᵈ , ds′ ]
                            ; txHash        = tx ♯ₜₓ
                            ; fee           = $0
                            ; forge         = $0 }) ptxIn≡ ⟩
        record { inputInfo     = [ ptxIn ]
                ; thisInput     = ptxIn
                ; outputInfo    = [ ptxOut ]
                ; dataWitnesses = [ ds′ ♯ᵈ , ds′ ]
                ; txHash        = tx ♯ₜₓ
                ; fee           = $0
                ; forge         = $0 }
      ∎

    state′≡ : ⦇ step (pure sm) (fromData ds) (fromData di) ⦈ ≡ pure (pure s′)
    state′≡ rewrite from∘to s | from∘to i | step≡ = refl

    outs≡ : getContinuingOutputs ptx ≡ [ ptxOut ]
    outs≡ rewrite ≟ℕ-refl {𝕍} = refl

    findData≡ : findData (PendingTxOutput.dataHash ptxOut) ptx ≡ pure ds′
    findData≡ rewrite ≟ℕ-refl {ds′ ♯ᵈ} = refl

    validate≡ : mkValidator sm ptx di ds ≡ true
    validate≡
      rewrite state′≡
            | outs≡
            | findData≡
            | ≟ᵈ-refl {ds′}
            | final≡
            = refl

    val :
      let
        i   = prevTx at j ←— i
        out = lookupOutput l prevTxRef prevTx♯∈ len<
        ptx = mkPendingTx l tx i (here refl) v₀ v₁
      in
       T (runValidation ptx i out)
    val rewrite lookupPrevOutput≡ | validate≡ = tt

    vtx : IsValidTx tx l
    validTxRefs         vtx = v₀
    validOutputIndices  vtx = v₁
    validOutputRefs     vtx = λ{ i (here refl) → prev∈utxo
                               ; _ (there ()) }
    preservesValues     vtx rewrite lookupValue≡ = refl
    noDoubleSpending    vtx = [] ∷ []
    allInputsValidate   vtx = λ{ i (here refl) → val
                               ; _ (there ()) }
    validateValidHashes vtx = λ{ i (here refl) → addr≡′
                               ; _ (there ()) }
