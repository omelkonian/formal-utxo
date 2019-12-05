module StateMachine.Properties.Safety where

open import Data.Unit    using (tt)
open import Data.Bool    using (Bool; T; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Maybe   using (Maybe; nothing; Is-just; _>>=_; fromMaybe)
  renaming (just to pure; ap to _<*>_)
open import Data.Nat     using (ℕ; _<_; zero; suc; ≤-pred)
  renaming (_≟_ to _≟ℕ_)
open import Data.Fin     using (toℕ; fromℕ<)
open import Data.List    using (List; []; _∷_; [_]; map; length)

open import Data.Maybe.Properties using (just-injective)

open import Data.List.Membership.Propositional  using (_∈_; mapWith∈; find)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)

open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; sym; trans; inspect)
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

safety : ∀ {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
           {s : S} {i : I} {s′ : S} {l : Ledger}
           {prevTx : Tx} {v : Value}

  → ValidLedger l

  → (prevTxRef∈ : record { address = (mkValidator sm) ♯
                         ; value   = v
                         ; dataVal = toData s
                         } ∈ outputs prevTx)

  → record { inputs  = [ record { outputRef = (prevTx ♯ₜₓ) indexed-at (toℕ (Any.index prevTxRef∈))
                                ; validator = mkValidator sm
                                ; redeemer  = toData i } ]
           ; outputs = [ record { address = (mkValidator sm) ♯
                                ; value = v
                                ; dataVal = toData s′ } ]
           ; fee     = $ 0
           ; forge   = $ 0
           ; range   = -∞ ⋯ +∞
           } ∈ l

    ---------------------------------------------------------------------------------------

  → step sm s i ≡ pure s′

safety {S = S} {sm = sm@(SM[ _ , final , step′ ])} {s} {i} {s′} {l} {prevTx} {v} vl prevTxRef∈ tx∈l = fin
  where
    ds  = toData s
    di  = toData i
    ds′ = toData s′
    𝕍 = (mkValidator sm) ♯

    prevOut : TxOutput
    address prevOut = 𝕍
    value   prevOut = v
    dataVal prevOut = ds

    prevTxRef : TxOutputRef
    prevTxRef = (prevTx ♯ₜₓ) indexed-at (toℕ (Any.index prevTxRef∈))

    txIn : TxInput
    outputRef txIn = prevTxRef
    validator txIn = mkValidator sm
    redeemer  txIn = di

    txOut : TxOutput
    address txOut = 𝕍
    value   txOut = v
    dataVal txOut = ds′

    tx : Tx
    inputs tx  = [ txIn ]
    outputs tx = [ txOut ]
    fee     tx = $ 0
    forge   tx = $ 0
    range   tx = -∞ ⋯ +∞

    ∈⇒valid : ∀ {tx l}
      → tx ∈ l
      → ValidLedger l
      → ∃[ l′ ] IsValidTx tx l′
    ∈⇒valid (here refl) (vl ⊕ t ∶- vtx) = _ , vtx
    ∈⇒valid (there tx∈) (vl ⊕ t ∶- vtx) = ∈⇒valid tx∈ vl

    ∃l′ : ∃[ l′ ] IsValidTx tx l′
    ∃l′ = ∈⇒valid tx∈l vl

    l′ : Ledger
    l′ = proj₁ ∃l′

    vtx : IsValidTx tx l′
    vtx = proj₂ ∃l′

    i∈ : txIn ∈ inputs tx
    i∈ = here refl

    v₁ = validTxRefs vtx
    v₂ = validOutputIndices vtx

    ∃tx≡id : Any (λ tx′ → tx′ ♯ₜₓ ≡ id prevTxRef) l′
    ∃tx≡id = v₁ txIn i∈

    proj₁∘find∘♯ : ∀ {l : Ledger} {tx₂ : Tx}
      → (any≡ : Any (λ tx₁ → tx₁ ♯ₜₓ ≡ tx₂ ♯ₜₓ) l)
      → proj₁ (find any≡)
      ≡ tx₂
    proj₁∘find∘♯ (here px)  = injective♯ₜₓ px
    proj₁∘find∘♯ (there x∈) = proj₁∘find∘♯ x∈

    lookupPrevTx≡ : lookupTx l′ prevTxRef ∃tx≡id
                  ≡ prevTx
    lookupPrevTx≡ = proj₁∘find∘♯ ∃tx≡id

    len<′ : index prevTxRef < length (outputs (lookupTx l′ prevTxRef ∃tx≡id))
    len<′ = v₂ txIn i∈

    len< : index prevTxRef < length (outputs prevTx)
    len< = toℕ< (Any.index prevTxRef∈)

    lookupOutput≡ : lookupOutput l′ (outputRef txIn) ∃tx≡id len<′
                  ≡ prevOut
    lookupOutput≡ = trans h₁ h₂
      where
        h₁ : (outputs (lookupTx l′ prevTxRef ∃tx≡id) ‼ (fromℕ< len<′))
           ≡ (outputs prevTx ‼ (fromℕ< len<))
        h₁ = ‼-fromℕ<-≡ len<′ len< (cong outputs lookupPrevTx≡)

        h₂ : (outputs prevTx ‼ (fromℕ< len<))
           ≡ prevOut
        h₂ rewrite ‼-fromℕ<∘toℕ< {xs = outputs prevTx} (Any.index prevTxRef∈)
                 | ‼-index prevTxRef∈
                 = refl

    ptxIn : PendingTxInput
    validatorHash ptxIn = 𝕍
    dataHash      ptxIn = ds ♯ᵈ
    redeemerHash  ptxIn = di ♯ᵈ
    value         ptxIn = v

    ptxIn≡ : mkPendingTxIn l′ txIn ∃tx≡id len<′
           ≡ ptxIn
    ptxIn≡ = h
      where
        h : record { validatorHash = 𝕍
                   ; dataHash      = (dataVal (lookupOutput l′ prevTxRef ∃tx≡id len<′)) ♯ᵈ
                   ; redeemerHash  = di ♯ᵈ
                   ; value         = value (lookupOutput l′ prevTxRef ∃tx≡id len<′) }
          ≡ ptxIn
        h rewrite lookupOutput≡ = refl

    ptxOut : PendingTxOutput
    value         ptxOut = v
    validatorHash ptxOut = 𝕍
    dataHash      ptxOut = ds′ ♯ᵈ

    ptx : PendingTx
    inputInfo     ptx = [ ptxIn ]
    thisInput     ptx = ptxIn
    outputInfo    ptx = [ ptxOut ]
    dataWitnesses ptx = [ ds′ ♯ᵈ , ds′ ]
    txHash        ptx = tx ♯ₜₓ
    fee           ptx = $ 0
    forge         ptx = $ 0
    range         ptx = -∞ ⋯ +∞

    ptx≡ : mkPendingTx l′ tx txIn i∈ v₁ v₂
         ≡ ptx
    ptx≡ = h
      where
        h : record { inputInfo     = [ mkPendingTxIn l′ txIn ∃tx≡id len<′ ]
                   ; thisInput     = mkPendingTxIn l′ txIn ∃tx≡id len<′
                   ; outputInfo    = [ ptxOut ]
                   ; dataWitnesses = [ ds′ ♯ᵈ , ds′ ]
                   ; txHash        = tx ♯ₜₓ
                   ; fee           = $ 0
                   ; forge         = $ 0
                   ; range         = -∞ ⋯ +∞ }
          ≡ ptx
        h rewrite ptxIn≡ = refl

    validate≡ :
         T (runValidation (mkPendingTx l′ tx txIn i∈ v₁ v₂) txIn (lookupOutput l′ (outputRef txIn) ∃tx≡id len<′))
       → T (mkValidator sm ptx di ds)
    validate≡ p rewrite ptx≡ | lookupOutput≡ = p

    fromMaybe≡true : ∀ {S : Set} {mx : Maybe S} {k : S → Maybe Bool}
      → T (fromMaybe false (mx >>= k))
      → ∃[ x ] ( (mx  ≡ pure x)
               × (k x ≡ pure true) )
    fromMaybe≡true {mx = mx} {k = k} p
      with mx | p
    ... | nothing | ()
    ... | pure x  | p′
      with k x | inspect k x | p′
    ... | nothing    | _       | ()
    ... | pure false | _       | ()
    ... | pure true  | ≡[ k≡ ] | _  = x , refl , k≡

    k′ : S → Maybe Bool
    k′ x =
      if final x then
        pure false
      else
        pure (toData s′ == toData x)

    mx′ : Maybe S
    mx′ with ⦇ step′ (fromData ds) (fromData di) ⦈
    ... | pure r = r
    ... | _      = nothing

    mx≡′ : ∀ {s″ : S}
      → mx′ ≡ pure s″
      → step′ s i ≡ pure s″
    mx≡′ {s″} mx≡
      rewrite from∘to s | from∘to i
      with step′ s i | mx≡
    ... | nothing  | ()
    ... | pure .s″ | refl = refl

    hh : T (mkValidator sm ptx di ds)
       → T (fromMaybe false (mx′ >>= k′))
    hh p rewrite from∘to s | from∘to i | ≟ℕ-refl {𝕍} | ≟ℕ-refl {ds′ ♯ᵈ} = p

    step≡ : T (mkValidator sm ptx di ds)
          → step′ s i ≡ pure s′
    step≡ p
      with fromMaybe≡true {mx = mx′} {k = k′} (hh p)
    ... | s″ , mx≡ , k≡
      with final s″ | k≡
    ... | true  | ()
    ... | false | k≡′
      with toData s′ ≟ᵈ toData s″ | k≡′
    ... | no _   | ()
    ... | yes eq | _
      with cong (fromData {A = S}) eq
    ... | eq′
      rewrite from∘to s″ | from∘to s′ =
        begin
          step′ s i
        ≡⟨ mx≡′ mx≡ ⟩
           pure s″
        ≡⟨ sym eq′ ⟩
           pure s′
        ∎

    fin : step sm s i ≡ pure s′
    fin = step≡ (validate≡ (allInputsValidate vtx txIn i∈))
