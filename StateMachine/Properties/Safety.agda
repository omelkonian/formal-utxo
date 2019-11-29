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

Address = HashId

open import UTxO.Ledger      Address (λ x → x) _≟ℕ_
open import UTxO.TxUtilities Address (λ x → x) _≟ℕ_
open import UTxO.Hashing.Tx  Address (λ x → x) _≟ℕ_
open import UTxO.Validity    Address (λ x → x) _≟ℕ_

module _ {S : Set} {{_ : IsData S}} {x′ : S} where

    T (fromMaybe false (mx >>= k))
  → ∃[ x ] (mx ≡ pure x)
           ×

  k : (S → Bool) → S → Maybe Bool
  k b x =
    if b x then
      pure false
    else
      pure (toData x′ == toData x)

  h : ∀ {mx : Maybe S} {b : S → Bool}
    → T (fromMaybe false (mx >>= k b))
    → ∃[ x ] ( (mx ≡ pure x)
             × (x′ ≡ x) )
  h {mx = mx} {b = b} p
    with mx | p
  ... | nothing | ()
  ... | pure x  | p′
    with k b x | inspect (k b) x | p′
  ... | nothing    | _       | ()
  ... | pure false | _       | ()
  ... | pure true  | ≡[ k≡ ] | p″
    with b x | k≡
  ... | true  | ()
  ... | false | k≡′
    with toData x′ ≟ᵈ toData x | k≡′
  ... | no _   | ()
  ... | yes eq | _
    with cong (fromData {A = S}) eq
  ... | eq′
    rewrite from∘to x | from∘to x′
      = x , refl , just-injective eq′


∈⇒valid : ∀ {tx l}
  → tx ∈ l
  → ValidLedger l
  → ∃[ l′ ] IsValidTx tx l′
∈⇒valid (here refl) (vl ⊕ t ∶- vtx) = _ , vtx
∈⇒valid (there tx∈) (vl ⊕ t ∶- vtx) = ∈⇒valid tx∈ vl

fromℕ<-≡ : ∀ {A : Set} {xs : List A} {m : ℕ}
  → (p₁ : m < length xs)
  → (p₂ : m < length xs)
  → fromℕ< p₁ ≡ fromℕ< p₂
fromℕ<-≡ {xs = x ∷ xs} {zero}  p₁ p₂ = refl
fromℕ<-≡ {xs = x ∷ xs} {suc m} p₁ p₂ rewrite fromℕ<-≡ {xs = xs} {m = m} (≤-pred p₁) (≤-pred p₂) = refl

‼-fromℕ<-≡ : ∀ {A : Set} {xs ys : List A} {m : ℕ}
  → (p₁ : m < length xs)
  → (p₂ : m < length ys)
  → xs ≡ ys
  → (xs ‼ fromℕ< p₁)
  ≡ (ys ‼ fromℕ< p₂)
‼-fromℕ<-≡ {xs = xs} {m = m} p₁ p₂ refl rewrite fromℕ<-≡ {xs = xs} {m = m} p₁ p₂ = refl

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
    lookupPrevTx≡ = {!!}
      {-
      -- rewrite proj₁∘find ? = refl
      begin
        lookupTx l′ prevTxRef ∃tx≡id
      ≡⟨⟩
        proj₁ (find ∃tx≡id)
      ≡⟨ proj₁∘find∘♯ ∃tx≡id ⟩
        prevTx
      ∎
      -}

    len<′ : index prevTxRef < length (outputs (lookupTx l′ prevTxRef ∃tx≡id))
    len<′ = v₂ txIn i∈

    -- h : fromℕ< len<′ ≡ Any.index prevTxRef∈
    -- h = ?

    len< : index prevTxRef < length (outputs prevTx)
    len< = toℕ< (Any.index prevTxRef∈)

    lookupOutput≡ : lookupOutput l′ (outputRef txIn) ∃tx≡id len<′
                  ≡ prevOut
    lookupOutput≡ = {!!}
      {-
      -- rewrite lookupPrevTx≡
      --       | ‼-fromℕ<∘toℕ< {xs = outputs prevTx} (Any.index prevTxRef∈)
      --       | ‼-index prevTxRef∈
      --       = refl
      begin
        lookupOutput l′ (outputRef txIn) ∃tx≡id len<′
      ≡⟨⟩
        lookupOutput l′ prevTxRef ∃tx≡id len<′
      ≡⟨⟩
        outputs (lookupTx l′ prevTxRef ∃tx≡id) ‼ (fromℕ< len<′)
      ≡⟨ h₁ ⟩
        outputs prevTx ‼ (fromℕ< len<)
      ≡⟨ h₂ ⟩
        prevOut
      ∎
      where
        h₁ : (outputs (lookupTx l′ prevTxRef ∃tx≡id) ‼ (fromℕ< len<′))
           ≡ (outputs prevTx ‼ (fromℕ< len<))
        h₁ = ‼-fromℕ<-≡ len<′ len< (cong outputs lookupPrevTx≡)

        h₂ : (outputs prevTx ‼ (fromℕ< len<))
           ≡ prevOut
        h₂ rewrite ‼-fromℕ<∘toℕ< {xs = outputs prevTx} (Any.index prevTxRef∈)
                 | ‼-index prevTxRef∈
                 = refl
      -}
    open PendingTxInput
    open PendingTxOutput
    open PendingTx

    ptxIn : PendingTxInput
    validatorHash ptxIn = 𝕍
    dataHash      ptxIn = ds ♯ᵈ
    redeemerHash  ptxIn = di ♯ᵈ
    value         ptxIn = v

    ptxIn≡ : mkPendingTxIn l′ txIn ∃tx≡id len<′
           ≡ ptxIn
    ptxIn≡ = {!!}
      {-
      -- rewrite lookupOutput≡ = refl
      begin
        mkPendingTxIn l′ txIn ∃tx≡id len<′
      ≡⟨⟩
        record { validatorHash = 𝕍
               ; dataHash      = (dataVal (lookupOutput l′ prevTxRef ∃tx≡id len<′)) ♯ᵈ
               ; redeemerHash  = di ♯ᵈ
               ; value         = value (lookupOutput l′ prevTxRef ∃tx≡id len<′) }

      ≡⟨ h ⟩
        ptxIn
      ∎
      where
        h : record { validatorHash = 𝕍
                   ; dataHash      = (dataVal (lookupOutput l′ prevTxRef ∃tx≡id len<′)) ♯ᵈ
                   ; redeemerHash  = di ♯ᵈ
                   ; value         = value (lookupOutput l′ prevTxRef ∃tx≡id len<′) }
          ≡ ptxIn
        h rewrite lookupOutput≡ = refl
      -}

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

    ptx≡ : mkPendingTx l′ tx txIn i∈ v₁ v₂
         ≡ ptx
    ptx≡ = {!!}
    {-
      -- rewrite ptxIn≡ = refl
      begin
        mkPendingTx l′ tx txIn i∈ v₁ v₂
      ≡⟨ h ⟩
        ptx
      ∎
      where
        h : record { inputInfo     = [ mkPendingTxIn l′ txIn ∃tx≡id len<′ ]
                   ; thisInput     = mkPendingTxIn l′ txIn ∃tx≡id len<′
                   ; outputInfo    = [ ptxOut ]
                   ; dataWitnesses = [ ds′ ♯ᵈ , ds′ ]
                   ; txHash        = tx ♯ₜₓ
                   ; fee           = $ 0
                   ; forge         = $ 0 }
          ≡ ptx
        h rewrite ptxIn≡ = refl
    -}

    validate≡ :
         T (runValidation (mkPendingTx l′ tx txIn i∈ v₁ v₂) txIn (lookupOutput l′ (outputRef txIn) ∃tx≡id len<′))
       → T (mkValidator sm ptx (toData i) (toData s))
    validate≡ = {!!} -- p rewrite ptx≡ | lookupOutput≡ = p

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

    step≡ : T (mkValidator sm ptx (toData i) (toData s))
          → step′ s i ≡ pure s′
    step≡ p
      with h {x′ = s′} {mx = mx′} {b = final} p
    ... | .s′ , p′ , refl  = {!!}
    --   with mx | p
    -- ... | nothing | ()
    -- ... | pure x  | p′
    --   with k x | inspect k x | p′
    -- ... | nothing    | _       | ()
    -- ... | pure false | _       | ()
    -- ... | pure true  | ≡[ k≡ ] | p″
    --   with final x | k≡
    -- ... | true  | ()
    -- ... | false | k≡′
    --   with toData s′ ≟ᵈ toData x | k≡′
    -- ... | no _   | ()
    -- ... | yes eq | _
    --   with cong (fromData {A = S}) eq
    -- ... | eq′
    --   rewrite from∘to x | from∘to s′
    --     = x , refl , just-injective eq′

    fin : step sm s i ≡ pure s′
    fin = {!!} -- step≡ (validate≡ (allInputsValidate vtx txIn i∈))
