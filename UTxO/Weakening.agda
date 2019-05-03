------------------------------------------------------------------------
-- Weakening.
------------------------------------------------------------------------

open import Function using (_∘_)
open import Function.Injection using (module Injection; _↣_)

open import Data.Unit    using (tt)
open import Data.Bool    using (T)
open import Data.Nat     using (_<_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)

open import Data.Fin using (Fin; toℕ; fromℕ≤; inject≤)
open import Data.Fin.Properties using (toℕ-injective; toℕ-fromℕ≤; toℕ-inject≤)

open import Data.List.Properties using (length-map; map-compose; map-id₂)
open import Data.List.Membership.Propositional using (_∈_; mapWith∈)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Pointwise using (Pointwise; Pointwise-≡⇒≡)

open import Relation.Binary using (Decidable)
open import Relation.Nullary.Decidable using (toWitness)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import UTxO.Types
open import Hashing.Base
open import Hashing.Types
open import Hashing.MetaHash

module UTxO.Weakening
  (𝔸 : Set) (_♯ᵃ : Hash 𝔸) (_≟ᵃ_ : Decidable {A = 𝔸} _≡_) -- smaller address space
  (𝔹 : Set) (_♯ᵇ : Hash 𝔹) (_≟ᵇ_ : Decidable {A = 𝔹} _≡_) -- larger address space
  (A↪B : 𝔸 , _♯ᵃ ↪ 𝔹 , _♯ᵇ)
  where

import UTxO.Validity      𝔸 _♯ᵃ _≟ᵃ_ as A
open import UTxO.Validity 𝔹 _♯ᵇ _≟ᵇ_ as B

-- Weakening operations.
weakenTxOutput : A.TxOutput → B.TxOutput
weakenTxOutput record { value = v ; dataScript = ds ; address = addr }
             = record { value = v ; dataScript = ds ; address = A↪B ⟨$⟩ addr}

weakenTx : A.Tx → B.Tx
weakenTx record { inputs  = inputs
                ; outputs = outputs
                ; forge   = forge
                ; fee     = fee }
       = record { inputs  = inputs
                ; outputs = map weakenTxOutput outputs
                ; forge   = forge
                ; fee     = fee }

weakenLedger : A.Ledger → B.Ledger
weakenLedger = map weakenTx

-- Hashes should be preserved.
weakenTxOutput-preserves♯ : ∀ (o : A.TxOutput) → (address (weakenTxOutput o)) ♯ᵇ ≡ (A.address o) ♯ᵃ
weakenTxOutput-preserves♯ o rewrite (preserves♯ A↪B (A.address o)) = refl

mapWeakenTxOutput-preserves♯ : ∀ (os : List A.TxOutput) → map _♯ₒ (map weakenTxOutput os) ≡ map A._♯ₒ os
mapWeakenTxOutput-preserves♯ [] = refl
mapWeakenTxOutput-preserves♯ (o ∷ os)
  rewrite mapWeakenTxOutput-preserves♯ os | weakenTxOutput-preserves♯ o = refl

weakenTx-preserves♯ : ∀ (tx : A.Tx) → (weakenTx tx) ♯ₜₓ ≡ tx A.♯ₜₓ
weakenTx-preserves♯ tx rewrite mapWeakenTxOutput-preserves♯ (A.outputs tx) = refl

weakening : ∀ {tx : A.Tx} {l : A.Ledger}

          → A.IsValidTx tx l
            ------------------------------------------------
          → B.IsValidTx (weakenTx tx) (weakenLedger l)

weakening {tx} {l}
    record
      { validTxRefs          = vtx
      ; validOutputIndices   = voi
      ; validOutputRefs      = vor
      ; validDataScriptTypes = vds
      ; preservesValues      = pv
      ; noDoubleSpending     = nds
      ; allInputsValidate    = aiv
      ; validateValidHashes  = vvh
      ; forging              = frg
      }
  = record
      { validTxRefs          = vtx′
      ; validOutputIndices   = voi′
      ; validOutputRefs      = vor′
      ; validDataScriptTypes = vds′
      ; preservesValues      = pv′
      ; noDoubleSpending     = nds
      ; allInputsValidate    = aiv′
      ; validateValidHashes  = vvh′
      ; forging              = frg′
      }
  where
    tx′ = weakenTx tx
    l′  = weakenLedger l

    ----------------------------------------------------------

    weaken₀ : ∀ {xs i}
      → Any (λ t → t A.♯ₜₓ ≡ id (outputRef i)) xs
      → Any (λ t → t ♯ₜₓ   ≡ id (outputRef i)) (weakenLedger xs)
    weaken₀ {x ∷ xs} {i} (here px) = here (trans (weakenTx-preserves♯ x) px)
    weaken₀ {x ∷ xs} {i} (there p) = there (weaken₀ {xs} {i} p)

    vtx′ : ∀ i → i ∈ inputs tx′ → Any (λ tx → tx ♯ₜₓ ≡ id (outputRef i)) l′
    vtx′ i i∈ = weaken₀ {l} {i} (vtx i i∈)

    ----------------------------------------------------------------------------------------

    outputs≡ : ∀ {t} → length (outputs (weakenTx t))
                     ≡ length (A.outputs t)
    outputs≡ {t} = length-map weakenTxOutput (A.outputs t)

    lookupTxWeakens : ∀ {xs i v₀}
      → lookupTx (weakenLedger xs) (outputRef i) (weaken₀ {xs} {i} v₀)
      ≡ weakenTx (A.lookupTx xs (outputRef i) v₀)
    lookupTxWeakens {v₀ = (here px)}  = refl
    lookupTxWeakens {v₀ = (there v₀)} = lookupTxWeakens {v₀ = v₀}

    weaken₁ : ∀ {xs i v₀}
      → index (outputRef i) < length (A.outputs (A.lookupTx xs (outputRef i) v₀))
      → index (outputRef i) < length (outputs (lookupTx (weakenLedger xs) (outputRef i) (weaken₀ {xs} {i} v₀)))
    weaken₁ {xs} {i} {v₀} p
      rewrite lookupTxWeakens {xs} {i} {v₀}
            | outputs≡ {A.lookupTx xs (outputRef i) v₀}
            = p

    voi′ : ∀ i → (i∈ : i ∈ inputs tx′) →
      index (outputRef i) < length (outputs (lookupTx l′ (outputRef i) (vtx′ i i∈)))
    voi′ i i∈ = weaken₁ {l} {i} {vtx i i∈} (voi i i∈)

    ------------------------------------------------------------------------------------

    weakenIndices : ∀ {x}
      → indices (outputs (weakenTx x))
      ≡ indices (A.outputs x)
    weakenIndices {x} rewrite length-map weakenTxOutput (A.outputs x) = refl

    weakenUnspentOutputsTx : ∀ {x}
      → unspentOutputsTx (weakenTx x)
      ≡ A.unspentOutputsTx x
    weakenUnspentOutputsTx {x} rewrite weakenIndices {x} | weakenTx-preserves♯ x = refl

    weakenUnspentOutputs : ∀ {xs}
      → unspentOutputs (weakenLedger xs)
      ≡ A.unspentOutputs xs
    weakenUnspentOutputs {[]}     = refl
    weakenUnspentOutputs {x ∷ xs} rewrite weakenUnspentOutputs {xs}
                                        | weakenUnspentOutputsTx {x}
                                        = refl

    vor′ : ∀ i → i ∈ inputs tx′ → outputRef i SETₒ.∈′ unspentOutputs l′
    vor′ i i∈ rewrite weakenUnspentOutputs {l} = vor i i∈

    ------------------------------------------------------------------------------------

    mapValue≡ : (map value ∘ map weakenTxOutput) (A.outputs tx)
              ≡ map A.value (A.outputs tx)
    mapValue≡
      rewrite sym (map-compose {g = value} {f = weakenTxOutput} (A.outputs tx))
            = refl

    Σvalue≡ : sumᶜ (map A.value (A.outputs tx)) ≡ sumᶜ (map value (outputs tx′))
    Σvalue≡ rewrite mapValue≡ = refl

    lookupOutputWeakens : ∀ {xs i}
      → (v₀ : Any (λ tx → tx A.♯ₜₓ ≡ id (outputRef i)) xs)
      → (v₁ : index (outputRef i) < length (A.outputs (A.lookupTx xs (outputRef i) v₀)))
      → lookupOutput (weakenLedger xs) (outputRef i) (weaken₀ {xs} {i} v₀) (weaken₁ {xs} {i} {v₀} v₁)
      ≡ weakenTxOutput (A.lookupOutput xs (outputRef i) v₀ v₁)
    lookupOutputWeakens {xs} {i} v₀ v₁ =
      begin
        lookupOutput xs′ refi v₀′ v₁′
      ≡⟨⟩
        outputs (lookupTx xs′ refi v₀′)
          ‼
        index₁
      ≡⟨ h₁ ⟩
        outputs (weakenTx (A.lookupTx xs refi v₀))
          ‼
        index₂
      ≡⟨⟩
        map weakenTxOutput (A.outputs (A.lookupTx xs refi v₀))
          ‼
        index₂
      ≡⟨ h₂ ⟩
        weakenTxOutput (A.outputs (A.lookupTx xs refi v₀) ‼ index₀)
      ≡⟨⟩
        weakenTxOutput (A.lookupOutput xs refi v₀ v₁)
      ∎
      where
        refi : TxOutputRef
        refi = outputRef i

        tx₀ : A.Tx
        tx₀ = A.lookupTx xs refi v₀

        xs′ : List Tx
        xs′ = weakenLedger xs

        outs₀ : List A.TxOutput
        outs₀ = A.outputs (A.lookupTx xs refi v₀)

        v₀′ : Any (λ tx → tx ♯ₜₓ ≡ id refi) xs′
        v₀′ = weaken₀ {xs} {i} v₀

        outs₁ : List TxOutput
        outs₁ = outputs (lookupTx xs′ refi v₀′)

        v₁′ : index refi < length outs₁
        v₁′ = weaken₁ {xs} {i} {v₀} v₁

        outs₂ : List TxOutput
        outs₂ = outputs (weakenTx tx₀)

        outs≡ : outs₁ ≡ outs₂
        outs≡ rewrite lookupTxWeakens {xs} {i} {v₀} = refl

        len≡ : length outs₁ ≡ length outs₂
        len≡ = cong length outs≡

        index₀ : Index outs₀
        index₀ = fromℕ≤ {index refi} v₁

        index₁ : Index outs₁
        index₁ = fromℕ≤ {index refi} v₁′

        index₂ : Index outs₂
        index₂ = cast len≡ (fromℕ≤ {index refi} v₁′)

        hh : toℕ index₂ ≡ toℕ (cast (sym (outputs≡ {tx₀})) index₀)
        hh rewrite toℕ-cast {fm = index₁} len≡
                 | toℕ-cast {fm = index₀} (sym (outputs≡ {tx₀}))
                 | toℕ-fromℕ≤ v₁′
                 | toℕ-fromℕ≤ v₁
                 = refl

        h₁ : (outs₁ ‼ index₁) ≡ (outs₂ ‼ index₂)
        h₁ = ⁉→‼ {xs = outs₁} {ys = outs₂} {ix = index₁} len≡ h₁′
          where h₁′ : (outs₁ ⁉ toℕ index₁) ≡ (outs₂ ⁉ toℕ index₁)
                h₁′ rewrite lookupTxWeakens {xs} {i} {v₀} = refl

        outputs‼ : ∀ {t} {x : Index (A.outputs t)}
             → (outputs (weakenTx t) ‼ cast (sym (outputs≡ {t})) x)
             ≡ weakenTxOutput (A.outputs t ‼ x)
        outputs‼ {t} {x} rewrite ‼-map {f = weakenTxOutput} {xs = A.outputs t} {i = x}
                               | outputs≡ {t}
                               = refl

        h₂ : (outs₂ ‼ index₂) ≡ weakenTxOutput (outs₀ ‼ index₀)
        h₂ =
          begin
            outs₂ ‼ index₂
          ≡⟨ cong (outs₂ ‼_) (toℕ-injective hh) ⟩
            outs₂ ‼ cast (sym (outputs≡ {tx₀})) index₀
          ≡⟨ outputs‼ {t = tx₀} {x = index₀} ⟩
            weakenTxOutput (outs₀ ‼ index₀)
          ∎

    lookupValue≡ : ∀ {i i∈} →
        A.lookupValue l i (vtx i i∈) (voi i i∈)
      ≡ lookupValue l′ i (vtx′ i i∈) (voi′ i i∈)
    lookupValue≡ {i} {i∈}
      rewrite lookupOutputWeakens {l} {i} (vtx i i∈) (voi i i∈)
            = refl


    map∈-cong : ∀ {A : Set} {xs : List TxInput}
                  → (f : ∀ {i} → i ∈ xs → A)
                  → (g : ∀ {i} → i ∈ xs → A)
                  → (∀ {i} → (i∈ : i ∈ xs) → f i∈ ≡ g i∈)
                  → Pointwise _≡_ (mapWith∈ xs f) (mapWith∈ xs g)
    map∈-cong {xs = []}     f g cong = Pointwise.[]
    map∈-cong {xs = x ∷ xs} f g cong =
      cong (here refl)
        Pointwise.∷
      map∈-cong (f ∘ there) (g ∘ there) λ {i} i∈ → cong (there i∈)

    mapLookupValue≡ :
        mapWith∈ (A.inputs tx) (λ {i} i∈ → A.lookupValue l i (vtx i i∈) (voi i i∈))
      ≡ mapWith∈ (inputs tx′) (λ {i} i∈ → lookupValue l′ i (vtx′ i i∈) (voi′ i i∈))
    mapLookupValue≡ =
      Pointwise-≡⇒≡ (map∈-cong
        (λ {i} i∈ → A.lookupValue l i (vtx i i∈) (voi i i∈))
        (λ {i} i∈ → lookupValue l′ i (vtx′ i i∈) (voi′ i i∈))
        (λ {i} i∈ → lookupValue≡ {i} {i∈}))

    pv₁ :
      forge tx′ +ᶜ sumᶜ (mapWith∈ (inputs tx′) λ {i} i∈ → lookupValue l′ i (vtx′ i i∈) (voi′ i i∈))
        ≡
      A.forge tx +ᶜ sumᶜ (mapWith∈ (A.inputs tx) λ {i} i∈ → A.lookupValue l i (vtx i i∈) (voi i i∈))
    pv₁ rewrite sym (cong sumᶜ mapLookupValue≡) = refl

    pv₂ :
      fee tx′ +ᶜ sumᶜ (map value (outputs tx′))
        ≡
      A.fee tx +ᶜ sumᶜ (map A.value (A.outputs tx))
    pv₂ rewrite Σvalue≡ = refl

    pv′ :
      forge tx′ +ᶜ sumᶜ (mapWith∈ (inputs tx′) λ {i} i∈ → lookupValue l′ i (vtx′ i i∈) (voi′ i i∈))
        ≡
      fee tx′ +ᶜ sumᶜ (map value (outputs tx′))
    pv′ rewrite pv₁ | pv₂ = pv

    ------------------------------------------------------------------------------------

    vds′ : ∀ i → (i∈ : i ∈ inputs tx′) →
      D i ≡ Data (lookupOutput l′ (outputRef i) (vtx′ i i∈) (voi′ i i∈))
    vds′ i i∈ rewrite lookupOutputWeakens {l} {i} (vtx i i∈) (voi i i∈) = vds i i∈

    vds″ : ∀ i → (i∈ : i ∈ inputs tx′) →
      D i ≡ Data (weakenTxOutput (A.lookupOutput l (outputRef i) (vtx i i∈) (voi i i∈)))
    vds″ i i∈ = vds i i∈

    ------------------------------------------------------------------------------------

    value≡ : ∀ {o} → value (weakenTxOutput o) ≡ A.value o
    value≡ = refl

    dataScript≡ : ∀ {o} → dataScript (weakenTxOutput o) ≡ A.dataScript o
    dataScript≡ = refl

    mapPending≡ : (map mkPendingTxOut ∘ map weakenTxOutput) (A.outputs tx)
              ≡ map A.mkPendingTxOut (A.outputs tx)
    mapPending≡
      rewrite sym (map-compose {g = mkPendingTxOut} {f = weakenTxOutput} (A.outputs tx))
            = refl

    pendingOut≡ : map mkPendingTxOut (outputs tx′)
                ≡ map A.mkPendingTxOut (A.outputs tx)
    pendingOut≡ rewrite mapPending≡
                      = refl


    mkPending≡ : ∀ {i i∈} →
        A.mkPendingTxIn l i (vtx i i∈) (voi i i∈)
      ≡ mkPendingTxIn l′ i (vtx′ i i∈) (voi′ i i∈)
    mkPending≡ {i} {i∈} =
      begin
        A.mkPendingTxIn l i (vtx i i∈) (voi i i∈)
      ≡⟨⟩
       record { value         = A.lookupValue l i (vtx i i∈) (voi i i∈)
              ; validatorHash = (validator i) ♯
              ; redeemerHash  = (redeemer i) ♯
              }
      ≡⟨ cong (λ v → record { value = v
                            ; validatorHash = (validator i) ♯
                            ; redeemerHash  = (redeemer i) ♯
                            }) (lookupValue≡ {i} {i∈}) ⟩
       record { value         = lookupValue l′ i (vtx′ i i∈) (voi′ i i∈)
              ; validatorHash = (validator i) ♯
              ; redeemerHash  = (redeemer i) ♯
              }
      ≡⟨⟩
        mkPendingTxIn l′ i (vtx′ i i∈) (voi′ i i∈)
      ∎

    pendingIn≡ : mapWith∈ (A.inputs tx) (λ {i} i∈ → A.mkPendingTxIn l i (vtx i i∈) (voi i i∈))
               ≡ mapWith∈ (inputs tx′) (λ {i} i∈ → mkPendingTxIn l′ i (vtx′ i i∈) (voi′ i i∈))
    pendingIn≡ =
      Pointwise-≡⇒≡ (map∈-cong
        (λ {i} i∈ → A.mkPendingTxIn l i (vtx i i∈) (voi i i∈))
        (λ {i} i∈ → mkPendingTxIn l′ i (vtx′ i i∈) (voi′ i i∈))
        (λ {i} i∈ → mkPending≡ {i} {i∈}))

    ptx : PendingTx
    ptx = A.mkPendingTx l tx vtx voi

    ptx′ : PendingTx
    ptx′ = mkPendingTx l′ tx′ vtx′ voi′

    pendingTx≡ : ptx ≡ ptx′
    pendingTx≡ =
      begin
        ptx
      ≡⟨⟩
        record { txHash  = tx A.♯ₜₓ
               ; inputs  = mapWith∈ (A.inputs tx) λ {i} i∈ → A.mkPendingTxIn l i (vtx i i∈) (voi i i∈)
               ; outputs = map A.mkPendingTxOut (A.outputs tx)
               ; forge   = A.forge tx
               ; fee     = A.fee tx
               }
      ≡⟨ helper ⟩
        record { txHash  = tx′ ♯ₜₓ
               ; inputs  = mapWith∈ (inputs tx′) λ {i} i∈ → mkPendingTxIn l′ i (vtx′ i i∈) (voi′ i i∈)
               ; outputs = map mkPendingTxOut (outputs tx′)
               ; forge   = forge tx′
               ; fee     = fee tx′
               }
      ≡⟨⟩
        ptx′
      ∎
      where
        helper : record { txHash  = tx A.♯ₜₓ
                        ; inputs  = mapWith∈ (A.inputs tx) λ {i} i∈ → A.mkPendingTxIn l i (vtx i i∈) (voi i i∈)
                        ; outputs = map A.mkPendingTxOut (A.outputs tx)
                        ; forge   = A.forge tx
                        ; fee     = A.fee tx
                        }
               ≡ record { txHash  = tx′ ♯ₜₓ
                        ; inputs  = mapWith∈ (inputs tx′) λ {i} i∈ → mkPendingTxIn l′ i (vtx′ i i∈) (voi′ i i∈)
                        ; outputs = map mkPendingTxOut (outputs tx′)
                        ; forge   = forge tx′
                        ; fee     = fee tx′
                        }
        helper rewrite weakenTx-preserves♯ tx
                     | pendingOut≡
                     | pendingIn≡
                     = refl

    state≡ : getState l′ ≡ getState l
    state≡ = cong (λ x → record {height = x}) (length-map weakenTx l)

    weakenRunValidation : ∀ {i i∈ o} {v : D i ≡ A.Data o} {v′ : D i ≡ Data (weakenTxOutput o)} →
        T (runValidation   ptx′ i (weakenTxOutput o) v′ (getState l′))
      ≡ T (A.runValidation ptx  i o                  v  (getState l))
    weakenRunValidation {_} {_} {o} {refl} {refl}
      rewrite state≡
            | sym pendingTx≡
            | value≡      {o}
            | dataScript≡ {o}
            = refl

    aiv′ :
      ∀ i → (i∈ : i ∈ inputs tx′) →
        let out = lookupOutput l′ (outputRef i) (vtx′ i i∈) (voi′ i i∈)
        in T (runValidation ptx′ i out (vds′ i i∈) (getState l′))
    aiv′ i i∈
      rewrite lookupOutputWeakens {l} {i} (vtx i i∈) (voi i i∈)
            | weakenRunValidation {i} {i∈} {A.lookupOutput l (outputRef i) (vtx i i∈) (voi i i∈)}
                                           {vds i i∈} {vds″ i i∈}
            = aiv i i∈

    ------------------------------------------------------------------------------------

    vvh′ : ∀ i → (i∈ : i ∈ inputs tx′) →
      let out = lookupOutput l′ (outputRef i) (vtx′ i i∈) (voi′ i i∈)
      in (address out) ♯ᵇ ≡ (validator i) ♯
    vvh′ i i∈
      rewrite lookupOutputWeakens {l} {i} (vtx i i∈) (voi i i∈)
            | weakenTxOutput-preserves♯ (A.lookupOutput l (outputRef i) (vtx i i∈) (voi i i∈))
            = vvh i i∈

    ------------------------------------------------------------------------------------

    frg′ : ∀ c → c ∈ keys (forge tx′) →
      ∃[ i ] ∃ λ (i∈ : i ∈ inputs tx′) →
        let out = lookupOutput l′ (outputRef i) (vtx′ i i∈) (voi′ i i∈)
        in (address out) ♯ᵇ ≡ c
    frg′ c c∈
      with frg c c∈
    ... | (i , i∈ , p) = (i , i∈ , helper)
      where
        helper : (address (lookupOutput l′ (outputRef i) (vtx′ i i∈) (voi′ i i∈))) ♯ᵇ ≡ c
        helper
          rewrite lookupOutputWeakens {l} {i} (vtx i i∈) (voi i i∈)
                | weakenTxOutput-preserves♯ (A.lookupOutput l (outputRef i) (vtx i i∈) (voi i i∈))
                = p
