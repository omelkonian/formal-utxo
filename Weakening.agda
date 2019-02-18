------------------------------------------------------------------------
-- Weakening (adding available addresses).
------------------------------------------------------------------------

module Weakening where

open import Level         using (0ℓ)
open import Function      using (_∘_; _∋_; _$_; case_of_)
open import Data.Product  using (Σ; Σ-syntax; proj₁; proj₂; ∃; ∃-syntax; _,_; map₁)
open import Data.Unit     using (⊤; tt)
open import Data.Bool     using (Bool; true; false; T)
open import Data.Fin      using (Fin; toℕ; fromℕ≤; inject≤)
  renaming (zero to 0ᶠ; suc to sucᶠ)
open import Data.Fin.Properties using (toℕ-injective; toℕ-fromℕ≤; toℕ-inject≤)
open import Data.Nat      using (ℕ; zero; suc; _+_; _<_; _≟_)
open import Data.Nat.Properties using (suc-injective)
open import Data.List     using (List; []; _∷_; _∷ʳ_; [_]; _++_; length; upTo; map; sum)
open import Data.List.Any using (Any; here; there)
open import Data.List.Properties using (length-map; map-compose)
open import Data.List.Relation.Pointwise using (Pointwise; Pointwise-≡⇒≡)

open import Relation.Binary using (Rel)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import Utilities.Lists
open import Types

Ledger′ : List Address → Set₁
Ledger′ as = Ledger
  where open import UTxO as

Tx′ : List Address → Set₁
Tx′ as = Tx
  where open import UTxO as

IsValidTx′ : (as : List Address) → Tx′ as → Ledger′ as → Set₁
IsValidTx′ as t l = IsValidTx t l
  where open import UTxO as

TxOutput′ : List Address → Set₁
TxOutput′ as = TxOutput
  where open import UTxO as

weakenTxOutput : ∀ {as bs} → Prefix as bs → TxOutput′ as → TxOutput′ bs
weakenTxOutput {as} {bs} pr
    record { value = v ; dataScript = ds ; address = addr }
  = record { value = v ; dataScript = ds ; address = inject≤ addr (prefix-length pr) }
  where open import UTxO bs

weakenTx : ∀ {as bs} → Prefix as bs → Tx′ as → Tx′ bs
weakenTx {as} {bs} pr
    record { inputs = inputs
           ; outputs = outputs
           ; forge = forge
           ; fee = fee }
  = record { inputs = inputs
           ; outputs = map (weakenTxOutput pr) outputs
           ; forge = forge
           ; fee = fee
           }

weakenLedger : ∀ {as bs} → Prefix as bs → Ledger′ as → Ledger′ bs
weakenLedger pr = map (weakenTx pr)

weakening : ∀ {as bs : List Address} {tx : Tx′ as} {l : Ledger′ as}

          → (pr : Prefix as bs) -- T0D0 generalize to subset
          → IsValidTx′ as tx l
            -------------------------------------------------------
          → IsValidTx′ bs (weakenTx pr tx) (weakenLedger pr l)

weakening {as} {bs} {tx} {l} pr
    record
      { validTxRefs          = vtx
      ; validOutputIndices   = voi
      ; validOutputRefs      = vor
      ; validDataScriptTypes = vds
      ; preservesValues      = pv
      ; noDoubleSpending     = nds
      ; allInputsValidate    = aiv
      ; validateValidHashes  = vvh
      }
  = record
      { validTxRefs          = weakenValidTxRefs vtx
      ; validOutputIndices   = weakenValidOutputIndices vtx voi
      ; validOutputRefs      = weakenValidOutputRefs vor
      ; validDataScriptTypes = weakenValidDataScriptTypes vtx voi vds
      ; preservesValues      = weakenPreservesValues vtx voi pv
      ; noDoubleSpending     = weakenNoDoubleSpending nds
      ; allInputsValidate    = weakenAllInputsValidate vtx voi vds aiv
      ; validateValidHashes  = weakenValidateValidHashes vtx voi vvh
      }
  where
    open import UTxO as
      as U₀ using ()
    open import UTxO bs

    open import Relation.Binary.PropositionalEquality using (_≡_; setoid)
    open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-map⁺)

    import Data.List.Membership.Setoid as SetoidMembership
    open SetoidMembership (setoid TxInput)     using ()
      renaming (_∈_ to _∈ⁱ_; mapWith∈ to map∈)
    open SetoidMembership (setoid TxOutputRef) using ()
      renaming (_∈_ to _∈ᵒ_)
    open SetoidMembership (setoid Tx) using ()
      renaming (find to find′)
    open SetoidMembership (setoid U₀.Tx) using ()
      renaming (find to find₀)

    open import Data.List.Membership.Setoid (setoid TxInput) using (_∈_; mapWith∈)

    open SETₒ using () renaming (_∈_ to _∈ₒ_)

    ------------------------------------------------------------------------------------

    -- intuitive and reasonable (modulo implementation details)
    postulate
      weakenTx-preserves-♯ : ∀ {x : U₀.Tx} → x ♯ ≡ weakenTx pr x ♯

    tx′ : Tx
    tx′ = weakenTx pr tx

    l′ : Ledger
    l′ = weakenLedger pr l

    ------------------------------------------------------------------------------------

    weaken₀ : ∀ {xs i}
      → Any (λ tx → tx ♯ ≡ id (outputRef i)) xs
      → Any (λ tx → tx ♯ ≡ id (outputRef i)) (weakenLedger pr xs)
    weaken₀ {_}      {i} (here px) = here (trans (sym weakenTx-preserves-♯) px)
    weaken₀ {x ∷ xs} {i} (there p) = there (weaken₀ {xs} {i} p)

    weakenValidTxRefs :
       (∀ i → i ∈ⁱ U₀.inputs tx → Any (λ tx → tx ♯ ≡ id (outputRef i)) l)
      → ∀ i → i ∈ⁱ inputs tx′   → Any (λ tx → tx ♯ ≡ id (outputRef i)) l′
    weakenValidTxRefs validTxRefs i i∈ = weaken₀ {l} {i} (validTxRefs i i∈)

    ------------------------------------------------------------------------------------

    import Data.Fin.Properties using (toℕ-inject)

    outputs≡ : ∀ {t} → length (outputs (weakenTx pr t))
                     ≡ length (U₀.outputs t)
    outputs≡ {t} = length-map (weakenTxOutput pr) (U₀.outputs t)

    outputs‼ : ∀ {t} {x : Index (U₀.outputs t)}
             → (outputs (weakenTx pr t) ‼ cast (sym (outputs≡ {t})) x)
             ≡ weakenTxOutput pr (U₀.outputs t ‼ x)
    outputs‼ {t} {x}
      rewrite ‼-map {f = weakenTxOutput pr} {xs = U₀.outputs t} {i = x}
            | outputs≡ {t}
            = refl

    lookupTxWeakens : ∀ {xs i v₀}
      → lookupTx (weakenLedger pr xs) (outputRef i) (weaken₀ {xs} {i} v₀)
      ≡ weakenTx pr (U₀.lookupTx xs (outputRef i) v₀)
    lookupTxWeakens {v₀ = (here px)}  = refl
    lookupTxWeakens {v₀ = (there v₀)} = lookupTxWeakens {v₀ = v₀}

    weaken₁ : ∀ {xs i v₀}
      → index (outputRef i) <
           length (U₀.outputs (
             U₀.lookupTx xs
                         (outputRef i)
                         v₀
           ))
      → index (outputRef i) <
           length (outputs (
             lookupTx (weakenLedger pr xs)
                      (outputRef i)
                      (weaken₀ {xs} {i} v₀)
           ))
    weaken₁ {xs} {i} {v₀} p
      rewrite lookupTxWeakens {xs} {i} {v₀}
            | outputs≡ {U₀.lookupTx xs (outputRef i) v₀}
            = p

    weakenValidOutputIndices :
        (validTxRefs₀ : ∀ i → i ∈ⁱ U₀.inputs tx →
           Any (λ tx → tx ♯ ≡ id (outputRef i)) l)
      → (valid₀ : ∀ i → (i∈₀ : i ∈ⁱ U₀.inputs tx) →
          index (outputRef i) <
            length (U₀.outputs (U₀.lookupTx l (outputRef i)
                               (validTxRefs₀ i i∈₀))))
      → ∀ i → (i∈ : i ∈ⁱ inputs tx′) →
          index (outputRef i) <
            length (outputs (lookupTx l′ (outputRef i)
                            (weakenValidTxRefs validTxRefs₀ i i∈)))
    weakenValidOutputIndices validTxRefs₀ v₀ i i∈ =
      weaken₁ {l} {i} {validTxRefs₀ i i∈} (v₀ i i∈)

    ------------------------------------------------------------------------------------

    weakenIndices : ∀ {x}
      → indices (outputs (weakenTx pr x))
      ≡ indices (U₀.outputs x)
    weakenIndices {x}
      rewrite length-map (weakenTxOutput pr) (U₀.outputs x)
            = refl

    weakenUnspentOutputsTx : ∀ {x}
      → unspentOutputsTx (weakenTx pr x)
      ≡ U₀.unspentOutputsTx x
    weakenUnspentOutputsTx {x}
      rewrite weakenIndices {x}
            | sym (weakenTx-preserves-♯ {x})
            = refl

    weakenUnspentOutputs : ∀ {xs}
      → unspentOutputs (weakenLedger pr xs)
      ≡ U₀.unspentOutputs xs
    weakenUnspentOutputs {[]} = refl
    weakenUnspentOutputs {x ∷ xs}
      rewrite weakenUnspentOutputs {xs}
            | weakenUnspentOutputsTx {x}
            = refl

    weakenValidOutputRefs :
        (validOutputRefs₀ :
          ∀ i → i ∈ⁱ U₀.inputs tx → outputRef i SETₒ.∈′ U₀.unspentOutputs l)
        → ∀ i → i ∈ⁱ inputs tx′ → outputRef i SETₒ.∈′ unspentOutputs l′
    weakenValidOutputRefs v₀ i i∈
      rewrite weakenUnspentOutputs {l}
            = v₀ i i∈

    ------------------------------------------------------------------------------------

    forge≡ : U₀.forge tx ≡ forge tx′
    forge≡ = refl

    fee≡ : U₀.fee tx ≡ fee tx′
    fee≡ = refl

    mapValue≡ : (map value ∘ map (weakenTxOutput pr)) (U₀.outputs tx)
              ≡ map U₀.value (U₀.outputs tx)
    mapValue≡
      rewrite sym (map-compose {g = value} {f = weakenTxOutput pr} (U₀.outputs tx))
            = refl

    Σvalue≡ : Σ[ U₀.value ∈ U₀.outputs tx ] ≡ Σ[ value ∈ outputs tx′ ]
    Σvalue≡ rewrite mapValue≡ = refl

    lookupOutputWeakens : ∀ {xs i}
      → (v₀ : Any (λ tx → tx ♯ ≡ id (outputRef i)) xs)
      → (v₁ : index (outputRef i) < length (U₀.outputs (U₀.lookupTx xs (outputRef i) v₀)))
      → lookupOutput (weakenLedger pr xs)
                     (outputRef i)
                     (weaken₀ {xs} {i} v₀)
                       (weaken₁ {xs} {i} {v₀} v₁)
      ≡ weakenTxOutput pr (
          U₀.lookupOutput xs
                          (outputRef i)
                          v₀
                          v₁
        )
    lookupOutputWeakens {xs} {i} v₀ v₁ =
      begin
        lookupOutput xs′ refi v₀′ v₁′
      ≡⟨⟩
        outputs (lookupTx xs′ refi v₀′)
          ‼
        index₁
      ≡⟨ h₁ ⟩
        outputs (weakenTx pr (U₀.lookupTx xs refi v₀))
          ‼
        index₂
      ≡⟨⟩
        map (weakenTxOutput pr) (U₀.outputs (U₀.lookupTx xs refi v₀))
          ‼
        index₂
      ≡⟨ h₂ ⟩
        weakenTxOutput pr (
          U₀.outputs (U₀.lookupTx xs refi v₀)
            ‼
          index₀
        )
      ≡⟨⟩
        weakenTxOutput pr (U₀.lookupOutput xs refi v₀ v₁)
      ∎
      where
        refi : TxOutputRef
        refi = outputRef i

        tx₀ : U₀.Tx
        tx₀ = U₀.lookupTx xs refi v₀

        xs′ : List Tx
        xs′ = weakenLedger pr xs

        outs₀ : List U₀.TxOutput
        outs₀ = U₀.outputs (U₀.lookupTx xs refi v₀)

        v₀′ : Any (λ tx → tx ♯ ≡ id refi) xs′
        v₀′ = weaken₀ {xs} {i} v₀

        outs₁ : List TxOutput
        outs₁ = outputs (lookupTx xs′ refi v₀′)

        v₁′ : index refi < length outs₁
        v₁′ = weaken₁ {xs} {i} {v₀} v₁

        outs₂ : List TxOutput
        outs₂ = outputs (weakenTx pr tx₀)

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

        h₂ : (outs₂ ‼ index₂) ≡ weakenTxOutput pr (outs₀ ‼ index₀)
        h₂ =
          begin
            outs₂ ‼ index₂
          ≡⟨ cong (outs₂ ‼_) (toℕ-injective hh) ⟩
            outs₂ ‼ cast (sym (outputs≡ {tx₀})) index₀
          ≡⟨ outputs‼ {t = tx₀} {x = index₀} ⟩
            weakenTxOutput pr (outs₀ ‼ index₀)
          ∎

    lookupValue≡ : ∀ {v₀ v₁ i i∈} →
        U₀.lookupValue l i (v₀ i i∈) (v₁ i i∈)
      ≡ lookupValue l′ i (weakenValidTxRefs v₀ i i∈)
                         (weakenValidOutputIndices v₀ v₁ i i∈)
    lookupValue≡ {v₀} {v₁} {i} {i∈}
      rewrite lookupOutputWeakens {l} {i} (v₀ i i∈) (v₁ i i∈)
            = refl

    map∈-cong : ∀ {xs : List TxInput}
                  → (f : ∀ {i} → i ∈ xs → ℕ)
                  → (g : ∀ {i} → i ∈ xs → ℕ)
                  → (∀ {i} → (i∈ : i ∈ xs) → f i∈ ≡ g i∈)
                  → Pointwise _≡_ (map∈ xs f) (map∈ xs g)
    map∈-cong {[]}     f g cong = Pointwise.[]
    map∈-cong {x ∷ xs} f g cong =
      cong (here refl)
        Pointwise.∷
      map∈-cong (f ∘ there) (g ∘ there) λ {i} i∈ → cong (there i∈)

    mapLookupValue≡ : ∀ {v₀ v₁} →
        map∈ (U₀.inputs tx) (λ {i} i∈ → U₀.lookupValue l i (v₀ i i∈) (v₁ i i∈))
      ≡ map∈ (inputs tx′) (λ {i} i∈ → lookupValue l′ i
                                        (weakenValidTxRefs v₀ i i∈)
                                        (weakenValidOutputIndices v₀ v₁ i i∈))
    mapLookupValue≡ {v₀} {v₁} =
      Pointwise-≡⇒≡ (map∈-cong
        (λ {i} i∈ → U₀.lookupValue l i (v₀ i i∈) (v₁ i i∈))
        (λ {i} i∈ → lookupValue l′ i (weakenValidTxRefs v₀ i i∈)
                                     (weakenValidOutputIndices v₀ v₁ i i∈))
        (λ {i} i∈ → lookupValue≡ {v₀} {v₁} {i} {i∈}))

    weakenPreservesValues :
        (validTxRefs₀ : ∀ i → i ∈ⁱ U₀.inputs tx →
          Any (λ tx → tx ♯ ≡ id (outputRef i)) l)
      → (validOutputIndices₀ : ∀ i → (i∈₀ : i ∈ⁱ U₀.inputs tx) →
          index (outputRef i) <
            length (U₀.outputs (U₀.lookupTx l (outputRef i) (validTxRefs₀ i i∈₀))))
      → (preservesValues₀ :
          U₀.forge tx
          + sum (map∈ (U₀.inputs tx) λ {i} i∈ →
              U₀.lookupValue l i (validTxRefs₀ i i∈) (validOutputIndices₀ i i∈))
            ≡
          U₀.fee tx + Σ[ U₀.value ∈ U₀.outputs tx ])
      → forge tx′
      + sum (map∈ (inputs tx′) λ {i} i∈ →
          lookupValue l′ i
            (weakenValidTxRefs validTxRefs₀ i i∈)
            (weakenValidOutputIndices validTxRefs₀ validOutputIndices₀ i i∈))
          ≡
        fee tx′ + Σ[ value ∈ outputs tx′ ]
    weakenPreservesValues v₀ v₁ v₂
      rewrite forge≡
            | fee≡
            | Σvalue≡
            | mapLookupValue≡ {v₀} {v₁}
            = v₂

    ------------------------------------------------------------------------------------

    weakenValidDataScriptTypes :
        (validTxRefs₀ : ∀ i → i ∈ⁱ U₀.inputs tx →
          Any (λ tx → tx ♯ ≡ id (outputRef i)) l)
      → (validOutputIndices₀ : ∀ i → (i∈₀ : i ∈ⁱ U₀.inputs tx) →
          index (outputRef i) <
            length (U₀.outputs (U₀.lookupTx l (outputRef i) (validTxRefs₀ i i∈₀))))
      → (validDataScriptTypes₀ :
          ∀ i → (i∈ : i ∈ⁱ U₀.inputs tx) →
            D i ≡ U₀.Data (U₀.lookupOutput l (outputRef i) (validTxRefs₀ i i∈) (validOutputIndices₀ i i∈)))
      → ∀ i → (i∈ : i ∈ⁱ inputs tx′) →
          D i ≡ Data (lookupOutput l′ (outputRef i)
                     (weakenValidTxRefs validTxRefs₀ i i∈)
                     (weakenValidOutputIndices validTxRefs₀ validOutputIndices₀ i i∈))
    weakenValidDataScriptTypes v₀ v₁ v₂ i i∈
      rewrite lookupOutputWeakens {l} {i} (v₀ i i∈) (v₁ i i∈)
            = v₂ i i∈

    weakenValidDataScriptTypes′ :
        (validTxRefs₀ : ∀ i → i ∈ⁱ U₀.inputs tx →
          Any (λ tx → tx ♯ ≡ id (outputRef i)) l)
      → (validOutputIndices₀ : ∀ i → (i∈₀ : i ∈ⁱ U₀.inputs tx) →
          index (outputRef i) <
            length (U₀.outputs (U₀.lookupTx l (outputRef i) (validTxRefs₀ i i∈₀))))
      → (validDataScriptTypes₀ :
          ∀ i → (i∈ : i ∈ⁱ U₀.inputs tx) →
            D i ≡ U₀.Data (U₀.lookupOutput l (outputRef i) (validTxRefs₀ i i∈) (validOutputIndices₀ i i∈)))
      → ∀ i → (i∈ : i ∈ⁱ inputs tx′) →
          D i ≡ Data (weakenTxOutput pr
                     (U₀.lookupOutput l (outputRef i) (validTxRefs₀ i i∈) (validOutputIndices₀ i i∈)))
    weakenValidDataScriptTypes′ v₀ v₁ v₂ i i∈ = v₂ i i∈

    ------------------------------------------------------------------------------------

    weakenNoDoubleSpending :
      (noDoubleSpending₀ :
        SETₒ.noDuplicates (map outputRef (U₀.inputs tx)))
      → SETₒ.noDuplicates (map outputRef (inputs tx′))
    weakenNoDoubleSpending v₀ = v₀

    ------------------------------------------------------------------------------------

    value≡ : ∀ {o} → value (weakenTxOutput pr o) ≡ U₀.value o
    value≡ = refl

    dataScript≡ : ∀ {o} → dataScript (weakenTxOutput pr o) ≡ U₀.dataScript o
    dataScript≡ = refl

    weakenRunValidation : ∀ {o : U₀.TxOutput} {i : TxInput} {st : State}
                            {v : D i ≡ U₀.Data o}
                            {v′ : D i ≡ Data (weakenTxOutput pr o)}
      → U₀.runValidation i o v st
          ≡
        runValidation i (weakenTxOutput pr o) v′ st
    weakenRunValidation {o} {_} {_} {refl} {refl}
      rewrite value≡ {o}
            | dataScript≡ {o}
            = refl

    weakenAllInputsValidate :
        (validTxRefs₀ : ∀ i → i ∈ⁱ U₀.inputs tx →
           Any (λ tx → tx ♯ ≡ id (outputRef i)) l)
      → (validOutputIndices₀ : ∀ i → (i∈₀ : i ∈ⁱ U₀.inputs tx) →
          index (outputRef i) <
            length (U₀.outputs (U₀.lookupTx l (outputRef i) (validTxRefs₀ i i∈₀))))
      → (validDataScriptTypes₀ :
          ∀ i → (i∈ : i ∈ⁱ U₀.inputs tx) →
            D i ≡ U₀.Data (U₀.lookupOutput l (outputRef i) (validTxRefs₀ i i∈) (validOutputIndices₀ i i∈)))
      → (allInputsValidate₀ :
          ∀ i → (i∈ : i ∈ⁱ U₀.inputs tx) →
            let
              out : U₀.TxOutput
              out = U₀.lookupOutput l (outputRef i) (validTxRefs₀ i i∈) (validOutputIndices₀ i i∈)
            in
              ∀ (st : State) →
                T (U₀.runValidation i out (validDataScriptTypes₀ i i∈) st))
      → ∀ i → (i∈ : i ∈ⁱ inputs tx′) →
          let
            out : TxOutput
            out = lookupOutput l′ (outputRef i) (weakenValidTxRefs validTxRefs₀ i i∈)
                                                (weakenValidOutputIndices validTxRefs₀ validOutputIndices₀ i i∈)
          in
            ∀ (st : State) →
              T (runValidation i out (weakenValidDataScriptTypes validTxRefs₀ validOutputIndices₀
                                                                 validDataScriptTypes₀ i i∈) st)
    weakenAllInputsValidate v₀ v₁ v₂ v₃ i i∈ st
      rewrite lookupOutputWeakens {l} {i} (v₀ i i∈) (v₁ i i∈)
            | sym (weakenRunValidation {U₀.lookupOutput l (outputRef i) (v₀ i i∈) (v₁ i i∈)}
                                       {i} {st}
                                       {v = v₂ i i∈}
                                       {v′ = weakenValidDataScriptTypes′ v₀ v₁ v₂ i i∈})
            = v₃ i i∈ st

    ------------------------------------------------------------------------------------

    weakenValidateValidHashes :
        (validTxRefs₀ : ∀ i → i ∈ⁱ U₀.inputs tx →
          Any (λ tx → tx ♯ ≡ id (outputRef i)) l)
      → (validOutputIndices₀ : ∀ i → (i∈₀ : i ∈ⁱ U₀.inputs tx) →
          index (outputRef i) <
            length (U₀.outputs (U₀.lookupTx l (outputRef i) (validTxRefs₀ i i∈₀))))
      → (validateValidHashes₀ :
          ∀ i → (i∈ : i ∈ⁱ U₀.inputs tx) →
            toℕ (U₀.address (U₀.lookupOutput l (outputRef i)
              (validTxRefs₀ i i∈)
              (validOutputIndices₀ i i∈)))
              ≡
            (validator i) ♯)
      → ∀ i → (i∈ : i ∈ⁱ inputs tx′) →
          toℕ (address (lookupOutput l′ (outputRef i)
            (weakenValidTxRefs validTxRefs₀ i i∈)
            (weakenValidOutputIndices validTxRefs₀ validOutputIndices₀ i i∈)))
            ≡
          (validator i) ♯
    weakenValidateValidHashes v₀ v₁ v₂ i i∈ =
      begin
        toℕ (address (lookupOutput l′ (outputRef i)
          (weakenValidTxRefs v₀ i i∈)
          (weakenValidOutputIndices v₀ v₁ i i∈)))
      ≡⟨ hhh ⟩
        toℕ (U₀.address (U₀.lookupOutput l (outputRef i) (v₀ i i∈) (v₁ i i∈)))
      ≡⟨ v₂ i i∈ ⟩
        (validator i) ♯
      ∎

      where
        address≡ : ∀ {t}
          → toℕ (address (weakenTxOutput pr t))
          ≡ toℕ (U₀.address t)
        address≡ {t} rewrite toℕ-inject≤ (U₀.address t) (prefix-length pr)
                           = refl

        hhh :
          toℕ (address (lookupOutput (weakenLedger pr l) (outputRef i)
            (weakenValidTxRefs v₀ i i∈) (weakenValidOutputIndices v₀ v₁ i i∈)))
          ≡
          toℕ (U₀.address (U₀.lookupOutput l (outputRef i) (v₀ i i∈) (v₁ i i∈)))
        hhh rewrite lookupOutputWeakens {l} {i} (v₀ i i∈) (v₁ i i∈)
                  | address≡ {t = U₀.lookupOutput l (outputRef i) (v₀ i i∈) (v₁ i i∈)}
                  = refl


    ------------------------------------------------------------------------------------
