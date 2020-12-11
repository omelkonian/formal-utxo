open import Data.Nat.Properties
open import Data.Nat.Induction using (<-wellFounded)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺)

open import Prelude.Init renaming (sum to ∑ℕ)
open import Prelude.General
open import Prelude.Lists

open import UTxO.Hashing
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities
open import UTxO.Validity
open import UTxO.GlobalPreservation
open import StateMachine.Base hiding (origin)

module StateMachine.Extract
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  {L : ∃ ValidLedger} {jo : Is-just (StateMachine.origin sm)}
  where

open CEM {sm = sm}
open import StateMachine.Properties {sm = sm}
open import StateMachine.Inductive {sm = sm}

open FocusTokenClass nftₛₘ
open import UTxO.TokenProvenance nftₛₘ
open import UTxO.TokenProvenanceNF nftₛₘ
open import StateMachine.Initiality {sm = sm}

private
  variable
    tx : Tx
    n  : Quantity

outputs◆ : Tx → List TxOutput
outputs◆ = filter (◆∈?_ ∘ value) ∘ outputs

ams-outputs◆ : ∀ {tx}
  → tx ∈′ L
  → AtMostSingleton (outputs◆ tx)
ams-outputs◆ {tx} tx∈
  with l′ , l≺  ← ∈⇒Suffix tx∈
  = qed
  where
    open ≤-Reasoning

    l  = tx ∷ l′
    vl = ≼⇒valid (proj₂ L) l≺

    ∑forge≤1 : NonFungible (_ , vl) nftₛₘ
    ∑forge≤1 = JustOrigin.nf jo (_ , vl)

    ∑≥ᶜ : T $ ∑ l forge ≥ᶜ ∑ (outputs tx) value
    ∑≥ᶜ rewrite globalPreservation {vl = vl} = ∑utxo≥∑out tx l′

    ∑≥ : ∑ l forge ◆ ≥ ∑ (outputs◆ tx) value ◆
    ∑≥ = begin ∑ (outputs◆ tx) value ◆ ≡⟨ ∑-filter-◆ {xs = outputs tx} {fv = value} ⟩
               ∑ (outputs tx) value ◆  ≤⟨ ≥ᶜ-◆ {x = ∑ l forge} {y = ∑ (outputs tx) value} ∑≥ᶜ ⟩
               ∑ l forge ◆             ∎

    qed : AtMostSingleton (outputs◆ tx)
    qed with outputs◆ tx | L.All.all-filter (◆∈?_ ∘ value) (outputs tx) | ∑≥
    ... | []         | []            | _   = tt
    ... | _ ∷ []     | _ ∷ _         | _   = tt
    ... | x ∷ y ∷ os | ◆∈x ∷ ◆∈y ∷ _ | ∑≥′ = ⊥-elim $ ¬i≥x+y ∑forge≤1 ◆∈x ◆∈y i≥x+y
      where
        ⊆-helper : value x ◆ ∷ value y ◆ ∷ [] ⊆ value x ◆ ∷ value y ◆ ∷ map (_◆ ∘ value) os
        ⊆-helper (here refl)         = here refl
        ⊆-helper (there (here refl)) = there (here refl)
        ⊆-helper (there (there ()))

        i≥x+y : ∑ l forge ◆ ≥ value x ◆ + value y ◆
        i≥x+y = begin value x ◆ + value y ◆                            ≡⟨ cong (value x ◆ +_)
                                                                               (sym $ +-identityʳ (value y ◆)) ⟩
                      ∑ℕ (value x ◆ ∷ value y ◆ ∷ [])                  ≤⟨ ∑ℕ-⊆ ⊆-helper ⟩
                      ∑ℕ (value x ◆ ∷ value y ◆ ∷ map (_◆ ∘ value) os) ≡⟨ sym $ ∑-◆ {xs = x ∷ y ∷ os} {f = value} ⟩
                      ∑ (x ∷ y ∷ os) value ◆                           ≤⟨ ∑≥′ ⟩
                      ∑ l forge ◆                                      ∎

data X¹ : Tx → Tx → Set where

  root :

      (tx : Tx)
    → (tx∈ : tx ∈′ L)
    → T (policyₛₘ $ record {this = ℂ; txInfo = mkTxInfo (proj₁ $ ∈⇒Suffix tx∈) tx})
      -----------------------------------------------------------------------------
    → X¹ tx tx

  cons : ∀ {tx tx′ tx″}

    → X¹ tx tx′
    → tx″ ∈′ L
    → tx′ ↝⟦ 1 ⟧ tx″
      --------------
    → X¹ tx tx″

∣_∣ᵗ : Trace L tx n → ℕ
∣_∣ᵗ = L.NE.length ∘ txs

X→X¹ :
    n > 0
  → (tr : Trace L tx n)
  → T (policyₛₘ $ mkPendingMPS {L = L} tr ℂ)
    -----------------------------------------
  → X¹ (origin tr) tx

X→X¹ {n = n} n>0 tr = go tr (<-wellFounded ∣ tr ∣ᵗ)
  where
    -- NB: well-founded recursion used here, because Agda could not figure out tr′ is structurally smaller!!
    go : ∀ (tr : Trace L tx n) → Acc _<_ ∣ tr ∣ᵗ → T (policyₛₘ $ mkPendingMPS {L = L} tr ℂ) → X¹ (origin tr) tx
    go record {txs = tx ∷ []; trace∈ = tx∈ ∷ []; linked = root .tx _; head≡ = refl} _ p≡
      = root tx tx∈ p≡
    go record {txs = tx′ ∷ (tx ∷ txs); trace∈ = tx∈ ∷ tr∈; linked = cons {tx ∷ txs}{tx′} lnk tx↝; head≡ = refl}
       (acc a) p≡
       rewrite last-∷ {x = tx′}{tx ∷ txs}
       = cons (go tr′ (a _ (s≤s ≤-refl)) p≡) tx∈ tx↝⟦1⟧tx′
       where
         tr′ : Trace L tx n
         tr′ = record {txs = tx ∷ txs; trace∈ = tr∈; linked = lnk; head≡ = refl}

         tx↝⟦1⟧tx′ : tx ↝⟦ 1 ⟧ tx′
         tx↝⟦1⟧tx′ = weaken-↝ {tx = tx}{tx′} tx↝ n>0

OutputsWith◆ : Tx → S → Set
OutputsWith◆ tx s =
  ∃ λ v → outputs◆ tx ≡ [ record {value = v; address = 𝕍; datumHash = toData s ♯ᵈ} ]

record TxS (tx : Tx) (s : S) : Set where
  field
    tx∈ : tx ∈′ L
    s∈  : OutputsWith◆ tx s

∃TxS = ∃ λ tx → ∃ λ s → TxS tx s

h₀ : ∀ {tx}
  → (tx∈ : tx ∈′ L)
  → T (policyₛₘ $ record {this = ℂ; txInfo = mkTxInfo (proj₁ $ ∈⇒Suffix tx∈) tx})
  → ∃ λ s → Init s × TxS tx s
h₀ {tx = tx} tx∈ p≡
  with v , s , _ , outs≡ , init-s
       ← Tpolicy⇒ {tx = tx} {l = proj₁ $ ∈⇒Suffix tx∈} refl refl p≡
  = s , init-s , record {tx∈ = tx∈; s∈ = v , outs≡}

hh : ∀ {tx tx′}
  → tx ↝⟦ 1 ⟧ tx′
  → (tx∈ : tx′ ∈′ L)
    --------------------------------
  → let l = proj₁ $ ∈⇒Suffix tx∈
    in ∃ λ i → ∃ λ o → (i ∈ inputs tx′)
                     × (o ∈ outputs tx)
                     × (◆∈ value o)
                     × (getSpentOutput l i ≡ just o)
hh {tx = tx}{tx′} (or∈ , o , ⁉≡just , ◆∈v) tx∈
  = i , o , i∈ , o∈ , ◆∈v , getSpent≡
  where
    l = proj₁ $ ∈⇒Suffix tx∈

    ∃i : ∃ λ i → i ∈ inputs tx′ × (tx ♯ₜₓ ≡ hid (outputRef i))
    ∃i  = find $ L.Any.map⁻ or∈
    i   = proj₁ ∃i
    i∈  = proj₁ $ proj₂ ∃i
    id≡ = proj₂ $ proj₂ ∃i

    o∈ : o ∈ outputs tx
    o∈ = just-⁉⇒∈ {i = index (L.Any.lookup or∈)} ⁉≡just

    index≡ : L.Any.lookup or∈ ≡ outputRef i
    index≡ = lookup≡find∘map⁻ {xs = inputs tx′} {f = outputRef} or∈

    ⁉≡just′ : outputs tx ⟦ index (outputRef i) ⟧ ≡ just o
    ⁉≡just′ = subst (λ x → outputs tx ⟦ index x ⟧ ≡ just o) index≡ ⁉≡just

    vtx : IsValidTx tx′ l
    vtx = tx∈⇒valid {L = L} tx∈

    vvh : Is-just (getSpentOutput l i)
    vvh = Any⇒Is-just {mx = getSpentOutput l i} $ L.All.lookup (validateValidHashes vtx) i∈

    getSpent≡ : getSpentOutput l i ≡ just o
    getSpent≡ = lookup-⟦⟧ {tx = tx}{l}{i}{o} vvh (sym id≡) ⁉≡just′

h : ∀ {tx tx′ s}
  → TxS tx s
  → tx′ ∈′ L
  → tx ↝⟦ 1 ⟧ tx′
  → ∃ λ s′ → TxS tx′ s′ × (s ↝ s′)
h {tx = tx}{tx′}{s} (record {s∈ = v , outs≡}) tx∈ tx↝
  with txIn , o , txIn∈ , o∈ , ◆∈v , getSpent≡ ← hh {tx = tx}{tx′} tx↝ tx∈
  = qed
  where
    open ≡-Reasoning

    l = proj₁ $ ∈⇒Suffix tx∈

    vtx : IsValidTx tx′ l
    vtx = tx∈⇒valid {L = L} tx∈

    o∈◆ : o ∈ outputs◆ tx
    o∈◆ = ∈-filter⁺ (◆∈?_ ∘ value) o∈ ◆∈v

    o≡ : o ≡ record {value = v; address = 𝕍; datumHash = toData s ♯ᵈ}
    o≡ with here eq ← subst (o ∈_) outs≡ o∈◆ = eq

    vi = validator txIn
    ri = redeemer txIn
    di = datum txIn
    ds = toData s
    ptx = toPendingTx l tx′ (L.Any.index txIn∈)

    aiv : All (λ{ (n , i) → T (validator i (toPendingTx l tx′ n) (redeemer i) (datum i))})
              (enumerate $ inputs tx′)
    aiv = allInputsValidate vtx

    aiv′ : T $ vi ptx ri di
    aiv′ = L.All.lookup aiv (x∈→ix∈ txIn∈)

    vvh : All (λ i → M.Any.Any (λ o → (address o ≡ validator i ♯) × (datumHash o ≡ datum i ♯ᵈ)) (getSpentOutput l i))
              (inputs tx′)
    vvh = validateValidHashes vtx

    vvh′ : M.Any.Any (λ o → (address o ≡ vi ♯) × (datumHash o ≡ di ♯ᵈ)) (getSpentOutput l txIn)
    vvh′ = L.All.lookup vvh txIn∈

    vvh″ : (address o ≡ vi ♯) × (datumHash o ≡ di ♯ᵈ)
    vvh″ = Any-just {mx = getSpentOutput l txIn} getSpent≡ vvh′

    vi≡ : vi ≡ validatorₛₘ
    vi≡ = ♯-injective
        $ begin vi ♯      ≡⟨ sym (proj₁ vvh″) ⟩
                address o ≡⟨ cong address o≡ ⟩
                𝕍        ∎

    di≡ : di ≡ ds
    di≡ = injective♯ᵈ
        $ begin di ♯ᵈ       ≡⟨ sym (proj₂ vvh″) ⟩
                datumHash o ≡⟨ cong datumHash o≡ ⟩
                ds ♯ᵈ       ∎

    Tval : T (validatorₛₘ ptx ri ds)
    Tval = subst T (begin vi ptx ri di          ≡⟨ cong (λ x → x ptx ri di) vi≡ ⟩
                          validatorₛₘ ptx ri di ≡⟨ cong (validatorₛₘ ptx ri) di≡ ⟩
                          validatorₛₘ ptx ri ds ∎) aiv′

    qed : ∃ λ s′ → TxS tx′ s′ × (s ↝ s′)
    qed with i , s′ , tx≡ , s→s′ , outsOK , _ , prop  ← T-validator {di = ri}{s}{ptx} Tval
        with _ , vout≥                                ← T-propagates {ptx} prop
        with o′ , o′∈ , outs≡ , datum≡ , refl , addr≡ ← T-outputsOK {l}{tx′}{di}{ds}{s′}{txIn}{txIn∈} outsOK
      = s′ , record {tx∈ = tx∈; s∈ = value o′ , outs◆≡′} , i , tx≡ , s→s′
      where
        vout◆≥ : value o′ ◆ ≥ threadₛₘ ◆
        vout◆≥ = ≥ᶜ-◆ {x = value o′} {y = threadₛₘ} (true⇒T vout≥)

        ◆∈v′ : ◆∈ value o′
        ◆∈v′ = subst (value o′ ◆ ≥_) (◆-single {n = 1}) vout◆≥

        o′≡ : o′ ≡ record {value = value o′; address = 𝕍; datumHash = toData s′ ♯ᵈ}
        o′≡ rewrite addr≡ | vi≡ | datum≡ = refl

        o′∈outs◆ : o′ ∈ outputs◆ tx′
        o′∈outs◆ = ∈-filter⁺ (◆∈?_ ∘ value) o′∈ ◆∈v′

        outs◆≡ : outputs◆ tx′ ≡ [ o′ ]
        outs◆≡ = ams-∈ {x = o′} {xs = outputs◆ tx′} (ams-outputs◆ tx∈) o′∈outs◆

        outs◆≡′ : outputs◆ tx′ ≡ [ record {value = value o′; address = 𝕍; datumHash = toData s′ ♯ᵈ} ]
        outs◆≡′ = trans outs◆≡ (cong [_] o′≡)

data Xˢ : ∃TxS → ∃TxS → Set where

  root : ∀ {tx}

    → (tx∈ : tx ∈′ L)
    → (p≡ : T (policyₛₘ $ record {this = ℂ; txInfo = mkTxInfo (proj₁ $ ∈⇒Suffix tx∈) tx}))
      --------------------------------------------------------
    → let s , _ , txs = h₀ tx∈ p≡
      in  Xˢ (tx , s , txs) (tx , s , txs)

  cons : ∀ {txs₀ tx s tx′} {txs : TxS tx s}

    → Xˢ txs₀ (tx , s , txs)
    → (tx∈ : tx′ ∈′ L)
    → (tx↝ : tx ↝⟦ 1 ⟧ tx′)
      -----------------------------------
    → let s′ , txs′ , _ = h txs tx∈ tx↝
      in  Xˢ txs₀ (tx′ , s′ , txs′)


X¹→Xˢ : ∀ {tx tx′}
  → X¹ tx tx′
    -------------------------------------
  → ∃ λ s → ∃ λ s′ → ∃ λ txs → ∃ λ txs′ →
      Xˢ (tx , s , txs) (tx′ , s′ , txs′)
X¹→Xˢ {tx = tx} {.tx} (root .tx tx∈ p≡) =
  let s , _ , txs = h₀ tx∈ p≡
  in  _ , _ , _ , _ , root tx∈ p≡
X¹→Xˢ {tx = tx} {tx′} (cons x¹ tx∈ tx↝) =
  let _ , s , _ , txs , xˢ  = X¹→Xˢ x¹
      s′ , txs′ , _ = h txs tx∈ tx↝
  in  _ , _ , _ , _ , cons xˢ tx∈ tx↝

Xˢ→R : ∀ {tx s tx′ s′} {txs : TxS tx s} {txs′ : TxS tx′ s′}
  → Xˢ (_ , _ , txs) (_ , _ , txs′)
    -------------------------------
  → s ↝⋆ s′
Xˢ→R (root {tx = tx} tx∈ p≡) =
  let _ , init-s , _ = h₀ {tx = tx} tx∈ p≡
  in  root init-s
Xˢ→R (cons {txs = txs} x tx∈ tx↝) =
  let _ , _ , s→s′ = h txs tx∈ tx↝
  in  snoc (Xˢ→R x) s→s′

∃Xˢ = ∃[ tx ] ∃[ tx′ ] ∃[ s ] ∃[ s′ ] ∃[ txs ] ∃[ txs′ ] Xˢ (tx , s , txs) (tx′ , s′ , txs′)

module Extraction {tx o}
  (o∈  : o ∈ outputs tx)
  (jo  : Is-just originₛₘ)
  where

  source dest : ∃Xˢ → S
  source = proj₁ ∘ proj₂ ∘ proj₂
  dest   = proj₁ ∘ proj₂ ∘ proj₂ ∘ proj₂

  provenanceˢ :
      (tx∈ : tx ∈′ L)
    → (◆∈v : ◆∈ value o)
      ------------------
    → ∃Xˢ
  provenanceˢ tx∈ ◆∈v
    with l , l≺                ← ∈⇒Suffix tx∈
    with vl                    ← ≼⇒valid (proj₂ L) l≺
    with n , tr , _ , n>0 , p≡ ← initiality vl o∈ ◆∈v jo
     = _ , _ , X¹→Xˢ (X→X¹ n>0 tr′ p≡′)
    where
      tr′ : Trace L tx n
      tr′ = weakenTrace l≺ tr

      p≡′ : T (policyₛₘ $ mkPendingMPS {L = L} tr′ ℂ)
      p≡′ = subst (λ x → T (policyₛₘ $ toPendingMPS x (origin tr) ℂ)) (sym $ mps≡ {L = L} {_ , vl} l≺ tr) p≡
      -- rewrite mps≡ {L = L}{_ , vl} l≺ tr = p≡

  extract :
      (tx∈ : tx ∈′ L)
    → (◆∈v : ◆∈ value o)
    → let xˢ = provenanceˢ tx∈ ◆∈v in
    ---------------------------------
    source xˢ ↝⋆ dest xˢ
  extract tx∈ ◆∈v = let _ , _ , _ , _ , _ , _ , xˢ = provenanceˢ tx∈ ◆∈v
                    in  Xˢ→R xˢ
