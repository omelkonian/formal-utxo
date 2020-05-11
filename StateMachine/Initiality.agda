open import Level
open import Category.Monad using (RawMonad)
open import Function

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Bool using (T)
open import Data.Nat using (_≤_; _≥_; _>_; _+_)
  renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (+-identityˡ; +-identityʳ; <⇒≢; ≤⇒pred≤)

open import Data.Maybe using (Maybe; just; nothing; Is-just)
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List hiding (fromMaybe)
open import Data.List.NonEmpty as NE using (List⁺)
  renaming ([_] to [_]⁺)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (here; there)
open import Data.List.Relation.Binary.Pointwise using (≡⇒Pointwise-≡)

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Prelude.General
open import Prelude.Lists

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities
open import UTxO.Validity
open import StateMachine.Base

module StateMachine.Initiality
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open CEM {sm = sm}

nft : TokenClass
nft = ℂ , 𝕋

open FocusTokenClass nft
open import UTxO.TokenProvenance nft
open import UTxO.TokenProvenanceNF nft

◆∈⇒Tpolicy : ∀ {tx l}
  → IsValidTx tx l
  → ◆∈ forge tx
  → T (policyₛₘ $ toPendingMPS l tx ℂ)
◆∈⇒Tpolicy {tx} {l} vtx ◆∈ = policy≡
  where
    policy≡ : T (policyₛₘ $ toPendingMPS l tx ℂ)
    policy≡ = All.lookup (allPoliciesValidate vtx) $ ∈♯ $ All.lookup (forging vtx) $ ◆-currencies∈ ◆∈

module JustOrigin (just-origin : Is-just originₛₘ) where

  𝕆 : TxOutputRef
  𝕆 = proj₁ $ destruct-Is-just just-origin

  o∈ : ∀ {txi} → T (spentsOrigin txi) → 𝕆 ∈ map InputInfo.outputRef (TxInfo.inputInfo txi)
  o∈ p with originₛₘ
  ... | nothing = ⊥-elim $ Is-just⇒≢nothing just-origin refl
  ... | just _  = toWitness p

  frg◆≤1 : ∀ {tx} {l} → IsValidTx tx l → forge tx ◆ ≤ 1
  frg◆≤1 {tx} {l} vtx = ¬>⇒≤ ¬frg◆>1
    where
      ¬frg◆>1 : ¬ (forge tx ◆ > 1)
      ¬frg◆>1 frg◆>1 = <⇒≢ frg◆>1 (sym frg≡1)
        where
          ◆∈frg : ◆∈ forge tx
          ◆∈frg = ≤⇒pred≤ frg◆>1

          Tpolicy : T (policyₛₘ $ toPendingMPS l tx ℂ)
          Tpolicy = ◆∈⇒Tpolicy vtx ◆∈frg

          frg≡1 : forge tx ◆ ≡ 1
          frg≡1 = toWitness {Q = lookupQuantity (ℂ , 𝕋) (forge tx) ≟ℕ 1} (proj₁ $ T-∧ Tpolicy)

  ∃forging : ∀ {l}
    → ValidLedger l
    → ∑ l forge ◆ > 0
    → ∃ λ tx → ∃ λ l′ →
        ValidLedger (tx ∷ l′)
      × tx ∷ l′ ≼ l
      × (◆∈ forge tx)
  ∃forging {tx ∷ l} vl₀@(vl ⊕ .tx ∶- vtx) ∑>0
    rewrite +ᶜ-◆ {x = forge tx} {y = ∑ l forge}
    with ◆∈? forge tx
  ... | no  ◆∉ rewrite ¬x>0⇒x≡0 ◆∉ | +-identityˡ (∑ l forge ◆)
               with tx , l′ , vl′ , l′≺ , ◆∈ ← ∃forging vl ∑>0
                 = tx , l′ , vl′ , there l′≺ , ◆∈
  ... | yes ◆∈ = tx , l , vl₀ , here (≡⇒Pointwise-≡ refl) , ◆∈

  ∃forging² : ∀ {l}
    → ValidLedger l
    → ∑ l forge ◆ > 1
    → ∃ λ tx₁ → ∃ λ l₁ → ∃ λ tx₂ → ∃ λ l₂
        → ValidLedger (tx₁ ∷ l₁)
        × ValidLedger (tx₂ ∷ l₂)
        × tx₁ ∷ l₁ ≼ l₂
        × (◆∈ forge tx₁)
        × (◆∈ forge tx₂)
  ∃forging² {tx ∷ l} vl₀@(vl ⊕ .tx ∶- vtx) ∑>1
    rewrite +ᶜ-◆ {x = forge tx} {y = ∑ l forge}
    with ◆∈? forge tx
  ... | no  ◆∉
    rewrite ¬x>0⇒x≡0 ◆∉ | +-identityˡ (∑ l forge ◆) = ∃forging² vl ∑>1
  ... | yes ◆∈
    rewrite x>0,x≤1⇒x≡1 ◆∈ (frg◆≤1 vtx)
    with ∑>0 ← x+y>x⇒y>0 {x = 1} {y = ∑ l forge ◆} ∑>1
    with tx′ , l′ , vl′ , l′≺l , ◆∈′ ← ∃forging vl ∑>0
       = tx′ , l′ , tx , l , vl′ , vl₀ , l′≺l , ◆∈′ , ◆∈

  ◆∈⇒𝕆∈ : ∀ {tx l}
    → IsValidTx tx l
    → ◆∈ forge tx
    → 𝕆 ∈ outputRefs tx
  ◆∈⇒𝕆∈ {tx} {l} vtx ◆∈frg = outRef∈txi {tx}{l}{𝕆} $ o∈ {txi} Tspents
    where
      txi = mkTxInfo l tx

      Tpolicy : T (policyₛₘ $ toPendingMPS l tx ℂ)
      Tpolicy = ◆∈⇒Tpolicy vtx ◆∈frg

      Tspents : T (spentsOrigin txi)
      Tspents = proj₁ $ T-∧ {l = spentsOrigin txi} $ proj₂ $ T-∧ {l = ⌊ forge tx ◆ ≟ℕ 1 ⌋} Tpolicy

initiality : ∀ L → ∀ {o} (o∈ : o ∈ outputsₘ L)
  → (◆∈v : ◆∈ value o)
  → Is-just originₛₘ
    --------------------------------------------------------
  → Σ (∃ $ ForgingTx L) λ tx →
         (origins⁺ (provenance L o∈ ◆∈v) ≡ [ tx ]⁺)
       × T (policyₛₘ $ mkPendingMPS {L = L} (proj₂ tx) ℂ)
initiality L@(l , vl) {o} o∈ ◆∈v just-origin
  = ∃tx , prov≡ , policy≡
  where
    v    = value o
    prov = provenance L o∈ ◆∈v

--

    nf : NonFungible L nft
    nf = ¬>⇒≤ nf′
      where
        open JustOrigin just-origin

        nf′ : ¬ (∑ l forge ◆ > 1)
        nf′ ∑>1
          with tx₁ , l₁ , tx₂ , l₂
             , vl₁ ⊕ .tx₁ ∶- vtx₁ , vl₂ ⊕ .tx₂ ∶- vtx₂
             , l₁≺l₂ , ◆∈₁ , ◆∈₂
             ← ∃forging² vl ∑>1
          = o∉utxo₂ o∈utxo₂
          where
            o∈₁ : 𝕆 ∈ outputRefs tx₁
            o∈₁ = ◆∈⇒𝕆∈ vtx₁ ◆∈₁

            o∈utxo₁ : 𝕆 ∈ map outRef (utxo l₁)
            o∈utxo₁ = validOutputRefs vtx₁ o∈₁

            o∉utxo₂ : 𝕆 ∉ map outRef (utxo l₂)
            o∉utxo₂ = suf-utxo vl₂ l₁≺l₂ o∈utxo₁ o∈₁

            o∈₂ : 𝕆 ∈ outputRefs tx₂
            o∈₂ = ◆∈⇒𝕆∈ vtx₂ ◆∈₂

            o∈utxo₂ : 𝕆 ∈ map outRef (utxo l₂)
            o∈utxo₂ = validOutputRefs vtx₂ o∈₂

    nfp : SingleOrigin⁺ prov
    nfp = provenanceNF L {o} o∈ ◆∈v nf

--
    des-nfp : ∃ λ ∃tx → origins⁺ prov ≡ [ ∃tx ]⁺
    des-nfp = destruct-SingleOrigin⁺ {os = prov} nfp

    ∃tx : ∃ $ ForgingTx L
    ∃tx = proj₁ des-nfp

    prov≡ : origins⁺ prov ≡ [ ∃tx ]⁺
    prov≡ = proj₂ des-nfp

    n : Quantity
    n = proj₁ ∃tx

    ∑≥ : ∑₁⁺ (origins⁺ prov) ≥ v ◆
    ∑≥ = sums⁺ prov

    ∑≥′ : ∑₁⁺ [ ∃tx ]⁺ ≥ v ◆
    ∑≥′ = subst (λ x → ∑₁⁺ x ≥ v ◆) prov≡ ∑≥

    n≥ : n ≥ v ◆
    n≥ = subst (_≥ v ◆) (+-identityʳ n) ∑≥′

    frgTx : ForgingTx L n
    frgTx = proj₂ ∃tx

    tx₀ : Tx
    tx₀ = proj₁ frgTx

    frg≥ : forge tx₀ ◆ ≥ n
    frg≥ = proj₁ $ proj₂ frgTx

    tx₀∈ : tx₀ ∈′ L
    tx₀∈ = proj₂ $ proj₂ frgTx

    ◆∈frg : ◆∈ (forge tx₀)
    ◆∈frg = ◆-≥ {v = forge tx₀} {v′ = v} (≥-trans frg≥ n≥) ◆∈v

    policy≡ : T (policyₛₘ $ mkPendingMPS {L = L} frgTx ℂ)
    policy≡ with l₀ , l₀≼      ← ∈⇒Suffix tx₀∈
            with _ ⊕ _ ∶- vtx₀ ← valid-suffix vl l₀≼
               = ◆∈⇒Tpolicy {tx = tx₀} {l = l₀} vtx₀ ◆∈frg
