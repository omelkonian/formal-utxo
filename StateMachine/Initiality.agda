open import Prelude.Init
open import Prelude.General
open import Prelude.Lists
open import Prelude.Membership
open import Prelude.Ord

open import UTxO.Hashing
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities
open import UTxO.Validity
open import StateMachine.Base hiding (origin)

module StateMachine.Initiality
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open CEM {sm = sm}

open FocusTokenClass nftₛₘ
open import UTxO.TokenProvenance nftₛₘ
open import UTxO.TokenProvenanceNF nftₛₘ

initiality : ∀ {tx l} (vl : ValidLedger (tx ∷ l)) {o} (o∈ : o ∈ outputs tx)
  → (◆∈v : ◆∈ value o)
  → Is-just originₛₘ
    ---------------------------------------------
  → ∃ λ n → Σ[ tr ∈ Trace (_ , vl) tx n ]
        (traces (provenance vl o∈) ≡ [ n , tr ])
      × (n > 0)
      × T (policyₛₘ $ mkPendingMPS {L = _ , vl} tr ℂ)
initiality {tx}{l} vl {o} o∈ ◆∈v jo
  with provenance vl o∈ | provenanceNF vl o∈ ◆∈v (JustOrigin.nf jo (_ , vl))
... | record {traces = (n , tr) ∷ []; sums = ∑≥} | refl
  = n , tr , refl , n>0 , policy≡
  where
    tx₀ = origin tr
    l₀ = proj₁ $ ∈⇒Suffix (origin∈ tr)

    vtx₀ : IsValidTx tx₀ l₀
    vtx₀ with _ ⊕ _ ∶- vtx₀ ← ≼⇒valid vl (proj₂ $ ∈⇒Suffix (origin∈ tr)) = vtx₀

    v≤ : value o ◆ ≤ n
    v≤ = begin value o ◆ ≤⟨ ∑≥ ⟩
               n + 0     ≡⟨ Nat.+-identityʳ n ⟩
               n ∎
         where open ≤-Reasoning

    n>0 : n > 0
    n>0 = Nat.≤-trans ◆∈v v≤

    frg≥ : forge tx₀ ◆ ≥ value o ◆
    frg≥ = Nat.≤-trans v≤ (forge◆≥ $ linked tr)

    ◆∈frg : ◆∈ forge tx₀
    ◆∈frg = ◆-≥ {v = forge tx₀} {v′ = value o} frg≥ ◆∈v

    policy≡ : T (policyₛₘ $ mkPendingMPS {L = _ , vl} tr ℂ)
    policy≡ = ◆∈⇒Tpolicy {tx = tx₀} {l = l₀} vtx₀ ◆∈frg
