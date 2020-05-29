open import Level
open import Category.Monad using (RawMonad)
open import Function

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Bool using (Bool; T; true; false)
open import Data.Nat
  renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties
open ≤-Reasoning

open import Data.Maybe using (Maybe; just; nothing; Is-just; fromMaybe)
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List hiding (fromMaybe)
open import Data.List.NonEmpty using (List⁺; _∷_; toList; _⁺++_; _++⁺_; _∷⁺_; _∷ʳ_; last)
  renaming ([_] to [_]⁺; map to map⁺; head to head⁺)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (here; there)
open import Data.List.Relation.Binary.Pointwise using (≡⇒Pointwise-≡)

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality renaming ([_] to ≡[_])

open import Prelude.General
open import Prelude.Lists

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
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
               n + 0     ≡⟨ +-identityʳ n ⟩
               n ∎

    n>0 : n > 0
    n>0 = ≤-trans ◆∈v v≤

    frg≥ : forge tx₀ ◆ ≥ value o ◆
    frg≥ = ≤-trans v≤ (forge◆≥ $ linked tr)

    ◆∈frg : ◆∈ forge tx₀
    ◆∈frg = ◆-≥ {v = forge tx₀} {v′ = value o} frg≥ ◆∈v

    policy≡ : T (policyₛₘ $ mkPendingMPS {L = _ , vl} tr ℂ)
    policy≡ = ◆∈⇒Tpolicy {tx = tx₀} {l = l₀} vtx₀ ◆∈frg
