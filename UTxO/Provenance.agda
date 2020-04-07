module UTxO.Provenance where

open import Level          using (0ℓ)
open import Function       using (_$_; _∘_; flip)
open import Category.Monad using (RawMonad)

open import Data.Empty               using (⊥-elim)
open import Data.Product             using (_×_; _,_; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum                 using (_⊎_; inj₁; inj₂)
open import Data.Bool                using (T; if_then_else_)
open import Data.List                using (List; []; _∷_; [_]; _++_; map; concat; _∷ʳ_; foldr; filter; concatMap)
open import Data.List.NonEmpty as NE using (List⁺; _∷_; head; toList; _++⁺_; _∷⁺_)
open import Data.Maybe               using (Maybe; just; nothing)
open import Data.Fin                 using (toℕ)

open import Data.Bool.Properties using (T?)

import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List.Membership.Propositional             using (_∈_; mapWith∈)
open import Data.List.Membership.Propositional.Properties  using (∈-map⁻; ∈-++⁻; ∈-filter⁻; ∈-map⁺)
open import Data.List.Relation.Unary.All as All            using (All; []; _∷_; tabulate)
open import Data.List.Relation.Unary.Any as Any            using (Any; here; there)
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (here; there)
open import Data.List.Relation.Binary.Pointwise            using (Pointwise-≡⇒≡)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; sym; subst; cong; module ≡-Reasoning)

open import Prelude.Lists

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities
open import UTxO.Validity

∑₁ : ∀ {H : Value → Set} → List (∃ H) → Value
∑₁ = flip ∑ proj₁

∑ᵥ : List TxOutput → Value
∑ᵥ = flip ∑ value

valid-suffix : ∀ {l l′}
  → ValidLedger l
  → Suffix≡ l′ l
  → ValidLedger l′
valid-suffix vl            (here eq)   rewrite Pointwise-≡⇒≡ eq = vl
valid-suffix (vl ⊕ t ∶- x) (there suf) = valid-suffix vl suf

---------------
-- Definitions

_↝⟦_⟧_ : Tx → Value → Tx → Set
tx ↝⟦ v ⟧ tx′ = Σ[ o∈ ∈ Any ((tx ♯ ≡_) ∘ id) (outputRefs tx′) ]
                  ∃[ o ] ( ((outputs tx ⁉ index (Any.lookup o∈)) ≡ just o)
                         × T (value o ≥ᶜ v) )

data Linked (v : Value) : List⁺ Tx → Set where
  ∙_∶-_ :

      (tx : Tx)
    → T (forge tx ≥ᶜ v)
      ------------------
    → Linked v (tx ∷ [])

  _⊕_∶-_ : ∀ {txs}

    → Linked v txs
    → (tx : Tx)
    → head txs ↝⟦ v ⟧ tx
      --------------------------
    → Linked v (tx ∷ toList txs)

record Branch (v : Value) : Set where
  field
    origin  : Tx      -- ^ forging transaction
    trace   : List Tx -- ^ rest of the trace
    linked  : Linked v (trace ++⁺ NE.[ origin ])

open Branch public

record Trace (v : Value) : Set where
  field
    branches : List (∃ Branch)
    sums     : T (∑₁ branches ≥ᶜ v)

open Trace public

Traces    = List $ ∃ Trace
History   = List⁺ ∘ Trace
Histories = List $ ∃ History
Choices   = List Histories

---------------
-- Utilities

singletonBranch : (tx : Tx) → Branch (forge tx)
singletonBranch tx = record
  { origin = tx
  ; trace  = []
  ; linked = ∙ tx ∶- ≥ᶜ-refl (forge tx) }

singletonTrace : (tx : Tx) → Trace (forge tx)
branches (singletonTrace tx) = [ _ , singletonBranch tx ]
sums     (singletonTrace tx) rewrite $0-identityʳ (forge tx) = ≥ᶜ-refl (forge tx)

emptyTrace : ∀ {v} → v ≡ $0 → Trace v
emptyTrace refl = record {branches = []; sums = ≥ᶜ-refl $0}

---------------
-- Provenance

combine : ∀ {v}
  → (hs : Histories)
  → T (∑₁ hs ≥ᶜ v)
  → List (Trace v)
combine {v} []                  ∑≥ = [ emptyTrace ($0-≥ᶜ v ∑≥) ]
combine {v} hs₀@((hᵥ , h) ∷ hs) ∑≥
  with combine {v = ∑₁ hs} hs (≥ᶜ-refl $ ∑₁ hs)
... | trs
    = concatMap (λ tr → map (tr ∷ᵗ_) trs) (toList h)
  where
    _∷ᵗ_ : Trace hᵥ → Trace (∑₁ hs) → Trace v
    tr ∷ᵗ tr′ = record
      { branches = branches tr ++ branches tr′
      ; sums     = ≥ᶜ-trans {x = ∑₁ (branches tr ++ branches tr′)} {y = ∑₁ hs₀} {z = v}
                            (∑-++-≥ᶜ {fv = proj₁} {v₁ = hᵥ} {v₂ = ∑₁ hs} {xs = branches tr} {ys = branches tr′}
                                     (sums tr) (sums tr′)) ∑≥
      }

combine≢[] : ∀ {v} {hs : Histories} {∑≥ : T (∑₁ hs ≥ᶜ v)} → ¬Null (combine {v} hs ∑≥)
combine≢[] {v} {hs = (hᵥ , h) ∷ hs} {∑≥}
  = concat≢[] {xss = map (λ tr → map _ _) (toList h)}
              (_ , here refl , map≢[] (combine≢[] {∑₁ hs} {hs} {≥ᶜ-refl $ ∑₁ hs}))

{-# NON_TERMINATING #-}
history : ∀ {tx l} {vl : ValidLedger (tx ∷ l)} →
  ∀ o → o ∈ outputs tx →
    History (value o)
history {tx} {l} {vl₀@(vl ⊕ tx ∶- vtx)} o@(record {value = v}) o∈ = toList⁺ traces traces≢[]
  where
    forgeHistory : History (forge tx)
    forgeHistory = NE.[ singletonTrace tx ]

    prevHistory′ : ∀ {i} → i ∈ inputs tx →
      ∃[ v ] ( History v
             × ((value <$> getSpentOutput l i) ≡ just v) )
    prevHistory′ {i} i∈
      with ∈-map⁻ outRef (validOutputRefs vtx (∈-map⁺ outputRef i∈))
    ... | u , u∈ , refl
      with ∈utxo⇒outRef≡ {l = l} u∈
    ... | prev∈ , prevOut∈ , refl
      with ∈⇒Suffix prev∈
    ... | l′ , suf
        = _ , history {tx = prevTx u} {l = l′} {vl = valid-suffix vl suf} (out u) prevOut∈
            , utxo-getSpentᵛ {l} {u} {i} u∈ refl

    prevHistory : ∀ {i} → i ∈ inputs tx → ∃ History
    prevHistory = drop₃ ∘ prevHistory′

    prevLookup :  ∀ {i} → i ∈ inputs tx → ∃[ v ] ((value <$> getSpentOutput l i) ≡ just v)
    prevLookup = drop₂ ∘ prevHistory′

    prevHistories : Histories
    prevHistories = mapWith∈ (inputs tx) prevHistory

    allPrevs : Histories
    allPrevs = (_ , forgeHistory) ∷ prevHistories

    lookupOutputs≡ : ∑M (map (getSpentOutput l) (inputs tx)) value ≡ just (∑₁ prevHistories)
    lookupOutputs≡ = ∑M-help prevHistory′

    pv′ : forge tx +ᶜ ∑₁ prevHistories ≡ fee tx +ᶜ ∑ᵥ (outputs tx)
    pv′ = ∑M≡just lookupOutputs≡ (preservesValues vtx)

    pv″ : T $ forge tx +ᶜ ∑₁ prevHistories ≥ᶜ ∑ᵥ (outputs tx)
    pv″ = +ᶜ-≡⇒≥ᶜ {x = forge tx} {y = ∑₁ prevHistories} {z = fee tx} {w = ∑ᵥ (outputs tx)} (≥ᶜ-refl′ pv′)

    pv‴ : T $ forge tx +ᶜ ∑₁ prevHistories ≥ᶜ v
    pv‴ = ≥ᶜ-trans {x = ∑₁ allPrevs} {y = ∑ᵥ (outputs tx)} {z = v} pv″ (∑-≥ᶜ {fv = value} o∈)

    choices : Choices
    choices = subsequences allPrevs

    validChoices : Choices
    validChoices = filter (λ hs → T? $ ∑₁ hs ≥ᶜ v) choices

    validChoices≢[] : ¬Null validChoices
    validChoices≢[] vc≡[] = All.lookup (filter≡[] {P = λ hs → T $ ∑₁ hs ≥ᶜ v} vc≡[])
                                       (subsequences-refl {xs = allPrevs})
                                       pv‴

    ∑≥ : ∀ {hs} → hs ∈ validChoices → T (∑₁ hs ≥ᶜ v)
    ∑≥ = proj₂ ∘ ∈-filter⁻ (λ hs → T? $ ∑₁ hs ≥ᶜ v) {xs = choices}

    traces : List (Trace v)
    traces = concat $ mapWith∈ validChoices λ {hs} → combine {v} hs ∘ ∑≥

    traces≢[] : ¬Null traces
    traces≢[] tr≡[]
        = ∀mapWith∈≡[] {f = λ {hs} → combine {v} hs ∘ ∑≥}
                       (λ {hs} hs∈ → combine≢[] {hs = hs} {∑≥ = ∑≥ hs∈})
                       validChoices≢[]
                       (concat≡[] {xss = mapWith∈ validChoices λ {hs} → combine {v} hs ∘ ∑≥} tr≡[])
