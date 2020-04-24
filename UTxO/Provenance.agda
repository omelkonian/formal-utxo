module UTxO.Provenance where

open import Level          using (0ℓ)
open import Function       using (_$_; _∘_; flip)
open import Category.Monad using (RawMonad)

open import Induction.WellFounded using (Acc; acc)

open import Data.Empty               using (⊥-elim)
open import Data.Product             using (_×_; _,_; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂; map₁; map₂)
open import Data.Sum                 using (_⊎_; inj₁; inj₂)
open import Data.Bool                using (T; if_then_else_)
open import Data.List                using (List; []; _∷_; [_]; _++_; map; concat; _∷ʳ_; foldr; filter; concatMap)
open import Data.List.NonEmpty as NE using (List⁺; _∷_; head; toList; _++⁺_; _∷⁺_)
open import Data.Maybe               using (Maybe; just; nothing)
open import Data.Fin                 using (toℕ)


open import Data.Bool.Properties using (T?)

import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List.Properties                           using (map-compose; ∷-injective)
open import Data.List.Membership.Propositional             using (_∈_; mapWith∈)
open import Data.List.Membership.Propositional.Properties  using (∈-map⁻; ∈-++⁻; ∈-filter⁻; ∈-map⁺)
open import Data.List.Relation.Unary.All as All            using (All; []; _∷_; tabulate)
open import Data.List.Relation.Unary.Any as Any            using (Any; here; there)
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (here; there)
open import Data.List.Relation.Binary.Pointwise            using (_∷_; Pointwise-≡⇒≡)

open import Relation.Nullary                            using (yes; no)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; sym; subst; cong; trans; inspect)
  renaming ([_] to ≡[_])
open Eq.≡-Reasoning

open import Prelude.Lists

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities
open import UTxO.Validity

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
sums     (singletonTrace tx) rewrite +ᶜ-identityʳ (forge tx) = ≥ᶜ-refl (forge tx)

emptyTrace : ∀ {v} → v ≡ $0 → Trace v
emptyTrace refl = record {branches = []; sums = ≥ᶜ-refl $0}

weakenTrace : ∀ {v v′} → T $ v ≥ᶜ v′ → Trace v → Trace v′
weakenTrace {v} {v′} v≥v′ tr = record
  { branches = branches tr
  ; sums     = ≥ᶜ-trans {x = ∑₁ (branches tr)} {y = v} {z = v′} (sums tr) v≥v′ }

---------------
-- Provenance

combine : ∀ {v}
  → (hs : Histories)
  → T (∑₁ hs ≥ᶜ v)
  → List (Trace v)
combine {v} []                  ∑≥ = [ emptyTrace ($0-≥ᶜ v ∑≥) ]
combine {v} ((hᵥ , h) ∷ hs) ∑≥
    = concatMap (λ tr → map (tr ∷ᵗ_) $ combine {v = ∑₁ hs} hs (≥ᶜ-refl $ ∑₁ hs)) (toList h)
  module M₀ where
    _∷ᵗ_ : Trace hᵥ → Trace (∑₁ hs) → Trace v
    tr ∷ᵗ tr′ = record
      { branches = branches tr ++ branches tr′
      ; sums     = ≥ᶜ-trans {x = ∑₁ (branches tr ++ branches tr′)} {y = ∑₁ $ (_ , h) ∷ hs} {z = v}
                            (∑-++-≥ᶜ {fv = proj₁} {v₁ = hᵥ} {v₂ = ∑₁ hs} {xs = branches tr} {ys = branches tr′}
                                     (sums tr) (sums tr′)) ∑≥
      }

combine≢[] : ∀ {v} {hs : Histories} {∑≥ : T (∑₁ hs ≥ᶜ v)} → ¬Null (combine {v} hs ∑≥)
combine≢[] {v} {hs = (hᵥ , h) ∷ hs} {∑≥}
  = concat≢[] {xss = map (λ tr → map _ _) (toList h)}
              (_ , here refl , map≢[] (combine≢[] {∑₁ hs} {hs} {≥ᶜ-refl $ ∑₁ hs}))

history : ∀ l → ∀ {o} → o ∈ outputsₘ l → History (value o)
history l = go l (≺′-wf l)
 module M₁ where
  go : ∀ l → Acc _≺′_ l → (∀ {o} → o ∈ outputsₘ l → History (value o))
  go (.tx ∷ l , vl₀@(vl ⊕ tx ∶- vtx)) (acc a) {o} o∈
    = toList⁺ traces traces≢[]
   module M₂ where
    v = value o

    forgeHistory : ∃ History
    forgeHistory = forge tx , NE.[ singletonTrace tx ]

    rs = prevs vl vtx

    res→history : Res vl vtx → ∃ History
    res→history record {vl′ = vl′; prevOut∈ = prevOut∈; vl′≺vl = vl′≺vl}
              = _ , go (_ , vl′) (a _ vl′≺vl) prevOut∈

    prevHistories : Histories
    prevHistories = map res→history rs

    ∑prev = ∑₁ prevHistories

    allPrevs₀ : Histories
    allPrevs₀ = forgeHistory ∷ prevHistories

    allPrevs : Histories
    allPrevs = filter ((_-contributesTo?- v) ∘ proj₁) allPrevs₀

    choices : Choices
    choices = subsequences allPrevs

    validChoices : Choices
    validChoices = filter (λ hs → T? $ ∑₁ hs ≥ᶜ v) choices

    ∑≥ : ∀ {hs} → hs ∈ validChoices → T (∑₁ hs ≥ᶜ v)
    ∑≥ = proj₂ ∘ ∈-filter⁻ (λ hs → T? $ ∑₁ hs ≥ᶜ v) {xs = choices}

    traces : List (Trace v)
    traces = concat $ mapWith∈ validChoices λ {hs} hs∈ → combine hs (∑≥ hs∈)

  --

    proj₁-ap≡ : forge tx ∷ map resValue rs ≡ map proj₁ allPrevs₀
    proj₁-ap≡ rewrite map-compose {g = proj₁} {f = res→history} rs = refl

    res≡ : ∑ rs resValue ≡ ∑prev
    res≡ = cong sumᶜ $ proj₂ (∷-injective proj₁-ap≡)

    lookupOutputs≡′ : ∑M (map (getSpentOutput l) (inputs tx)) value ≡ just ∑prev
    lookupOutputs≡′ = trans (∑prevs≡ vl vtx) $ cong just res≡

    pv₀ : forge tx +ᶜ ∑prev ≡ fee tx +ᶜ ∑ᵥ (outputs tx)
    pv₀ = ∑M≡just lookupOutputs≡′ (preservesValues vtx)

    pv₁ : T $ forge tx +ᶜ ∑prev ≥ᶜ ∑ᵥ (outputs tx)
    pv₁ = +ᶜ-≡⇒≥ᶜ {x = forge tx} {y = ∑prev} {z = fee tx} {w = ∑ᵥ (outputs tx)} (≥ᶜ-refl′ pv₀)

    pv₂ : T $ forge tx +ᶜ ∑prev ≥ᶜ v
       -- T $ ∑₁ allPrevs₀ ≥ᶜ v
    pv₂ = ≥ᶜ-trans {x = ∑₁ allPrevs₀} {y = ∑ᵥ (outputs tx)} {z = v} pv₁ (∑-≥ᶜ {fv = value} o∈)

    pv₃ : T $ ∑₁ allPrevs ≥ᶜ v
       -- T $ ∑₁ (filter ((_-contributesTo?- v) ∘ proj₁) allPrevs₀) ≥ᶜ v
    pv₃ = ∑filter {xs = allPrevs₀} {v = v} pv₂

    validChoices≢[] : ¬Null validChoices
    validChoices≢[] vc≡[] = All.lookup (filter≡[] {P = λ hs → T $ ∑₁ hs ≥ᶜ v} vc≡[])
                                       (subsequences-refl {xs = allPrevs})
                                       pv₃

    traces≢[] : ¬Null traces
    traces≢[] tr≡[]
        = ∀mapWith∈≡[] {f = λ {hs} hs∈ → combine {v} hs (∑≥ hs∈)}
                       (λ {hs} hs∈ → combine≢[] {hs = hs} {∑≥ = ∑≥ hs∈})
                       validChoices≢[]
                       (concat≡[] {xss = mapWith∈ validChoices λ {hs} → combine {v} hs ∘ ∑≥} tr≡[])
