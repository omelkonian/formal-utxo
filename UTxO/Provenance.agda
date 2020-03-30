module UTxO.Provenance where

open import Level          using (0ℓ)
open import Function       using (_$_; _∘_)
open import Category.Monad using (RawMonad)

open import Data.Product       using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Data.Bool          using (T; if_then_else_)
open import Data.List          using (List; []; _∷_; [_]; _++_; map; concat; _∷ʳ_)
open import Data.List.NonEmpty using (List⁺; _∷_; head; toList; _++⁺_)
open import Data.Maybe         using (Maybe; just; nothing)
open import Data.Fin           using (toℕ)

open import Data.Bool.Properties using (T?)

import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List.Membership.Propositional             using (_∈_; mapWith∈)
open import Data.List.Membership.Propositional.Properties  using (∈-map⁻; ∈-++⁻; ∈-filter⁻; ∈-map⁺)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any as Any            using (Any; here; there)
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (here; there)
open import Data.List.Relation.Binary.Pointwise            using (Pointwise-≡⇒≡)


open import Relation.Nullary                      using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities
open import UTxO.Validity

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

weakenLinked : ∀ {txs v v′}
  → T (v ≥ᶜ v′)
  → Linked v txs
  → Linked v′ txs
weakenLinked {v = v} {v′ = v′} p′ (∙ tx ∶- p)
  = ∙ tx ∶- ≥ᶜ-trans {x = forge tx} {y = v} {z = v′} p p′
weakenLinked {v = v} {v′ = v′} p′ (txs ⊕ tx ∶- (o∈ , o , ⁉≡ , p))
  = weakenLinked p′ txs ⊕ tx ∶- (o∈ , o , ⁉≡ , ≥ᶜ-trans {x = value o} {y = v} {z = v′} p p′)

record Trace (o : TxOutput) : Set where
  field
    origin  : Tx      -- ^ forging transaction
    trace   : List Tx -- ^ rest of the trace
    linked  : Linked (value o) (trace ++⁺ (origin ∷ []))

open Trace public

singletonTrace : ∀ {o} → (tx : Tx) → T (forge tx ≥ᶜ value o) → Trace o
singletonTrace tx p = record {origin = tx; trace = []; linked = ∙ tx ∶- p}

weakenTr : ∀ {o o′}
    → T (value o ≥ᶜ value o′)
    → Trace o
    → Trace o′
weakenTr {o} {o′} p tr = record { origin = origin tr ; trace = trace tr ; linked = weakenLinked p (linked tr) }

{-# NON_TERMINATING #-}
-- {-# TERMINATING #-}
history : ∀ {tx l} {vl : ValidLedger (tx ∷ l)} →
  ∀ o → o ∈ outputs tx →
    List (Trace o)
history {tx} {l} {vl₀@(vl ⊕ tx ∶- vtx)} o@(record {value = v}) o∈ = fromForge ++ prevHistory
  where
    valid-suffix : ∀ {l l′}
      → ValidLedger l
      → Suffix≡ l′ l
      → ValidLedger l′
    valid-suffix vl            (here eq)   rewrite Pointwise-≡⇒≡ eq = vl
    valid-suffix (vl ⊕ t ∶- x) (there suf) = valid-suffix vl suf

    getValidOutputs : ∀ {tx l}
      → ValidLedger (tx ∷ l)
      → ∀ i → i ∈ inputs tx →
          ∃[ prevTx ] ∃[ prevOut ]
            ( (prevOut ∈ outputs prevTx)
            × (getSpentOutput l i ≡ just prevOut)
            × ∃[ l′ ] Suffix≡ (prevTx ∷ l′) l )

    getValidOutputs {l = l} (vl ⊕ tx ∶- vtx) i i∈
      with ∈-map⁻ outRef (validOutputRefs vtx (∈-map⁺ outputRef i∈))
    ... | u , u∈ , refl
      with ∈utxo⇒outRef≡ {l = l} u∈
    ... | prev∈ , prevOut∈ , refl
        = prevTx u , out u , prevOut∈ , utxo-getSpent {l = l} u∈ , ∈⇒Suffix prev∈

    fromForge : List (Trace o)
    fromForge
      with T? (forge tx ≥ᶜ v)
    ... | yes p = [ singletonTrace tx p ]
    ... | no ¬p = []

    prevHistory : List (Trace o)
    prevHistory = concat $ mapWith∈ (inputs tx) go
      where
        go : ∀ {i} → i ∈ inputs tx → List (Trace o)
        go {i} i∈
          with getValidOutputs vl₀ i i∈
        ... | prevTx , prevOut , prevOut∈ , getSpent≡ , l′ , suf
          with T? (value prevOut ≥ᶜ v)
        ... | yes p = map (weakenTr {o = prevOut} {o′ = o} p)
                          (history {tx = prevTx} {l = l′} {vl = valid-suffix vl suf} prevOut prevOut∈)
        ... | no  _ = []



{-
NonFungible : MonetaryPolicy → Set

nf-history : ∀ {tx l} {vl : ValidLedger (tx ∷ l)} →
    ∀ o → o ∈ outputs tx →
      length (history {vl = vl} o o∈) ≡ 1
-}
