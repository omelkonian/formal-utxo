module UTxO.Tracing where

open import Level          using (0ℓ)
open import Function       using (_$_)
open import Category.Monad using (RawMonad)

open import Data.Product       using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Data.Bool          using (T; if_then_else_)
open import Data.List          using (List; []; _∷_; [_]; _++_; map; concat)
open import Data.List.NonEmpty using (List⁺; _∷_; head)
open import Data.Maybe         using (Maybe; just; nothing)

open import Data.Bool.Properties using (T?)

import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List.Membership.Propositional            using (_∈_; mapWith∈)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁻; ∈-filter⁻)
import Data.List.Relation.Unary.All as All

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities hiding (prevTx)
open import UTxO.Validity

_-forges-_ : Tx → Value → Set
tx -forges- v = T (forge tx ≥ᶜ v)

-- T0D0: add ledger
Trace : TxOutput → Set
Trace o = Σ[ tr ∈ List⁺ Tx ] (head tr -forges- value o)

weakenTr : ∀ {o o′}
  → T (value o ≥ᶜ value o′)
  → Trace o
  → Trace o′
weakenTr {o} {o′} p (tr , frg) = tr , ≥ᶜ-trans {x = forge (head tr)} {y = value o} {z = value o′} frg p

getValidOutputs : ∀ {tx l}
  → ValidLedger (tx ∷ l)
  → ∀ i → i ∈ inputs tx →
      ∃[ prevTx ] ∃[ prevOut ]
        ( (prevOut ∈ outputs prevTx)
        × (getSpentOutput l i ≡ just prevOut)
        × ∃[ l′ ] ( Suffix≡ (prevTx ∷ l′) l
                  × ValidLedger (prevTx ∷ l′)
                  )
        )
getValidOutputs {l = l} (vl ⊕ tx ∶- vtx) i i∈
  with ∈-map⁻ outRef (All.lookup (validOutputRefs vtx) i∈)
... | u@(record {prevTx = prevTx; out = prevOut@(record {value = v})}) , out∈ , i≡
  with utxo-getSpent {l} {u}
... | spent≡
  = prevTx , prevOut , prevOut∈ , getSpent≡ , l′ , suf-l′ , vl′
  where
    prevOut∈ : prevOut ∈ outputs prevTx
    prevOut∈ = {! !}

    getSpent≡ : getSpentOutput l i ≡ just prevOut
    getSpent≡ = {!!}

    l′ : Ledger
    l′ = {!!}

    suf-l′ : Suffix≡ (prevTx ∷ l′) l
    suf-l′ = {!!}

    vl′ : ValidLedger (prevTx ∷ l′)
    vl′ = {!!} ⊕ {!!} ∶- {!!}


{-# NON_TERMINATING #-}
-- {-# TERMINATING #-}
history : ∀ {tx l} {vl : ValidLedger (tx ∷ l)} →
  ∀ o → o ∈ outputs tx →
    List (Trace o)
history {tx} {l} {vl₀@(vl ⊕ tx ∶- vtx)} o@(record {value = v}) o∈ = fromForge ++ prevHistory
  where
    fromForge : List (Trace o)
    fromForge
      with T? (forge tx ≥ᶜ v)
    ... | yes p = [ tx ∷ [] , p ]
    ... | no ¬p = []

    prevHistory : List (Trace o)
    prevHistory = concat $ mapWith∈ (inputs tx) go
      where
        go : ∀ {i} → i ∈ inputs tx → List (Trace o)
        go {i} i∈
          with getValidOutputs vl₀ i i∈
        ... | prevTx , prevOut , prevOut∈ , getSpent≡ , l′ , _ , vl′
          with T? (value prevOut ≥ᶜ v)
        ... | yes p = map (weakenTr {o = prevOut} {o′ = o} p)
                          (history {tx = prevTx} {l = l′} {vl = vl′} prevOut prevOut∈)
        ... | no  _ = []


{-
NonFungible : MonetaryPolicy → Set

nf-history : ∀ {tx l} {vl : ValidLedger (tx ∷ l)} →
    ∀ o → o ∈ outputs tx →
      length (history {vl = vl} o o∈) ≡ 1
-}
