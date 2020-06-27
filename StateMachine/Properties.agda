open import Data.List.Membership.Propositional.Properties using (∈-filter⁻)

open import Prelude.Init
open import Prelude.General
open import Prelude.Lists using (enumerate)
open import Prelude.DecEq
open import Prelude.Bifunctor
open import Prelude.Monad

open import UTxO.Hashing
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities
open import UTxO.Validity
open import StateMachine.Base

module StateMachine.Properties
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open CEM {sm = sm}

T-propagates : ∀ {ptx}
  → propagates threadₛₘ ptx ≡ true
    ------------------------------
  → ((valueAtⁱ (thisValidator ptx) (txInfo ptx) ≥ᶜ threadₛₘ) ≡ true)
  × ((valueAtᵒ (thisValidator ptx) (txInfo ptx) ≥ᶜ threadₛₘ) ≡ true)
T-propagates {ptx} eq = bimap T⇒true T⇒true (T-∧ $ true⇒T eq)

T-outputsOK : ∀ {l tx di ds s′} {txIn : TxInput} {txIn∈ : txIn ∈ inputs tx}
  → let ptx = toPendingTx l tx (L.Any.index txIn∈) in
    outputsOK ptx di ds s′ ≡ true
    --------------------------------
  → ∃[ o ] ( (o ∈ outputs tx)
           × (getContinuingOutputs ptx ≡ [ o ])
           × (datumHash o ≡ toData s′ ♯ᵈ)
           × (value o ≡ valueAtᵒ (thisValidator ptx) (txInfo ptx))
           × (address o ≡ validator txIn ♯)
           )
T-outputsOK {l} {tx} {di} {ds} {s′} {txIn} {txIn∈} eq
  with getContinuingOutputs (toPendingTx l tx (L.Any.index txIn∈))
     | inspect getContinuingOutputs (toPendingTx l tx (L.Any.index txIn∈))
... | (o ∷ []) | ≡[ out≡ ]
  rewrite ptx-‼ {l = l} {tx = tx} {i∈ = txIn∈}
  with ∈-filter⁻ (((validator txIn) ♯ ≟_) ∘ address)
                  {v = o} {xs = outputs tx} (singleton→∈ (_ , out≡))
... | o∈ , refl
  with datumHash o ≟ toData s′ ♯ᵈ | eq
... | no ¬p    | ()
... | yes refl | _
    = o , o∈ , refl , refl , sym (sum-single {v = value o}) , refl

T-validator : ∀ {di s ptx} →
  let
    ds   = toData s
    txi  = txInfo ptx
    outs = getContinuingOutputs ptx
  in
    T (validatorₛₘ ptx di ds)
    ----------------------------------
  → ∃[ i ] ∃[ s′ ] ∃[ tx≡ ]
      ( (stepₛₘ s i ≡ pure (s′ , tx≡))
      × (outputsOK ptx di ds s′ ≡ true)
      × (verifyTxInfo txi tx≡ ≡ true)
      × (propagates threadₛₘ ptx ≡ true)
      )
T-validator {di} {s} {ptx} eq
  rewrite from∘to s
  with ⦇ stepₛₘ (pure s) (fromData di) ⦈
      | inspect (λ x → ⦇ stepₛₘ (pure s) x ⦈) (fromData di)
      | eq
... | nothing | _        | ()
... | just r  | ≡[ eq′ ] | _
  with fromData {A = I} di
... | nothing = ⊥-elim (ap-nothing {m = maybe′ (pure ∘ stepₛₘ) nothing (pure s)} eq′)
... | just i
  with stepₛₘ s i | inspect (stepₛₘ s) i | eq
... | nothing         | _          | ()
... | just (s′ , tx≡) | ≡[ step≡ ] | _
  rewrite step≡
  with outputsOK ptx di (toData s) s′ | inspect (outputsOK ptx di (toData s)) s′ | eq
... | false | _            | ()
... | true  | ≡[ outsOK≡ ] | _
  rewrite outsOK≡
  with verifyTxInfo (txInfo ptx) tx≡ | inspect (verifyTxInfo (txInfo ptx)) tx≡ | eq
... | false | _            | ()
... | true  | ≡[ verify≡ ] | _
  rewrite verify≡
  with propagates threadₛₘ ptx | eq
... | false | ()
... | true  | _
    = i , s′ , tx≡ , step≡ , outsOK≡ , verify≡ , refl
