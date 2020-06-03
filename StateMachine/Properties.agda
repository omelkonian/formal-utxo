open import Level    using (0ℓ)
open import Function using (_∘_; case_of_; _$_)

open import Category.Monad using (RawMonad)

open import Data.Empty   using (⊥-elim)
open import Data.Unit    using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax;Σ)
  renaming (map to map₁₂)
open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_; T)
open import Data.Maybe   using (Maybe; just; nothing; fromMaybe; maybe′)
open import Data.List    using (List; null; []; _∷_; [_]; filter; map; length; and)
open import Data.Nat     using (ℕ)
  renaming (_≟_ to _≟ℕ_)
open import Data.Sum using (_⊎_)

open import Data.Maybe.Properties  using (just-injective)
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List.Membership.Propositional            using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-filter⁻)
open import Data.List.Relation.Unary.Any as Any           using (here)

open import Relation.Nullary                      using (yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; inspect; trans; sym; cong; subst)
  renaming ([_] to ≡[_])

open import Prelude.General
open import Prelude.Lists using (enumerate)

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
T-propagates {ptx} eq = map₁₂ T⇒true T⇒true (T-∧ $ true⇒T eq)

T-outputsOK : ∀ {l tx di ds s′} {txIn : TxInput} {txIn∈ : txIn ∈ inputs tx}
  → let ptx = toPendingTx l tx (Any.index txIn∈) in
    outputsOK ptx di ds s′ ≡ true
    --------------------------------
  → ∃[ o ] ( (o ∈ outputs tx)
           × (getContinuingOutputs ptx ≡ [ o ])
           × (datumHash o ≡ toData s′ ♯ᵈ)
           × (value o ≡ valueAtᵒ (thisValidator ptx) (txInfo ptx))
           × (address o ≡ validator txIn ♯)
           )
T-outputsOK {l} {tx} {di} {ds} {s′} {txIn} {txIn∈} eq
  with getContinuingOutputs (toPendingTx l tx (Any.index txIn∈))
     | inspect getContinuingOutputs (toPendingTx l tx (Any.index txIn∈))
... | (o ∷ []) | ≡[ out≡ ]
  rewrite ptx-‼ {l = l} {tx = tx} {i∈ = txIn∈}
  with ∈-filter⁻ (((validator txIn) ♯ ≟ℕ_) ∘ address)
                  {v = o} {xs = outputs tx} (singleton→∈ (_ , out≡))
... | o∈ , refl
  with datumHash o ≟ℕ toData s′ ♯ᵈ | eq
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
