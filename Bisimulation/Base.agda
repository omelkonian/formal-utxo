open import Level          using (0ℓ)
open import Function       using (_∘_; case_of_; _$_)
open import Category.Monad using (RawMonad)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (Bool; T; true; false; if_then_else_; not)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Maybe   using (Maybe; just; nothing; fromMaybe; maybe)
open import Data.Fin     using (Fin; toℕ; fromℕ<)
  renaming (suc to fsuc; zero to fzero)
open import Data.Nat     using (ℕ; _<_; z≤n; s≤s; _+_; _≡ᵇ_)
  renaming (_≟_ to _≟ℕ_)
open import Data.List    using (List; []; _∷_; [_]; map; length; filter)

open import Data.Bool.Properties  using (T?)
  renaming (_≟_ to _≟𝔹_)
open import Data.Maybe.Properties using (just-injective)
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List.Relation.Unary.Any as Any           using (Any; here; there)
open import Data.List.Relation.Unary.AllPairs             using ([]; _∷_)
open import Data.List.Relation.Unary.All                  using (All; all; []; _∷_)
open import Data.List.Membership.Propositional            using (_∈_; _∉_; find; mapWith∈)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-map⁺; ∈-filter⁻)

open import Relation.Nullary.Decidable                  using (⌊_⌋; toWitness)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Prelude.General
open import Prelude.Lists

open import UTxO.Hashing
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities
open import UTxO.Validity
open import StateMachine.Base

open InputInfo

module Bisimulation.Base
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open CEM {sm = sm}

_—→[_]_ : S → I → (S × TxConstraints) → Set
s —→[ i ] (s′ , tx≡) = stepₛₘ s i ≡ just (s′ , tx≡)

infix 30 _—→[_∶-_]_
_—→[_∶-_]_ : ∀ {l} → ValidLedger l → (tx : Tx) → IsValidTx tx l → ValidLedger (tx ∷ l) → Set
vl —→[ tx ∶- vtx ] vl′ = vl′ ≡ vl ⊕ tx ∶- vtx

_~_ : ∀ {l} → ValidLedger l → S → Set
_~_ {l} _ s = (toData s) ♯ᵈ ∈ ( map (datumHash ∘ out)
                              ∘ filter ((_≟𝔹 true) ∘ (_≥ᶜ threadₛₘ) ∘ value ∘ out)
                              ∘ filter ((𝕍 ≟ℕ_) ∘ address ∘ out)
                              -- ∘ map out
                              ) (utxo l)

-- alternative definition (T0D0: replace everywhere)
-- _~′_ : ∀ {l} → ValidLedger l → S → Set
-- _~′_ {l} _ s = Any (λ o → (address o ≡ 𝕍) × (datumHash o ≡ toData s ♯ᵈ) × (nftₛₘ ∈ᶜ value o)) (map out $ utxo l)

view-~ : ∀ {l} {s : S} {vl : ValidLedger l}
  → vl ~ s
  → ∃[ prevTx ] ∃[ v ] (Σ[ prevOut∈ ∈ (s —→ v ∈ outputs prevTx) ]
      let
        oRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈)
        out  = record { address = 𝕍; datumHash = toData s ♯ᵈ; value = v }
        u    = record { prevTx = prevTx; out = out; outRef = oRef }
      in ( u ∈ utxo l
         × prevTx ∈ l
         × oRef ∈ map outRef (utxo l)
         × (getSpentOutputRef l oRef ≡ just out)
         × ((v ≥ᶜ threadₛₘ) ≡ true)
         ))
view-~ {l} {s} vl~s
  with ∈-map⁻ (datumHash ∘ out) vl~s
... | u@(record {prevTx = prevTx; out = record {value = v}}) , out∈ , refl
  with ∈-filter⁻ ((_≟𝔹 true) ∘ (_≥ᶜ threadₛₘ) ∘ value ∘ out) {xs = filter _ (utxo l)} out∈
... | u∈′ , threadToken≡
  with ∈-filter⁻ ((𝕍 ≟ℕ_) ∘ address ∘ out) {xs = utxo l} u∈′
... | u∈ , refl
  with ∈utxo⇒outRef≡ {u = u} {l = l} u∈
... | prev∈ , prevOut∈ , refl
    = prevTx , v , prevOut∈ , u∈ , prev∈ , ∈-map⁺ outRef u∈ , spent≡ , threadToken≡
  where
    oRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈)
    o    = record { address = 𝕍; datumHash = toData s ♯ᵈ; value = v }
    u′   = record { prevTx = prevTx; out = o; outRef = oRef }

    spent≡ : getSpentOutputRef l oRef ≡ just o
    spent≡ = utxo-getSpent {l = l} {u = u′} u∈

Satisfiable : ∀ {s l} {vl : ValidLedger l}
  → TxConstraints
  → vl ~ s
  → Set
Satisfiable {l = l} {vl} tx≡ vl~s
  with view-~ {vl = vl} vl~s
... | _ , v , _
    = (range≡ tx≡ >>=ₜ (_∋ length l) ≡ true)
    × (spent≥ tx≡ >>=ₜ (v ≥ᶜ_) ≡ true)
    × (∀ tx →
        All {A = MonetaryPolicy}
            (λ f → T (f (toPendingMPS l tx (f ♯))))
            (maybe (map proj₁) [] (forge≡ tx≡)))

mkTx : ∀ {l} {s s′ : S} {i : I} {vl : ValidLedger l} {vl~s : vl ~ s}
  → (tx≡ : TxConstraints)
  → Satisfiable {vl = vl} tx≡ vl~s
  → Σ[ tx ∈ Tx ] (verifyTx l tx tx≡ ≡ true)
mkTx {l} {s} {s′} {i} {vl} {vl~s} tx≡ (r≡ , s≥ , _)
  with view-~ {vl = vl} vl~s
... | prevTx , v , prevOut∈ , _ , _ , _ , getSpent≡ , _
    = tx , verify≡
    where
      frg = maybe toValue $0 (forge≡ tx≡)
      rng = fromMaybe (-∞ ⋯ +∞) (range≡ tx≡)
      plc = maybe (map proj₁) [] (forge≡ tx≡)

      i₀ = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈) ←— (i , s)

      tx = record { inputs   = [ i₀ ]
                  ; outputs  = [ s′ —→ (frg +ᶜ v) ]
                  ; policies = plc
                  ; forge    = frg
                  ; range    = rng
                  ; datumWitnesses = [ toData s′ ♯ᵈ , toData s′ ] }

      txi = mkTxInfo l tx

      frgT : (forge≡ tx≡ >>=ₜ λ v → ⌊ TxInfo.forge txi ≟ᶜ toValue v ⌋) ≡ true
      frgT with forge≡ tx≡
      ... | nothing = refl
      ... | just v  rewrite ≟-refl _≟ᶜ_ (toValue v) = refl

      rngT : (range≡ tx≡ >>=ₜ λ r → ⌊ TxInfo.range txi ≟ˢ r ⌋) ≡ true
      rngT with range≡ tx≡
      ... | nothing = refl
      ... | just v  rewrite ≟-refl _≟ˢ_ v = refl

      v≡ : valueSpent txi ≡ v
      v≡ rewrite sum-single {v = InputInfo.value (mkInputInfo l i₀)}
               | getSpent≡
               = refl

      spT  : (spent≥ tx≡ >>=ₜ (valueSpent txi ≥ᶜ_)) ≡ true
      spT rewrite v≡ = s≥

      verify≡ : verifyTx l tx tx≡ ≡ true
      verify≡ rewrite frgT | rngT | spT = refl
