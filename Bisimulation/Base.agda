open import Function using (_∘_; case_of_)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (Bool; T; true; false; if_then_else_; not)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Maybe   using (Maybe; fromMaybe; nothing; maybe)
  renaming (just to pure; ap to _<*>_) -- to use idiom brackets
open import Data.Fin     using (Fin; toℕ; fromℕ<)
  renaming (suc to fsuc; zero to fzero)
open import Data.Nat     using (ℕ; _<_; z≤n; s≤s; _+_; _≡ᵇ_)
  renaming (_≟_ to _≟ℕ_)
open import Data.List    using (List; []; _∷_; [_]; map; length; filter; null; all)

open import Data.Bool.Properties  using (T?)
open import Data.Maybe.Properties using (just-injective)

open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Unary.AllPairs   using ([]; _∷_)
open import Data.List.Relation.Unary.All        using ([]; _∷_)
open import Data.List.Membership.Propositional  using (_∈_; _∉_; find; mapWith∈)
open import Data.List.Membership.Propositional.Properties
  using (find∘map; ∈-map⁻; ∈-map⁺; ∈-filter⁻; ∈-filter⁺; ∈-++⁻; ∈-++⁺ʳ; ∈-++⁺ˡ)
open import Data.List.Relation.Binary.Equality.DecPropositional _≟ℕ_ using (_≡?_)

open import Relation.Nullary                            using (¬_; yes; no)
open import Relation.Nullary.Decidable                  using (⌊_⌋; toWitness)
open import Relation.Binary                             using (Decidable)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; cong; trans; sym; inspect)
  renaming ([_] to ≡[_])
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import Prelude.General
open import Prelude.Lists

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities
open import UTxO.Validity
open import StateMachine.Base

open InputInfo
open OutputInfo
open PendingTx

module Bisimulation.Base
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

stepₛₘ      = step sm
finalₛₘ     = isFinal sm
validatorₛₘ = mkValidator sm
𝕍 = validatorₛₘ ♯

_—→[_]_ : S → I → (S × TxConstraints) → Set
s —→[ i ] (s′ , tx≡) = stepₛₘ s i ≡ pure (s′ , tx≡)

infix 30 _—→[_∶-_]_
_—→[_∶-_]_ : ∀ {l} → ValidLedger l → (tx : Tx) → IsValidTx tx l → ValidLedger (tx ∷ l) → Set
vl —→[ tx ∶- vtx ] vl′ = vl′ ≡ vl ⊕ tx ∶- vtx

_~_ : ∀ {l} → ValidLedger l → S → Set
_~_ {l} _ s = (toData s) ♯ᵈ ∈ (map (dataHash ∘ out) ∘ filter ((𝕍 ≟ℕ_) ∘ address ∘ out)) (utxo l)

view-~ : ∀ {l} {s : S} {vl : ValidLedger l}
  → vl ~ s
  → ∃[ prevTx ] ∃[ v ] (Σ[ prevOut∈ ∈ (s —→ v at sm ∈ outputs prevTx) ]
      let
        oRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈)
        out  = record { address = 𝕍; dataHash = toData s ♯ᵈ; value = v }
        u    = record { prevTx = prevTx; out = out; outRef = oRef }
      in ( u ∈ utxo l
         × prevTx ∈ l
         × oRef ∈ map outRef (utxo l)
         × (getSpentOutputRef oRef l ≡ pure out)
         ))
view-~ {l} {s} vl~s
  with ∈-map⁻ (dataHash ∘ out) vl~s
... | u@(record {prevTx = prevTx; out = record {value = v}}) , out∈ , refl
  with ∈-filter⁻ ((𝕍 ≟ℕ_) ∘ address ∘ out) {xs = utxo l} out∈
... | u∈ , refl
  with ∈utxo⇒outRef≡ {u = u} {l = l} u∈
... | prev∈ , prevOut∈ , refl
    = prevTx , v , prevOut∈ , u∈ , prev∈ , ∈-map⁺ outRef u∈ , spent≡
  where
    oRef = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈)
    o    = record { address = 𝕍; dataHash = toData s ♯ᵈ; value = v }
    u′   = record { prevTx = prevTx; out = o; outRef = oRef }

    spent≡ : getSpentOutputRef oRef l ≡ pure o
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
    × maybe ((_≡ [ 𝕍 ]) ∘ currencies) ⊤ (forge≡ tx≡)

mkTx : ∀ {l} {s s′ : S} {i : I} {vl : ValidLedger l} {vl~s : vl ~ s}
  → (tx≡ : TxConstraints)
  → Satisfiable {vl = vl} tx≡ vl~s
  → Σ[ tx ∈ Tx ] (verifyTx l tx tx≡ ≡ true)
mkTx {l} {s} {s′} {i} {vl} {vl~s} tx≡ (r≡ , s≥ , _)
  with view-~ {vl = vl} vl~s
... | prevTx , v , prevOut∈ , _ , _ , _ , getSpent≡
    = tx , verify≡
    where
        frg = fromMaybe $0 (forge≡ tx≡)
        rng = fromMaybe (-∞ ⋯ +∞) (range≡ tx≡)

        x = (prevTx ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈) ←— (i , s) , sm

        tx = record { inputs  = [ x ]
                    ; outputs = [ s′ —→ (frg +ᶜ v) at sm ]
                    ; fee     = $0
                    ; forge   = frg
                    ; range   = rng }

        txi = mkTxInfo l tx

        frgT : (forge≡ tx≡ >>=ₜ λ v → ⌊ TxInfo.forge txi ≟ᶜ v ⌋) ≡ true
        frgT with forge≡ tx≡
        ... | nothing = refl
        ... | pure v  rewrite ≟-refl _≟ᶜ_ v = refl

        rngT : (range≡ tx≡ >>=ₜ λ r → ⌊ TxInfo.range txi ≟ˢ r ⌋) ≡ true
        rngT with range≡ tx≡
        ... | nothing = refl
        ... | pure v  rewrite ≟-refl _≟ˢ_ v = refl

        v≡ : valueSpent txi ≡ v
        v≡ rewrite sum-single {v = InputInfo.value (mkInputInfo l x)}
                 | getSpent≡
                 = refl

        spT  : (spent≥ tx≡ >>=ₜ (valueSpent txi ≥ᶜ_)) ≡ true
        spT rewrite v≡ = s≥

        verify≡ : verifyTx l tx tx≡ ≡ true
        verify≡ rewrite frgT | rngT | spT = refl
