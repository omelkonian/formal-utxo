open import Function using (_∘_; case_of_)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (Bool; T; true; false; if_then_else_; not)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Maybe   using (Maybe; fromMaybe; nothing)
  renaming (just to pure; ap to _<*>_) -- to use idiom brackets
open import Data.Fin     using (Fin; toℕ; fromℕ<)
  renaming (suc to fsuc; zero to fzero)
open import Data.Nat     using (ℕ; _<_; z≤n; s≤s; _+_)
  renaming (_≟_ to _≟ℕ_)
open import Data.List    using (List; []; _∷_; [_]; map; length; filter; null)

open import Data.Bool.Properties  using (T?)
open import Data.Maybe.Properties using (just-injective)

open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Membership.Propositional  using (_∈_; _∉_; find; mapWith∈)
open import Data.List.Membership.Propositional.Properties
  using (find∘map; ∈-map⁻; ∈-map⁺; ∈-filter⁻; ∈-filter⁺; ∈-++⁻; ∈-++⁺ʳ; ∈-++⁺ˡ)
open import Data.List.Relation.Unary.AllPairs   using ([]; _∷_)
open import Data.List.Relation.Unary.All        using ([]; _∷_)

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
open import UTxO.Hashing.MetaHash
open import UTxO.Types hiding (I)
open import StateMachine.Base

open PendingTxInput
open PendingTxOutput
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
_~_ {l} _ s = pure s ∈ ( map (fromData ∘ dataVal ∘ out)
                       ∘ filter ((_≟ℕ 𝕍) ∘ address ∘ out)
                       ) (utxo l)

view-~ : ∀ {l s} {vl : ValidLedger l}
  → vl ~ s
  → ∃[ u ]
      ( u ∈ utxo l
      × prevTx u ∈ l
      × (address (out u) ≡ 𝕍)
      × (dataVal (out u) ≡ toData s)
      × Σ[ prevOut∈ ∈ (s —→ $ (value (out u)) at sm ∈ outputs (prevTx u)) ]
          ( (outRef u ≡ ((prevTx u) ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈))
          × ((prevTx u) ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈) ∈ map outRef (utxo l)
          )
      )
view-~ {l} {s} vl~s
  with ∈-map⁻ (fromData ∘ dataVal ∘ out) vl~s
... | u
    , out∈ , data≡
  with ∈-filter⁻ ((_≟ℕ 𝕍) ∘ address ∘ out) {xs = utxo l} out∈
... | u∈ , refl
  with from-inj (dataVal (out u)) s (sym data≡)
... | refl
  with ∈utxo⇒outRef≡ {u = u} {l = l} u∈
... | prev∈ , prevOut∈ , outRef≡
    = u , u∈ , prev∈ , refl , refl , prevOut∈ , outRef≡ , prev∈utxo
  where
    prev∈utxo : ((prevTx u) ♯ₜₓ) indexed-at toℕ (Any.index prevOut∈) ∈ map outRef (utxo l)
    prev∈utxo rewrite sym outRef≡ = ∈-map⁺ outRef u∈
