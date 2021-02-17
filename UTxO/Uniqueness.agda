module UTxO.Uniqueness where

open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-filter⁻)
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (++⁺; filter⁺)
import Data.List.Relation.Unary.AllPairs as AllPairs

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Sets

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities
open import UTxO.Validity

postulate
  genesis : ∀ {l} → ValidLedger l → ¬Null l → count (null? ∘ inputs) l ≡ 1

Unique-ledger : ∀ {l} → ValidLedger l → Unique l
Unique-ledger {.[]}     ∙                    = []
Unique-ledger {.tx ∷ l} vl₀@(vl ⊕ tx ∶- vtx)
  with null? (inputs tx)
... | yes px
    = count-single {P? = null? ∘ inputs} (genesis vl₀ λ ()) px ∷ Unique-ledger vl
... | no ¬px
    = L.All.¬Any⇒All¬ l tx∉ ∷ Unique-ledger vl
    where
      tx∉ : tx ∉ l
      tx∉ tx∈ with x , x∈        ← ¬Null⇒∃x (map≢[] {f = outputRef} ¬px)
              with l′ , suf      ← ∈⇒Suffix tx∈
              with _ ⊕ _ ∶- vtx′ ← ≼⇒valid vl suf
                 = suf-utxo vl suf (validOutputRefs vtx′ x∈) x∈ (validOutputRefs vtx x∈)

u∈mkUtxo : ∀ {u tx}
  → u ∈ mapWith∈ (outputs tx) (mkUtxo tx)
  → prevTx u ≡ tx
u∈mkUtxo {tx = tx} = mapWith∈-∀ {P = (_≡ tx) ∘ prevTx} λ _ → refl

Unique-utxo : ∀ {l}
  → ValidLedger l
  → Unique (utxo l)
Unique-utxo {l = []}     ∙                     = []
Unique-utxo {l = tx ∷ l} vl₀@(vl ⊕ .tx ∶- vtx) = ++⁺ uniqˡ uniqʳ disj
  where
    lˡ = filter ((_∉? outputRefs tx) ∘ outRef) (utxo l)
    lʳ = mapWith∈ (outputs tx) (mkUtxo tx)

    uniqˡ : Unique lˡ
    uniqˡ = filter⁺ ((_∉? outputRefs tx) ∘ outRef) (Unique-utxo vl)

    uniqʳ : Unique lʳ
    uniqʳ = Unique-mapWith∈ h
      where
        h : ∀ {x x′} {x∈ : x ∈ outputs tx} {x∈′ : x′ ∈ outputs tx}
          → mkUtxo tx x∈ ≡ mkUtxo tx x∈′
          → L.Any.index x∈ ≡ L.Any.index x∈′
        h = F.toℕ-injective ∘ cong (index ∘ outRef)

    disj : Disjoint lˡ lʳ
    disj (x∈ˡ , x∈ʳ)
      with ∈-filter⁻ ((_∉? outputRefs tx) ∘ outRef) {xs = utxo l} x∈ˡ
    ... | x∈ˡ′ , _
      with ∈utxo⇒outRef≡ {l = l} x∈ˡ′
    ... | x∈ˡ″ , _
      rewrite u∈mkUtxo x∈ʳ
      with AllPairs.head (Unique-ledger vl₀)
    ... | all≢tx
        = L.All.lookup all≢tx x∈ˡ″ refl
