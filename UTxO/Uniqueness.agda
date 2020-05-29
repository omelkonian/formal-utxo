module UTxO.Uniqueness where

open import Level          using (0ℓ)
open import Function       using (_∘_; flip; case_of_; _$_)
open import Category.Monad using (RawMonad)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤)
open import Data.Sum     using (_⊎_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Bool    using (true)
open import Data.List    using (List; []; _∷_; map; filter)
open import Data.Maybe   using (Maybe)
open import Data.Fin     using ()
  renaming (zero to fzero; suc to fsuc)

open import Data.Fin.Properties using (suc-injective; toℕ-injective)

open import Data.Maybe.Properties using (just-injective)
import Data.Maybe.Relation.Unary.Any as M
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List.Membership.Propositional            using (_∈_; _∉_; mapWith∈)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-filter⁻)

open import Data.List.Relation.Unary.All as All                      using (All)
open import Data.List.Relation.Unary.All.Properties                  using (¬Any⇒All¬)
open import Data.List.Relation.Unary.Any as Any                      using (Any; here; there)
open import Data.List.Relation.Unary.AllPairs as AllPairs            using ([]; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional            using (Unique)
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (++⁺; filter⁺)
open import Data.List.Relation.Binary.Subset.Propositional           using (_⊆_)
open import Data.List.Relation.Binary.Disjoint.Propositional         using (Disjoint)

open import Relation.Nullary                      using (¬_; yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋)
import Relation.Unary as Unary
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; _≢_)

open import Prelude.Lists

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
    = ¬Any⇒All¬ l tx∉ ∷ Unique-ledger vl
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
    lˡ = filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)
    lʳ = mapWith∈ (outputs tx) (mkUtxo tx)

    uniqˡ : Unique lˡ
    uniqˡ = filter⁺ ((SETₒ._∉? outputRefs tx) ∘ outRef) (Unique-utxo vl)

    uniqʳ : Unique lʳ
    uniqʳ = Unique-mapWith∈ h
      where
        h : ∀ {x x′} {x∈ : x ∈ outputs tx} {x∈′ : x′ ∈ outputs tx}
          → mkUtxo tx x∈ ≡ mkUtxo tx x∈′
          → Any.index x∈ ≡ Any.index x∈′
        h = toℕ-injective ∘ cong (index ∘ outRef)

    disj : Disjoint lˡ lʳ
    disj (x∈ˡ , x∈ʳ)
      with ∈-filter⁻ ((SETₒ._∉? outputRefs tx) ∘ outRef) {xs = utxo l} x∈ˡ
    ... | x∈ˡ′ , _
      with ∈utxo⇒outRef≡ {l = l} x∈ˡ′
    ... | x∈ˡ″ , _
      rewrite u∈mkUtxo x∈ʳ
      with AllPairs.head (Unique-ledger vl₀)
    ... | all≢tx
        = All.lookup all≢tx x∈ˡ″ refl
