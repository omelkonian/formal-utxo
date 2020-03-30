module UTxO.Uniqueness where

open import Level          using (0ℓ)
open import Function       using (_∘_; flip; case_of_)
open import Category.Monad using (RawMonad)

open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Bool  using (true)
open import Data.List  using (List; []; _∷_; map; filter)
open import Data.Maybe using (Maybe)

open import Data.Fin.Properties using (suc-injective; toℕ-injective)

open import Data.Maybe.Properties using (just-injective)
import Data.Maybe.Relation.Unary.Any as M
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List.Membership.Propositional            using (_∈_; mapWith∈)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-filter⁻)
open import Data.List.Relation.Unary.All as All using (All)
import Data.List.Relation.Unary.Any as Any

open import Data.List.Relation.Unary.All as All                      using (All)
open import Data.List.Relation.Unary.AllPairs as AllPairs            using ([]; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional            using (Unique)
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (++⁺; filter⁺)
open import Data.List.Relation.Binary.Disjoint.Propositional         using (Disjoint)

open import Relation.Nullary.Decidable                  using (⌊_⌋)
open import Relation.Binary                             using (Decidable)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; trans; cong; sym; _≢_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities
open import UTxO.Validity


-- ** We have to postulate that there exist no duplicate transactions.
postulate
  Unique-ledger : ∀ {l} → ValidLedger l → Unique l

Unique-mapWith∈ : ∀ {A B : Set} {xs : List A} {f : ∀ {x} → x ∈ xs → B}
  → (∀ {x x′} {x∈ : x ∈ xs} {x∈′ : x′ ∈ xs} → f x∈ ≡ f x∈′ → Any.index x∈ ≡ Any.index x∈′)
  → Unique (mapWith∈ xs f)
Unique-mapWith∈ {xs = []}     {f = f} f≡ = []
Unique-mapWith∈ {xs = x ∷ xs} {f = f} f≡
  = All.tabulate (mapWith∈-∀ {P = f (Any.here refl) ≢_} λ _ eq → case f≡ eq of λ () )
  ∷ Unique-mapWith∈ {xs = xs} (suc-injective ∘ f≡)

u∈mkUtxo : ∀ {u tx}
  → u ∈ mapWith∈ (outputs tx) (mkUtxo tx)
  → prevTx u ≡ tx
u∈mkUtxo {tx = tx} = mapWith∈-∀ {P = (_≡ tx) ∘ prevTx} λ _ → refl

Unique-utxo : ∀ {l}
  → ValidLedger l
  → Unique (utxo l)
Unique-utxo {l = []}      ∙                     = []
Unique-utxo {l = tx ∷ l } vl₀@(vl ⊕ .tx ∶- vtx) = ++⁺ uniqˡ uniqʳ disj
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
