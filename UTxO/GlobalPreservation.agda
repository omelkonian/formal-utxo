module UTxO.GlobalPreservation where

open import Function       using (_$_)
open import Level          using (0ℓ)
open import Function       using (_∘_; flip)
open import Category.Monad using (RawMonad)

open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Bool  using (true)
open import Data.List  using (List; []; _∷_; map; filter)
open import Data.Maybe using (Maybe)

open import Data.Maybe.Properties using (just-injective)
import Data.Maybe.Relation.Unary.Any as M
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List.Properties                                           using (map-compose)
open import Data.List.Membership.Propositional                             using (_∈_; mapWith∈)
open import Data.List.Membership.Propositional.Properties                  using (∈-map⁻)
open import Data.List.Relation.Unary.All as All                            using (All)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.All                                   using (All)
open import Data.List.Relation.Unary.AllPairs                              using ([]; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional                  using (Unique)
open import Data.List.Relation.Unary.Unique.Propositional.Properties       using (++⁺; filter⁺)
open import Data.List.Relation.Binary.Disjoint.Propositional               using (Disjoint)
open import Data.List.Relation.Binary.Subset.Propositional                 using (_⊆_)
open import Data.List.Relation.Binary.Permutation.Propositional            using (_↭_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (map⁺)

open import Relation.Nullary                            using (Dec)
open import Relation.Nullary.Decidable                  using (⌊_⌋)
open import Relation.Binary                             using (Decidable)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; trans; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Prelude.Lists using (mapWith∈↭filter; ↭⇒≡)

open import UTxO.Hashing
open import UTxO.Value
open import UTxO.Types
open import UTxO.TxUtilities
open import UTxO.Validity
open import UTxO.Uniqueness

globalPreservation : ∀ {l} {vl : ValidLedger l} →
  ∑ l forge ≡ ∑ (utxo l) (value ∘ out)
globalPreservation {[]}          {vl}                    = refl
globalPreservation {l₀@(tx ∷ l)} {vl₀@(vl ⊕ .tx ∶- vtx)} = h″
  where
    view-pv : ∀ {A : Set} {mx : Maybe A} {P : A → Set}
      → M.Any P mx
      → ∃[ x ] ((mx ≡ pure x) × P x)
    view-pv (M.just p) = _ , refl , p

    ∑in : ∀ {l tx} → ValidLedger (tx ∷ l) → Value
    ∑in (_ ⊕ _ ∶- vtx) = (proj₁ ∘ view-pv ∘ preservesValues) vtx

    ∑-outRef : ∀ {l} {tx} {vl : ValidLedger (tx ∷ l)}
      → ∑in vl
      ≡ ∑ (filter ((SETₒ._∈? outputRefs tx) ∘ outRef) (utxo l)) (value ∘ out)
    ∑-outRef {l} {tx} {vl₀@(vl ⊕ _ ∶- vtx@(record { validOutputRefs  = vor
                                                  ; preservesValues  = pv
                                                  ; noDoubleSpending = ndp }))}
      = just-injective (begin
          pure (∑in vl₀)
        ≡⟨ sym (proj₁ (proj₂ (view-pv pv))) ⟩
          ∑M (map (getSpentOutput l) (inputs tx)) value
        ≡⟨⟩
          ∑M (map (getSpentOutputRef l ∘ outputRef) (inputs tx)) value
        ≡⟨ cong (λ x → ∑M x value) (map-compose {g = getSpentOutputRef l} {f = outputRef} (inputs tx)) ⟩
          ∑M (map (getSpentOutputRef l) (outputRefs tx)) value
        ≡⟨ ∑M-just getSpent≡ ⟩
          pure (∑ (mapWith∈ (outputRefs tx) (out ∘ getUTXO)) value)
        ≡⟨ cong pure (begin
              ∑ (mapWith∈ (outputRefs tx) (out ∘ getUTXO)) value
            ≡⟨ ∑-∘ {xs = outputRefs tx} {g = getUTXO} {g′ = out} {f = value} ⟩
              ∑ (mapWith∈ (outputRefs tx) getUTXO) (value ∘ out)
            ≡⟨ ∑map≡∑filter ⟩
              ∑ (filter ((SETₒ._∈? outputRefs tx) ∘ outRef) (utxo l)) (value ∘ out)
            ∎) ⟩
          pure (∑ (filter ((SETₒ._∈? outputRefs tx) ∘ outRef) (utxo l)) (value ∘ out))
        ∎)
        where
          getUTXO : ∀ {o} → o ∈ outputRefs tx → UTXO
          getUTXO = proj₁ ∘ ∈-map⁻ outRef ∘ vor

          getSpent≡ : ∀ {o} → (o∈ : o ∈ outputRefs tx) → getSpentOutputRef l o ≡ pure ((out ∘ getUTXO) o∈)
          getSpent≡ o∈
            with ∈-map⁻ outRef (vor o∈)
          ... | u , u∈ , refl
              = utxo-getSpent {l} {u} u∈

          map↭filter : mapWith∈ (outputRefs tx) getUTXO
                     ↭ filter ((SETₒ._∈? outputRefs tx) ∘ outRef) (utxo l)
          map↭filter = mapWith∈↭filter {_∈?_ = SETₒ._∈?_} vor (Unique-utxo vl)

          ∑map≡∑filter : ∑ (mapWith∈ (outputRefs tx) getUTXO) (value ∘ out)
                       ≡ ∑ (filter ((SETₒ._∈? outputRefs tx) ∘ outRef) (utxo l)) (value ∘ out)
          ∑map≡∑filter = ↭⇒≡ +ᶜ-identity +ᶜ-comm (map⁺ (value ∘ out) map↭filter)

    pv : forge tx +ᶜ ∑in vl₀ ≡ ∑ (outputs tx) value
    pv = proj₂ (proj₂ (view-pv (preservesValues vtx)))

    gpv : ∑ l forge ≡ ∑ (utxo l) (value ∘ out)
    gpv = globalPreservation {l} {vl}

    +ᶜ-helper : ∀ {x x′ y y′ : Value} → x ≡ x′ → y ≡ y′ → x +ᶜ y ≡ x′ +ᶜ y′
    +ᶜ-helper refl refl = refl

    pv-gpv : forge tx +ᶜ ∑in vl₀ +ᶜ ∑ l forge
           ≡ ∑ (outputs tx) value +ᶜ ∑ (utxo l) (value ∘ out)
    pv-gpv = +ᶜ-helper {x = forge tx +ᶜ ∑in vl₀} {x′ = ∑ (outputs tx) value}
                       {y = ∑ l forge} {y′ = ∑ (utxo l) (value ∘ out)}
                       pv gpv

    pv-gpv′ : forge tx +ᶜ ∑ l forge +ᶜ ∑in vl₀
            ≡ ∑ (utxo l) (value ∘ out) +ᶜ ∑ (outputs tx) value
    pv-gpv′ rewrite +ᶜ-assoc (forge tx) (∑ l forge) (∑in vl₀)
                  | +ᶜ-comm (∑ l forge) (∑in vl₀)
                  | sym $ +ᶜ-assoc (forge tx) (∑in vl₀) (∑ l forge)
                  | +ᶜ-comm (∑ (utxo l) (value ∘ out)) (∑ (outputs tx) value)
                  = pv-gpv

    pv-gpv″ : ∑ l₀ forge +ᶜ ∑in vl₀
            ≡ ∑ (outputs tx) value +ᶜ ∑ (utxo l) (value ∘ out)
    pv-gpv″
      rewrite +ᶜ-comm (∑ (outputs tx) value) (∑ (utxo l) (value ∘ out))
            = pv-gpv′

    helper : ∀ {l tx} {vl : ValidLedger (tx ∷ l)} {x y : Value}
      → x +ᶜ ∑in vl ≡ y +ᶜ ∑ (utxo l) (value ∘ out)
      → x ≡ y +ᶜ ∑ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) (value ∘ out)
    helper {l} {tx} {vl} {x} {y} p
      rewrite ∑-outRef {l} {tx} {vl}
            | ∑-filter {xs = utxo l} {q = (SETₒ._∈? outputRefs tx) ∘ outRef}
                       {f = value ∘ out} {x = x} {y = y} p
            = refl

    h : ∑ l₀ forge
      ≡  ∑ (outputs tx) value
      +ᶜ ∑ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) (value ∘ out)
    h = helper {l = l} {tx = tx} {vl = vl₀}
               {x = ∑ l₀ forge}
               {y = ∑ (outputs tx) value} pv-gpv″

    h′ : ∑ l₀ forge
       ≡ ( ∑ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) (value ∘ out)
         +ᶜ ∑ (outputs tx) value )
    h′ rewrite +ᶜ-comm (∑ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) (value ∘ out))
                       (∑ (outputs tx) value)
             = h

    ∑-utxo : ∀ {l tx}
      → ∑ (utxo (tx ∷ l)) (value ∘ out)
      ≡ ∑ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) (value ∘ out) +ᶜ ∑ (outputs tx) value
    ∑-utxo {l} {tx}
      rewrite ∑-++ {xs = filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)}
                   {ys = mapWith∈ (outputs tx) (mkUtxo tx)}
                   {fv = value ∘ out}
            | ∑-mapWith∈ {xs = outputs tx} {fv = value} {gv = out} {f = mkUtxo tx} (λ _ → refl)
            = refl

    h″ : ∑ l₀ forge ≡ ∑ (utxo l₀) (value ∘ out)
    h″ rewrite ∑-utxo {l} {tx} = h′
