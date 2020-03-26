{-# OPTIONS --allow-unsolved-metas #-}
module UTxO.GlobalPreservation where

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

open import Data.List.Membership.Propositional            using (_∈_; mapWith∈)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.List.Relation.Unary.All as All using (All)
import Data.List.Relation.Unary.Any as Any

open import Data.List.Relation.Unary.All                             using (All)
open import Data.List.Relation.Unary.AllPairs                        using ([]; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional            using (Unique)
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (++⁺; filter⁺)
open import Data.List.Relation.Binary.Disjoint.Propositional         using (Disjoint)

open import Relation.Nullary.Decidable                  using (⌊_⌋)
open import Relation.Binary                             using (Decidable)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; trans; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities hiding (prevTx)
open import UTxO.Validity

open import Prelude.Set' using (_∈?_)

globalPreservation : ∀ {l} {vl : ValidLedger l} →
  ∑ l forge ≡ ∑ l fee +ᶜ ∑ (utxo l) (value ∘ out)
globalPreservation {[]}          {vl}              = refl
globalPreservation {l′@(tx ∷ l)} {vl₀@(vl ⊕ .tx ∶- vtx)} = h″
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
        ≡⟨ ∑M-just getSpent≡ ⟩
          pure (∑ (mapWith∈ (inputs tx) (out ∘ getUTXO)) value)
        ≡⟨ cong pure (begin
              ∑ (mapWith∈ (inputs tx) (out ∘ getUTXO)) value
            ≡⟨ ∑-∘ {xs = inputs tx} {g = getUTXO} {g′ = out} {f = value} ⟩
              ∑ (mapWith∈ (inputs tx) getUTXO) (value ∘ out)
            ≡⟨ cong (flip ∑ (value ∘ out)) (mapWith∈≡filter vor ndp) ⟩
              ∑ (filter ((SETₒ._∈? outputRefs tx) ∘ outRef) (utxo l)) (value ∘ out)
            ∎) ⟩
          pure (∑ (filter ((SETₒ._∈? outputRefs tx) ∘ outRef) (utxo l)) (value ∘ out))
        ∎)
        where
          getUTXO : ∀ {i} → i ∈ inputs tx → UTXO
          getUTXO = proj₁ ∘ ∈-map⁻ outRef ∘ All.lookup vor

          getSpent≡ : ∀ {i} → (i∈ : i ∈ inputs tx) → getSpentOutput l i ≡ pure ((out ∘ getUTXO) i∈)
          getSpent≡ {i} i∈
            with (∈-map⁻ outRef ∘ All.lookup vor) i∈
          ... | u , u∈ , refl
              = utxo-getSpent {l} {u} u∈


          mapWith∈≡filter : ∀ {A B C : Set} {_≟_ : Decidable (_≡_ {A = C})}
                              {is : List A} {us : List B} {f : A → C} {g : B → C}
            → (all               : All (λ i → f i ∈ map g us) is)
            -- (All.lookup all _  : f i ∈ map g us
            -- (∈-map⁻ g _        : ∃[ u ] (u ∈ us) × (f i ≡ g u)
            → Unique (map f is)
            → mapWith∈ is (proj₁ ∘ ∈-map⁻ g ∘ All.lookup all)
            ≡ filter ((λ x → _∈?_ _≟_  x (map f is)) ∘ g) us
          mapWith∈≡filter = {!!}

    pv : forge tx +ᶜ ∑in vl₀ ≡ fee tx +ᶜ ∑ (outputs tx) value
    pv = proj₂ (proj₂ (view-pv (preservesValues vtx)))

    gpv : ∑ l forge ≡ ∑ l fee +ᶜ ∑ (utxo l) (value ∘ out)
    gpv = globalPreservation {l} {vl}

    +ᶜ-helper : ∀ {x x′ y y′ : Value} → x ≡ x′ → y ≡ y′ → x +ᶜ y ≡ x′ +ᶜ y′
    +ᶜ-helper refl refl = refl

    pv-gpv : (forge tx +ᶜ ∑in vl₀) +ᶜ ∑ l forge
           ≡ (fee tx +ᶜ ∑ (outputs tx) value) +ᶜ (∑ l fee +ᶜ ∑ (utxo l) (value ∘ out))
    pv-gpv = +ᶜ-helper {x = forge tx +ᶜ ∑in vl₀} {x′ = fee tx +ᶜ ∑ (outputs tx) value}
                       {y = ∑ l forge} {y′ = ∑ l fee +ᶜ ∑ (utxo l) (value ∘ out)}
                       pv gpv

    +ᶜ-comm-helper : ∀ {x₁ x₂ x₃ y₁ y₂ y₃ y₄ : Value}
      → (x₁ +ᶜ x₂) +ᶜ x₃ ≡ (y₁ +ᶜ y₂) +ᶜ (y₃ +ᶜ y₄)
      → x₁ +ᶜ x₃ +ᶜ x₂ ≡ y₁ +ᶜ y₃ +ᶜ y₄ +ᶜ y₂
    +ᶜ-comm-helper {x₁} {x₂} {x₃} {y₁} {y₂} {y₃} {y₄} p
      rewrite +ᶜ-assoc {x = x₁} {y = x₂} {z = x₃}
            | +ᶜ-comm {x = x₂} {y = x₃}
            | sym (+ᶜ-assoc {x = x₁} {y = x₃} {z = x₂})
            | +ᶜ-assoc {x = y₁} {y = y₂} {z = y₃ +ᶜ y₄}
            | +ᶜ-comm {x = y₂} {y = y₃ +ᶜ y₄} -- y₁ +ᶜ ((y₃ +ᶜ y₄) +ᶜ y₂)
            | sym (+ᶜ-assoc {x = y₁} {y = y₃ +ᶜ y₄} {z = y₂})
            | sym (+ᶜ-assoc {x = y₁} {y = y₃} {z = y₄})
            = p

    pv-gpv′ : forge tx +ᶜ ∑ l forge +ᶜ ∑in vl₀
            ≡ fee tx +ᶜ ∑ l fee +ᶜ ∑ (utxo l) (value ∘ out) +ᶜ ∑ (outputs tx) value
    pv-gpv′ = +ᶜ-comm-helper {x₁ = forge tx} {x₂ = ∑in vl₀} {x₃ = ∑ l forge}
                             {y₁ = fee tx} {y₂ = ∑ (outputs tx) value} {y₃ = ∑ l fee}
                             {y₄ = ∑ (utxo l) (value ∘ out)}
                             pv-gpv

    pv-gpv″ : ∑ l′ forge +ᶜ ∑in vl₀
            ≡ ∑ l′ fee +ᶜ ∑ (outputs tx) value +ᶜ ∑ (utxo l) (value ∘ out)
    pv-gpv″
      rewrite +ᶜ-assoc {x = ∑ l′ fee} {y = ∑ (outputs tx) value} {z = ∑ (utxo l) (value ∘ out)}
            | +ᶜ-comm {x = ∑ (outputs tx) value} {y = ∑ (utxo l) (value ∘ out)}
            | sym (+ᶜ-assoc {x = ∑ l′ fee} {y = ∑ (utxo l) (value ∘ out)} {z = ∑ (outputs tx) value})
            = pv-gpv′

    helper : ∀ {l tx} {vl : ValidLedger (tx ∷ l)} {x y : Value}
      → x +ᶜ ∑in vl ≡ y +ᶜ ∑ (utxo l) (value ∘ out)
      → x ≡ y +ᶜ ∑ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) (value ∘ out)
    helper {l} {tx} {vl} {x} {y} p
      rewrite ∑-outRef {l} {tx} {vl}
            | ∑-filter {xs = utxo l} {q = (SETₒ._∈? outputRefs tx) ∘ outRef}
                       {f = value ∘ out} {x = x} {y = y} p
            = refl

    h : ∑ l′ forge
      ≡ ∑ l′ fee
      +ᶜ ∑ (outputs tx) value
      +ᶜ ∑ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) (value ∘ out)
    h = helper {l = l} {tx = tx} {vl = vl₀}
               {x = ∑ l′ forge}
               {y = ∑ l′ fee +ᶜ ∑ (outputs tx) value} pv-gpv″

    h′ : ∑ l′ forge
       ≡ ∑ l′ fee
       +ᶜ ( ∑ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) (value ∘ out)
         +ᶜ ∑ (outputs tx) value )
    h′ rewrite +ᶜ-comm {x = ∑ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) (value ∘ out)}
                       {y = ∑ (outputs tx) value}
             | sym (+ᶜ-assoc {x = ∑ l′ fee}
                             {y = ∑ (outputs tx) value}
                             {z = ∑ (filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)) (value ∘ out)})
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

    h″ : ∑ l′ forge ≡ ∑ l′ fee +ᶜ ∑ (utxo l′) (value ∘ out)
    h″ rewrite ∑-utxo {l} {tx} = h′
