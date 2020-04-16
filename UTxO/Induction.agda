{-# OPTIONS --allow-unsolved-metas #-}
module UTxO.Induction where
-- Well-founded recursion based on suffix relation.

open import Level
open import Function
open import Induction
open import Induction.WellFounded
open import Data.Product
open import Data.List
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (here; there)
open import Data.List.Relation.Binary.Pointwise            using (_∷_; Pointwise-≡⇒≡)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Prelude.Lists

open import UTxO.Types
open import UTxO.Validity

_≺_ : Rel Ledger 0ℓ
l′ ≺ l = ∃[ tx ] Suffix≡ (tx ∷ l′) l

≺-trans : Transitive _≺_
≺-trans = {!!}

≺-there : ∀ {l′ l tx} → l′ ≺ l → l′ ≺ (tx ∷ l)
≺-there = map₂ there

≺-wf : WellFounded _≺_
≺-wf l = acc $ go l
  where
    go : ∀ l l′ → l′ ≺ l → Acc _≺_ l′
    go (_ ∷ l) l′ (_ , here (refl ∷ eq)) = acc λ y y<l′ → go l y (subst (y ≺_) (Pointwise-≡⇒≡ eq) y<l′)
    go (_ ∷ l) l′ (_ , there l′<l)       = acc λ y y<l′ → go l y (≺-trans y<l′ (_ , l′<l))

_≺′_ : Rel (∃ ValidLedger) 0ℓ
(l , _) ≺′ (l′ , _) = l ≺ l′

_≺′⇒≺_ : ∀ vl → Acc _≺_ (proj₁ vl) → Acc _≺′_ vl
(l , _) ≺′⇒≺ acc w = acc λ{ (l′ , _) l′<l → (l′ , _) ≺′⇒≺ w l′ l′<l }

≺′-wf : WellFounded _≺′_
≺′-wf vl = vl ≺′⇒≺ ≺-wf (proj₁ vl)

≺′-rec = All.wfRec ≺′-wf 0ℓ

_≼_ : Rel Ledger 0ℓ
_≼_ = Suffix≡

_≼′_ : Rel (∃ ValidLedger) 0ℓ
(l′ , _) ≼′ (l , _) = l′ ≼ l

postulate
  suffix-refl : ∀ {A : Set} → (xs : List A) → Suffix≡ xs xs

≺-transˡ : ∀ {x y z}
  → x ≼ y
  → y ≺ z
  → x ≺ z
≺-transˡ = {!!}

outputsₘ : ∃ ValidLedger → List TxOutput
outputsₘ ([]     , _) = []
outputsₘ (tx ∷ _ , _) = outputs tx
