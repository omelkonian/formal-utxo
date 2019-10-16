------------------------------------------------------------------------
-- Multi-currency support.
------------------------------------------------------------------------
module Data.Currency where

open import Function     using (_∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe   using (fromMaybe)
open import Data.Nat     using (ℕ; _+_; _≟_)
open import Data.List    using (List; _∷_; []; sum; map; foldl)

open import Data.Nat.Properties using (<-strictTotalOrder; <-isStrictTotalOrder)

open import Relation.Nullary using (yes; no)
open import Relation.Binary using (StrictTotalOrder; Rel; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

------------------------------------------------------------------------
-- Currency maps.

$ : ℕ → ℕ
$ v = v

Value = List (ℕ × ℕ)

$0 : Value
$0 = []

open import Data.AVL <-strictTotalOrder public
  renaming (Tree to Tree'; map to mapValues)
  hiding   (Value)

CurrencyMap = Tree' (MkValue (λ _ → ℕ) (subst (λ _ → ℕ)))

_+ᶜ_ : Value → Value → Value
c +ᶜ c′ = toList (foldl go (fromList c) c′)
  where
    go : CurrencyMap → (ℕ × ℕ) → CurrencyMap
    go cur (currency , value) = insertWith currency ((_+ value) ∘ fromMaybe 0) cur

sumᶜ : List Value → Value
sumᶜ = foldl _+ᶜ_ []

keys : Value → List ℕ
keys = map proj₁

values : Value → List ℕ
values = map proj₂

ex-map : Value
ex-map = (1 , $ 50)
       ∷ (2 , $ 77)
       ∷ []

infix 4 _≟ᶜ_
_≟ᶜ_ : Decidable {A = Value} _≡_
[]           ≟ᶜ []             = yes refl
[]           ≟ᶜ _ ∷ _          = no λ ()
_ ∷ _        ≟ᶜ []             = no λ ()
(x , y) ∷ xs ≟ᶜ (x′ , y′) ∷ ys with x ≟ x′
... | no ¬p                    = no λ{refl → ¬p refl}
... | yes refl                 with y ≟ y′
... | no ¬p                    = no λ{refl → ¬p refl}
... | yes refl                 with xs ≟ᶜ ys
... | no ¬p                    = no λ{refl → ¬p refl}
... | yes refl                 = yes refl
