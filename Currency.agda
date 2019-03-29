------------------------------------------------------------------------
-- Multi-currency support.
------------------------------------------------------------------------
module Currency where

open import Function     using (_∘_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Maybe   using (fromMaybe)
open import Data.Nat     using (ℕ; _+_)
open import Data.List    using (List; _∷_; []; sum; map; foldl)

open import Data.Nat.Properties using (<-strictTotalOrder; <-isStrictTotalOrder)

open import Relation.Binary using (StrictTotalOrder; Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

------------------------------------------------------------------------
-- Currency maps.

$ : ℕ → ℕ
$ v = v

open import Data.AVL <-strictTotalOrder public
  renaming (Tree to Tree'; map to mapValues)
  hiding   (Value)

CurrencyMap = Tree' (MkValue (λ _ → ℕ) (subst (λ _ → ℕ)))

_+ᶜ_ : CurrencyMap → CurrencyMap → CurrencyMap
c +ᶜ c′ = foldl go c (toList c′)
  where
    go : CurrencyMap → (ℕ × ℕ) → CurrencyMap
    go cur (currency , value) = insertWith currency ((_+ value) ∘ fromMaybe 0) cur

sumᶜ : List CurrencyMap → CurrencyMap
sumᶜ = foldl _+ᶜ_ empty

values : CurrencyMap → List ℕ
values = map proj₁ ∘ toList

ex-map : CurrencyMap
ex-map = fromList ( (1 , $ 50)
                  ∷ (2 , $ 77)
                  ∷ []
                  )
