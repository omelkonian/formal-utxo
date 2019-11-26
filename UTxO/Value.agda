------------------------------------------------------------------------
-- Multi-currency support.
------------------------------------------------------------------------
module UTxO.Value where

open import Function     using (_∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; map₂)
open import Data.Bool    using (Bool; true; _∧_)
open import Data.Maybe   using (fromMaybe)
open import Data.Nat     using (ℕ; _+_)
  renaming (_≟_ to _≟ℕ_)
open import Data.List    using (List; _∷_; []; sum; map; foldr)

open import Data.Nat.Properties     using (<-strictTotalOrder; _≥?_)
open import Data.List.Properties    renaming (≡-dec to ≡-decs)
open import Data.Product.Properties renaming (≡-dec to ≡-dec×)

open import Relation.Nullary                      using (yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary                       using (StrictTotalOrder; Rel; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

------------------------------------------------------------------------
-- Values are maps from currency identifiers to maps from tokens to quantities.
--   1) A traditional currency will have a single token with infinite supply.
--   2) A non-fungible-token (NFT) currency will have many singular tokens.

--------------------------
-- Interface

CurrencySymbol = ℕ
TokenName      = ℕ
Quantity       = ℕ

-- Users works with a list representation of the underlying maps/trees.
Value = List (CurrencySymbol × List (TokenName × Quantity))

currencies : Value → List ℕ
currencies = map proj₁

$0 : Value
$0 = []

ex-map : Value
ex-map = (1 , (0 , 50) ∷ [])
       ∷ (2 , (0 , 77) ∷ (1 , 23) ∷ [])
       ∷ []

--------------------------
-- Implementation
open import Data.AVL.Map <-strictTotalOrder
  using    (Map; fromList; toList; empty; unionWith)
  renaming (map to mapValues)

TokenMap    = Map Quantity
CurrencyMap = Map TokenMap

toList² : CurrencyMap → Value
toList² m = toList (mapValues toList m)

fromList² : Value → CurrencyMap
fromList² = fromList ∘ map (map₂ fromList)

_+ᶜ_ : Value → Value → Value
c +ᶜ c′ = toList² (unionWith (λ v v′ → v +ᶜ′ fromMaybe empty v′) (fromList² c) (fromList² c′))
  where
    _+ᶜ′_ : TokenMap → TokenMap → TokenMap
    _+ᶜ′_ = unionWith (λ v v′ → v + fromMaybe 0 v′)

sumᶜ : List Value → Value
sumᶜ = foldr _+ᶜ_ []

infix 4 _≟ᶜ_
_≟ᶜ_ : Decidable {A = Value} _≡_
_≟ᶜ_ = ≡-decs (≡-dec× _≟ℕ_ (≡-decs (≡-dec× _≟ℕ_ _≟ℕ_)))

checkBin : ∀ {V : Set} → V → (V → V → Bool) → Map V → Map V → Bool
checkBin {V} ε _⁇_ m m′ = all (mapValues proj₂ mb)
  where
    all : Map Bool → Bool
    all = foldr _∧_ true ∘ map proj₂ ∘ toList

    mb : Map (V × Bool)
    mb = unionWith (λ v v′ → v , v ⁇ proj₁ (fromMaybe (ε , true) v′)) m (mapValues (_, true) m′)

_≥ᶜ_ : Value → Value → Bool
c ≥ᶜ c′ = checkBin empty _≥ᶜ′_ (fromList² c) (fromList² c′)
  where
    _≥ᶜ′_ : TokenMap → TokenMap → Bool
    _≥ᶜ′_ = checkBin 0 (λ v v′ → ⌊ v ≥? v′ ⌋)
