{-# OPTIONS --allow-unsolved-metas #-}
module UTxO.Value where

open import Function using (_∘_)

open import Data.Product using (_×_; _,_; proj₁; proj₂; map₂)
open import Data.Bool    using (Bool; true; _∧_)
open import Data.Maybe   using (Maybe; just; nothing; fromMaybe; _>>=_)
open import Data.Nat     using (ℕ; _+_)
  renaming (_≟_ to _≟ℕ_)
open import Data.List    using (List; _∷_; []; [_]; sum; map; foldr; and)

open import Data.Nat.Properties     using (<-strictTotalOrder; _≥?_)
open import Data.List.Properties    renaming (≡-dec to ≡-decs)
open import Data.Product.Properties renaming (≡-dec to ≡-dec×)

open import Relation.Nullary                      using (yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary                       using (StrictTotalOrder; Rel; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import UTxO.Hashing.Base

--------------------------
-- Interface

CurrencySymbol = HashId
TokenName      = HashId
Quantity       = ℕ

------------------------------------------------------------------------
-- Values are maps from currency identifiers to maps from tokens to quantities.
--   1) A traditional currency will have a single token with infinite supply.
--   2) A non-fungible-token (NFT) currency will have many singular tokens.


-- Users works with a list representation of the underlying maps/trees.
SubValue = List (TokenName × Quantity)
Value = List (CurrencySymbol × SubValue)

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
  using    (Map; fromList; toList; empty; unionWith; lookup)
  renaming (map to mapValues)

TokenMap    = Map Quantity
CurrencyMap = Map TokenMap

toList² : CurrencyMap → Value
toList² m = toList (mapValues toList m)

fromList² : Value → CurrencyMap
fromList² = fromList ∘ map (map₂ fromList)

infixl 6 _+ᶜ_
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


infix 4 _≥ᶜ_
_≥ᶜ_ : Value → Value → Bool
c ≥ᶜ c′ =
  and (map (λ{ ( k₁ , vs ) →
    and (map (λ{ (k₂ , v) → ⌊ fromMaybe 0 (lookup k₁ (fromList² c) >>= lookup k₂) ≥? v ⌋ }) vs)}) c′)

-------------------
-- Sum notation

∑ : ∀ {A : Set} → List A → (A → Value) → Value
∑ []       f = $0
∑ (i ∷ []) f = f i
∑ (i ∷ is) f = f i +ᶜ ∑ is f

-- if one fails everything fails
∑M : ∀ {A : Set} → List A → (A → Maybe Value) → Maybe Value
∑M []       f = just $0
∑M (i ∷ []) f = f i
∑M (i ∷ is) f = f i >>= λ q → ∑M is f >>= λ qs → just (q +ᶜ qs)

-------------------
-- Properties

sum-single : ∀ {x} → sumᶜ [ x ] ≡ x
sum-single = {!!}

0+x≡x : ∀ {x} → $0 +ᶜ x ≡ x
0+x≡x = {!!}

x+0≡x : ∀ {x} → x +ᶜ $0 ≡ x
x+0≡x = {!!}

x+y+0≡y+x+0 : ∀ {x y} → x +ᶜ y +ᶜ $0 ≡ y +ᶜ x +ᶜ $0
x+y+0≡y+x+0 = {!!}
