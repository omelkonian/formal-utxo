module UTxO.Value where

open import Level          using (0ℓ)
open import Function       using (_∘_; flip; _$_)
open import Category.Monad using (RawMonad)

open import Data.Bool  using (Bool; true; _∧_; T)

open import Data.Product using (_×_; _,_; proj₁; proj₂; map₂; ∃; ∃-syntax)
open import Data.Product.Properties renaming (≡-dec to ≡-dec×)

open import Data.Maybe using (Maybe; just; nothing; fromMaybe; Is-nothing)
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.Nat using () renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (<-strictTotalOrder)

open import Data.Integer renaming (_≟_ to _≟ℤ_)
open import Data.Integer.Properties using (_≤?_)

open import Data.List hiding (fromMaybe; lookup) renaming (sum to ∑ℕ)
open import Data.List.Properties renaming (≡-dec to ≡-decs)

open import Data.List.Membership.Propositional using (_∈_; mapWith∈)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)

open import Relation.Nullary                      using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Nullary.Negation             using (¬?)
open import Relation.Binary                       using (StrictTotalOrder; Rel; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Prelude.Lists
import Prelude.Set' as SET

open import UTxO.Crypto

--------------------------
-- Interface

PolicyID AssetClass Asset Quantity : Set
PolicyID   = HashId
Asset      = HashId
Quantity   = ℤ
AssetClass = PolicyID × Asset

------------------------------------------------------------------------
-- Values are maps from currency identifiers to maps from tokens to quantities.
--   1) A traditional currency will have a single token with infinite supply.
--   2) A non-fungible-token (NFT) currency will have many singular tokens.


-- Users works with a list representation of the underlying maps/trees.
SubValue = List (Asset × Quantity)
Value = List (PolicyID × SubValue)

supp : ∀ {A B : Set} → List (A × B) → List A
supp = map proj₁

$0 : Value
$0 = []

--------------------------
-- Implementation

open import Data.AVL.Map <-strictTotalOrder
  using    (Map; empty; unionWith; lookup)
  renaming (map to mapᵛ; fromList to fromListᵛ; toList to toListᵛ)

TokenMap    = Map Quantity
CurrencyMap = Map TokenMap

mapᶜ : ∀ {A B C : Set} → (B → C) → List (A × B) → List (A × C)
mapᶜ f = map (map₂ f)

toListᶜ : CurrencyMap → Value
toListᶜ m = toListᵛ (mapᵛ toListᵛ m)

fromListᶜ : Value → CurrencyMap
fromListᶜ = fromListᵛ ∘ mapᶜ fromListᵛ

infixl 6 _+ᵛ′_
_+ᵛ′_ : TokenMap → TokenMap → TokenMap
_+ᵛ′_ = unionWith (λ v v′ → v + fromMaybe (+ 0) v′)

infixl 6 _+ᵛ_
_+ᵛ_ : CurrencyMap → CurrencyMap → CurrencyMap
_+ᵛ_ = unionWith (λ v v′ → v +ᵛ′ fromMaybe empty v′)

infixl 6 _+ᶜ_
_+ᶜ_ : Value → Value → Value
c +ᶜ c′ = toListᶜ (fromListᶜ c +ᵛ fromListᶜ c′)

sumᶜ : List Value → Value
sumᶜ = foldr _+ᶜ_ $0

infix 4 _≟ᶜ_
_≟ᶜ_ : Decidable {A = Value} _≡_
_≟ᶜ_ = ≡-decs (≡-dec× _≟ℕ_ (≡-decs (≡-dec× _≟ℕ_ _≟ℤ_)))

lookupᶜ : PolicyID → Value → SubValue
lookupᶜ pid = fromMaybe [] ∘ (toListᵛ <$>_) ∘ lookup pid ∘ fromListᶜ

lookupQuantity : AssetClass → Value → Quantity
lookupQuantity (c , t) v = fromMaybe (+ 0) (lookup c (fromListᶜ v) >>= lookup t)

infix 4 _≥ᶜ_
_≥ᶜ_ : Value → Value → Bool
c ≥ᶜ c′ =
  and (map (λ{ ( k₁ , vs ) →
    and (map (λ{ (k₂ , v) → ⌊ v ≤? lookupQuantity (k₁ , k₂) c ⌋}) vs)}) c′)

infix 4 _≤ᶜ_
_≤ᶜ_ : Value → Value → Bool
_≤ᶜ_ = flip _≥ᶜ_

_∈ᶜ_ : PolicyID → Value → Bool
pid ∈ᶜ v = ⌊ pid ∈? supp v ⌋
  where open SET _≟ℕ_

-- Sum notation
∑ : ∀ {A : Set} → List A → (A → Value) → Value
∑ xs f = sumᶜ (map f xs)

∑M : ∀ {A : Set} → List (Maybe A) → (A → Value) → Maybe Value
∑M xs f = (flip ∑ f) <$> seqM xs
  where
    -- if one fails everything fails
    seqM : ∀ {A : Set} → List (Maybe A) → Maybe (List A)
    seqM []       = just []
    seqM (x ∷ xs) = ⦇ x ∷ seqM xs ⦈
