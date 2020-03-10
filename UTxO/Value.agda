{-# OPTIONS --allow-unsolved-metas #-}
module UTxO.Value where

open import Function using (_∘_; flip)

open import Data.Product using (_×_; _,_; proj₁; proj₂; map₂)
open import Data.Bool    using (Bool; true; _∧_)
open import Data.Maybe   using (Maybe; nothing; fromMaybe; _>>=_)
  renaming (just to pure; ap to _<*>_; map to _<$>_) -- to use idiom brackets
open import Data.Nat     using (ℕ; _+_)
  renaming (_≟_ to _≟ℕ_)
open import Data.List    using (List; _∷_; []; [_]; _++_; sum; map; foldr; and; filter)

open import Data.List.Membership.Propositional  using (_∈_; mapWith∈)

open import Data.Nat.Properties     using (<-strictTotalOrder; _≥?_; +-identityʳ)
open import Data.List.Properties    renaming (≡-dec to ≡-decs)
open import Data.Product.Properties renaming (≡-dec to ≡-dec×)

open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Nullary.Negation             using (¬?)
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
_+ᵛ′_ = unionWith (λ v v′ → v + fromMaybe 0 v′)

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
_≟ᶜ_ = ≡-decs (≡-dec× _≟ℕ_ (≡-decs (≡-dec× _≟ℕ_ _≟ℕ_)))

infix 4 _≥ᶜ_
_≥ᶜ_ : Value → Value → Bool
c ≥ᶜ c′ =
  and (map (λ{ ( k₁ , vs ) →
    and (map (λ{ (k₂ , v) → ⌊ fromMaybe 0 (lookup k₁ (fromListᶜ c) >>= lookup k₂) ≥? v ⌋}) vs)}) c′)

-------------------
-- Sum notation

∑ : ∀ {A : Set} → List A → (A → Value) → Value
∑ xs f = sumᶜ (map f xs)

∑∈ : ∀ {A : Set} → (xs : List A) → (∀ {x} → x ∈ xs → Value) → Value
∑∈ xs f = sumᶜ (mapWith∈ xs f)

∑M : ∀ {A : Set} → List (Maybe A) → (A → Value) → Maybe Value
∑M xs f = (flip ∑ f) <$> seqM xs
  where
    -- if one fails everything fails
    seqM : ∀ {A : Set} → List (Maybe A) → Maybe (List A)
    seqM []       = pure []
    seqM (x ∷ xs) = ⦇ x ∷ seqM xs ⦈

-------------------
-- Properties

private
  variable
    A B C : Set
    xs ys : List A
    v     : List (ℕ × A)
    m     : Map B

postulate
  -- Properties of _+ᶜ_
  +ᶜ-comm  : ∀ {x y : Value} → x +ᶜ y ≡ y +ᶜ x
  +ᶜ-assoc : ∀ {x y z : Value} → x +ᶜ y +ᶜ z ≡ x +ᶜ (y +ᶜ z)

  -- Properties of ∑
  ∑-++ : ∀ {fv : A → Value} → ∑ (xs ++ ys) fv ≡ ∑ xs fv +ᶜ ∑ ys fv
  ∑-mapWith∈ : ∀ {fv : A → Value} {gv : B → A} {f : ∀ {x : A} → x ∈ xs → B}
             → (∀ {x} → (x∈ : x ∈ xs) → gv (f x∈) ≡ x)
             → ∑ (mapWith∈ xs f) (fv ∘ gv) ≡ ∑ xs fv
  ∑-filter : ∀ {P : A → Set} {q : (x : A) → Dec (P x)} {f : A → Value} {x y : Value}
           → x +ᶜ ∑ (filter q xs) f ≡ y +ᶜ ∑ xs f
           → x ≡ y +ᶜ ∑ (filter (¬? ∘ q) xs) f
  ∑-∘ : ∀ {xs : List A} {g : ∀ {x} → x ∈ xs → B} {g′ : B → C} {f : C → Value}
    → ∑ (mapWith∈ xs (g′ ∘ g)) f
    ≡ ∑ (mapWith∈ xs g) (f ∘ g′)

  -- Properties of ∑M
  ∑M-pure : ∀ {m : A → Maybe B} {f : B → Value} {g : ∀ {x} → x ∈ xs → B}
    → (∀ {x} (x∈ : x ∈ xs) → m x ≡ pure (g {x} x∈))
    → ∑M (map m xs) f ≡ pure (∑ (mapWith∈ xs g) f)

  -- Properties from Data.AVL.Properties
  toListᵛ∘fromListᵛ : toListᵛ (fromListᵛ v) ≡ v
  unionWith-identityʳ : ∀ {f : B → Maybe B → B} → unionWith f m empty ≡ mapᵛ (λ x → f x nothing) m
  mapᵛ-id           : ∀ {f : B → B} → (∀ {x} → f x ≡ x) → mapᵛ f m ≡ m

  -- Properties of UTxO.Value.mapᶜ
  mapᵛ-fromListᵛ      : ∀ {f : A → B} → mapᵛ f (fromListᵛ v) ≡ fromListᵛ (mapᶜ f v)
  mapᶜ∘mapᶜ         : ∀ {g : A → B} {f : B → C} → (mapᶜ f ∘ mapᶜ g) v ≡ mapᶜ (f ∘ g) v
  mapᶜ-id          : ∀ {f : A → A} → (∀ {x} → f x ≡ x) → mapᶜ f v ≡ v

toListᶜ∘fromListᶜ : ∀ {v} → toListᶜ (fromListᶜ v) ≡ v
toListᶜ∘fromListᶜ {v}
  rewrite mapᵛ-fromListᵛ {v = mapᶜ fromListᵛ v} {f = toListᵛ}
        | mapᶜ∘mapᶜ {v = v} {g = fromListᵛ} {f = toListᵛ}
        | mapᶜ-id {v = v} {f = toListᵛ ∘ fromListᵛ} toListᵛ∘fromListᵛ
        | toListᵛ∘fromListᵛ {v = v}
        = refl


unionWith-empty-id : ∀ {A : Set} {m : Map A} {f : A → Maybe A → A}
  → (∀ {x} → f x nothing ≡ x)
  → unionWith f m empty ≡ m
unionWith-empty-id {m = m} {f = f} f≡
  rewrite unionWith-identityʳ {m = m} {f = f}
        | mapᵛ-id {m = m} {f = λ x → f x nothing} f≡
        = refl

x+ᶜ′0≡x : ∀ {m} → m +ᵛ′ empty ≡ m
x+ᶜ′0≡x {m} rewrite unionWith-empty-id {m = m} {f = λ v v′ → v + fromMaybe 0 v′} (λ {x} → +-identityʳ x)
                  = refl

x+ᶜ0≡x : ∀ {v} → v +ᶜ $0 ≡ v
x+ᶜ0≡x {v} rewrite unionWith-empty-id {m = fromListᶜ v} {f = λ v v′ → v +ᵛ′ fromMaybe empty v′} x+ᶜ′0≡x
                 | toListᶜ∘fromListᶜ {v = v}
                 = refl

0+ᶜx≡x : ∀ {v} → $0 +ᶜ v ≡ v
0+ᶜx≡x {v} = toListᶜ∘fromListᶜ {v = v}

sum-single : ∀ {v} → sumᶜ [ v ] ≡ v
sum-single {v} rewrite x+ᶜ0≡x {v} = refl
