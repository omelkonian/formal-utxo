{-# OPTIONS --allow-unsolved-metas #-}
module UTxO.Value where

open import Level          using (0ℓ)
open import Function       using (_∘_; flip; _$_)
open import Category.Monad using (RawMonad)

open import Data.Product using (_×_; _,_; proj₁; proj₂; map₂; ∃; ∃-syntax)
open import Data.Bool    using (Bool; true; _∧_; T)
open import Data.Maybe   using (Maybe; just; nothing; fromMaybe; Is-nothing)
open import Data.Nat     using (ℕ; _+_; suc; _≤_; _≥_; _>_)
  renaming (_≟_ to _≟ℕ_)
open import Data.List    using (List; _∷_; []; [_]; _++_; map; foldr; and; filter; mapMaybe)
  renaming (sum to ∑ℕ)

import Data.Maybe.Relation.Unary.Any as M
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.Nat.Properties     using (<-strictTotalOrder; _≥?_; _>?_; +-identityʳ)
open import Data.List.Properties    renaming (≡-dec to ≡-decs)
open import Data.Product.Properties renaming (≡-dec to ≡-dec×)

open import Data.List.Membership.Propositional using (_∈_; mapWith∈)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)

open import Relation.Nullary                      using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Nullary.Negation             using (¬?)
open import Relation.Binary                       using (StrictTotalOrder; Rel; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Prelude.Lists

open import UTxO.Hashing.Base

--------------------------
-- Interface

CurrencySymbol = HashId
TokenName      = HashId
Quantity       = ℕ

TokenClass = CurrencySymbol × TokenName

------------------------------------------------------------------------
-- Values are maps from currency identifiers to maps from tokens to quantities.
--   1) A traditional currency will have a single token with infinite supply.
--   2) A non-fungible-token (NFT) currency will have many singular tokens.


-- Users works with a list representation of the underlying maps/trees.
SubValue = List (TokenName × Quantity)
Value = List (CurrencySymbol × SubValue)


currencies : Value → List ℕ
currencies = map proj₁

singleToken : TokenClass → Value
singleToken (c , t) = [ c , [ t , 1 ] ]

$0 : Value
$0 = []

ex-map : Value
ex-map = (1 , (0 , 50) ∷ [])
       ∷ (2 , (0 , 77) ∷ (1 , 23) ∷ [])
       ∷ []

open import Algebra.Definitions {A = Value} _≡_
  using (LeftIdentity; RightIdentity; Identity; Commutative; Associative)

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

lookupQuantity : TokenClass → Value → Quantity
lookupQuantity (c , t) v = fromMaybe 0 (lookup c (fromListᶜ v) >>= lookup t)

infix 5 _◇_
_◇_ : Value → TokenClass → Quantity
_◇_ = flip lookupQuantity

infix 4 _≥ᶜ_
_≥ᶜ_ : Value → Value → Bool
c ≥ᶜ c′ =
  and (map (λ{ ( k₁ , vs ) →
    and (map (λ{ (k₂ , v) → ⌊ lookupQuantity (k₁ , k₂) c ≥? v ⌋}) vs)}) c′)

infix 4 _≤ᶜ_
_≤ᶜ_ : Value → Value → Bool
_≤ᶜ_ = flip _≥ᶜ_


-------------------
-- Sum notation

∑ : ∀ {A : Set} → List A → (A → Value) → Value
∑ xs f = sumᶜ (map f xs)

∑∈ : ∀ {A : Set} →  (xs : List A) → (∀ {x} → x ∈ xs → Value) → Value
∑∈ xs f = sumᶜ (mapWith∈ xs f)

∑M : ∀ {A : Set} → List (Maybe A) → (A → Value) → Maybe Value
∑M xs f = (flip ∑ f) <$> seqM xs
  where
    -- if one fails everything fails
    seqM : ∀ {A : Set} → List (Maybe A) → Maybe (List A)
    seqM []       = just []
    seqM (x ∷ xs) = ⦇ x ∷ seqM xs ⦈


-------------------
-- _-contributesTo_

tokenClasses : Value → List TokenClass
tokenClasses []             = []
tokenClasses ((c , sv) ∷ v) = go sv ++ tokenClasses v
  where
    go : SubValue → List TokenClass
    go []                 = []
    go ((t , 0)     ∷ sv) = go sv
    go ((t , suc _) ∷ sv) = (c , t) ∷ go sv

_-contributesTo-_ : Rel Value 0ℓ
v′ -contributesTo- v = ¬ Disjoint (tokenClasses v′) (tokenClasses v)

_-contributesTo?-_ : Decidable _-contributesTo-_
v′ -contributesTo?- v = ¬? {!!} -- ¬? ((_∈? tokenClasses v′) ×-dec (_∈? tokenClasses v))

_∈ᶜ_ : TokenClass → Value → Set
nft ∈ᶜ v = v ◇ nft > 0

_∈?ᶜ_ : Decidable _∈ᶜ_
nft ∈?ᶜ v = v ◇ nft >? 0

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
  +ᶜ-comm  : Commutative _+ᶜ_
  +ᶜ-assoc : Associative _+ᶜ_
  +ᶜ-≡⇒≥ᶜ  : ∀ {x z w} → T $ x ≥ᶜ z +ᶜ w → T $ x ≥ᶜ w
  +ᶜ-≡⇒≤ᶜ : ∀ {v v₁ v₂} → v ≡ v₁ +ᶜ v₂ → T $ v₂ ≤ᶜ v

  -- Properties of _≥ᶜ_
  ≥ᶜ-refl  : ∀ v → T (v ≥ᶜ v)
  ≥ᶜ-trans : ∀ {x y z} → T (x ≥ᶜ y) → T (y ≥ᶜ z) → T (x ≥ᶜ z)
  ≥ᶜ-+ᶜ    : ∀ {x y z} → T (y ≥ᶜ z) → T (x +ᶜ y ≥ᶜ z)
  $0-≥ᶜ    : ∀ v → T ($0 ≥ᶜ v) → v ≡ $0

  -- Properties of ∑
  ∑-++ : ∀ {fv : A → Value}
    → ∑ (xs ++ ys) fv ≡ ∑ xs fv +ᶜ ∑ ys fv
  ∑-mapWith∈ : ∀ {fv : A → Value} {gv : B → A} {f : ∀ {x : A} → x ∈ xs → B}
    → (∀ {x} → (x∈ : x ∈ xs) → gv (f x∈) ≡ x)
    → ∑ (mapWith∈ xs f) (fv ∘ gv) ≡ ∑ xs fv
  ∑-filter : ∀ {P : A → Set} {q : (x : A) → Dec (P x)} {f : A → Value} {x y : Value}
    → x +ᶜ ∑ (filter q xs) f ≡ y +ᶜ ∑ xs f
    → x ≡ y +ᶜ ∑ (filter (¬? ∘ q) xs) f
  ∑-∘ : ∀ {xs : List A} {g : ∀ {x} → x ∈ xs → B} {g′ : B → C} {f : C → Value}
    → ∑ (mapWith∈ xs (g′ ∘ g)) f
    ≡ ∑ (mapWith∈ xs g) (f ∘ g′)
  ∑-++-≥ᶜ : ∀ {fv : A → Value} {v₁ v₂ : Value} {xs ys : List A}
    → T $ ∑ xs fv ≥ᶜ v₁
    → T $ ∑ ys fv ≥ᶜ v₂
    → T $ ∑ (xs ++ ys) fv ≥ᶜ v₁ +ᶜ v₂
  ∑-≥ᶜ : ∀ {x : A} {xs : List A} {fv : A → Value}
    → x ∈ xs
    → T $ ∑ xs fv ≥ᶜ fv x
  ∑filter : ∀ {P : Value → Set} {xs : List (∃ P)} {v : Value}
    → T $ ∑ xs proj₁ ≥ᶜ v
    → T $ ∑ (filter ((_-contributesTo?- v) ∘ proj₁) xs) proj₁ ≥ᶜ v

  -- Properties of ∑M
  ∑M-just : ∀ {m : A → Maybe B} {f : B → Value} {g : ∀ {x} → x ∈ xs → B}
    → (∀ {x} (x∈ : x ∈ xs) → m x ≡ just (g {x} x∈))
    → ∑M (map m xs) f ≡ just (∑ (mapWith∈ xs g) f)

  -- Properties from Data.AVL.Properties
  toListᵛ∘fromListᵛ : toListᵛ (fromListᵛ v) ≡ v
  unionWith-identityʳ : ∀ {f : B → Maybe B → B} → unionWith f m empty ≡ mapᵛ (λ x → f x nothing) m
  mapᵛ-id           : ∀ {f : B → B} → (∀ {x} → f x ≡ x) → mapᵛ f m ≡ m

  -- Properties of UTxO.Value.mapᶜ
  mapᵛ-fromListᵛ      : ∀ {f : A → B} → mapᵛ f (fromListᵛ v) ≡ fromListᵛ (mapᶜ f v)
  mapᶜ∘mapᶜ         : ∀ {g : A → B} {f : B → C} → (mapᶜ f ∘ mapᶜ g) v ≡ mapᶜ (f ∘ g) v
  mapᶜ-id          : ∀ {f : A → A} → (∀ {x} → f x ≡ x) → mapᶜ f v ≡ v


module FocusTokenClass (tk : TokenClass) where

  _◆ : Value → Quantity
  _◆ = lookupQuantity tk

  1◆   = singleToken tk
  ◆∈_  = tk ∈ᶜ_
  ◆∈?_ = tk ∈?ᶜ_

  -- Properties of focusing values (lookupQuantity/_◇_/_◆)
  postulate
    +ᶜ-◆ : ∀ {x y} → (x +ᶜ y) ◆ ≡ x ◆ + y ◆
    ≥ᶜ-◆ : ∀ {x y} → T $ x ≥ᶜ y → x ◆ ≥ y ◆
    ◆-+ᶜ-reject : ∀ {v vs} → ¬ ◆∈ v → (v +ᶜ vs) ◆ ≡ vs ◆
    ∑◆≤1⇒count≤1 : ∀ {vs} → (sumᶜ vs) ◆ ≤ 1 → count ◆∈?_ vs ≤ 1
    ◆-≤-weaken : ∀ {v vs n} → (v +ᶜ vs) ◆ ≤ (suc n) → ◆∈ v → vs ◆ ≤ n
    ∑◆≡0⇒count≡0 : ∀ {vs} → sumᶜ vs ◆ ≡ 0 → count ◆∈?_ vs ≡ 0
    ◆-currencies∈ : ∀ {v} → ◆∈ v → proj₁ tk ∈ currencies v
    ◆>0⇒◆∈ : ∀ {v n} → v ◆ ≥ n → n > 0 → ◆∈ v
    ◆-≥ : ∀ {v v′} → v ◆ ≥ v′ ◆ → ◆∈ v′ → ◆∈ v
    ≡0⇒◆∉ : ∀ {v} → v ◆ ≡ 0 → ¬ ◆∈ v
    ◆-single : ∀ {n} → [ proj₁ tk , [ proj₂ tk , n ] ] ◆ ≡ n

    ∑-◆ : ∀ {xs : List A} {f : A → Value}
      → ∑ xs f ◆ ≡ ∑ℕ (map (_◆ ∘ f) xs)

    ∑-mapMaybe : ∀ {X : Set} {xs : List A} {fm : A → Maybe X} {g : A → Value} {fv : X → Quantity}
      → (∀ x → Is-nothing (fm x) → g x ◆ ≡ 0)
      → (∀ x v → fm x ≡ just v → g x ◆ ≡ fv v)
      → ∑ℕ (map (_◆ ∘ g) xs) ≡ ∑ℕ (map fv $ mapMaybe fm xs)

    ∑-filter-◆ : ∀ {xs : List A} {fv : A → Value}
      → ∑ (filter (◆∈?_ ∘ fv) xs) fv ◆
      ≡ ∑ xs fv ◆

≥ᶜ-refl′ : ∀ {v v′}
  → v ≡ v′
  → T $ v ≥ᶜ v′
≥ᶜ-refl′ {v} refl = ≥ᶜ-refl v

toListᶜ∘fromListᶜ : ∀ {v} → toListᶜ (fromListᶜ v) ≡ v
toListᶜ∘fromListᶜ {v}
  rewrite mapᵛ-fromListᵛ {v = mapᶜ fromListᵛ v} {f = toListᵛ}
        | mapᶜ∘mapᶜ {v = v} {g = fromListᵛ} {f = toListᵛ}
        | mapᶜ-id {v = v} {f = toListᵛ ∘ fromListᵛ} toListᵛ∘fromListᵛ
        | toListᵛ∘fromListᵛ {v = v}
        = refl

unionWith-empty-id : ∀ {m : Map A} {f : A → Maybe A → A}
  → (∀ {x} → f x nothing ≡ x)
  → unionWith f m empty ≡ m
unionWith-empty-id {m = m} {f = f} f≡
  rewrite unionWith-identityʳ {m = m} {f = f}
        | mapᵛ-id {m = m} {f = λ x → f x nothing} f≡
        = refl

x+ᶜ′0≡x : ∀ {m} → m +ᵛ′ empty ≡ m
x+ᶜ′0≡x {m} rewrite unionWith-empty-id {m = m} {f = λ v v′ → v + fromMaybe 0 v′} (λ {x} → +-identityʳ x)
                  = refl

+ᶜ-identityˡ : LeftIdentity $0 _+ᶜ_
+ᶜ-identityˡ v = toListᶜ∘fromListᶜ {v = v}

+ᶜ-identityʳ : RightIdentity $0 _+ᶜ_
+ᶜ-identityʳ v rewrite unionWith-empty-id {m = fromListᶜ v} {f = λ v v′ → v +ᵛ′ fromMaybe empty v′} x+ᶜ′0≡x
                 | toListᶜ∘fromListᶜ {v = v}
                 = refl

+ᶜ-identity : Identity $0 _+ᶜ_
+ᶜ-identity = +ᶜ-identityˡ , +ᶜ-identityʳ

sum-single : ∀ {v} → sumᶜ [ v ] ≡ v
sum-single {v} rewrite +ᶜ-identityʳ v = refl

x+ᶜy+ᶜ0≡x+ᶜy+0 : ∀ {x y} → x +ᶜ (y +ᶜ $0) ≡ x +ᶜ y +ᶜ $0
x+ᶜy+ᶜ0≡x+ᶜy+0 {x} {y}
  rewrite +ᶜ-identityʳ y
        | +ᶜ-identityʳ (x +ᶜ y)
        = refl

∑M≡just : ∀ {x : A} {mx : Maybe A} {P : A → Set}
 → mx ≡ just x
 → M.Any P mx
 → P x
∑M≡just refl (M.just p) = p

∑M-[] : ∀ {f : A → Value}
  → ∑M [] f ≡ just $0
∑M-[] = refl

drop₂ : ∀ {P Q : A → Set}
  → ∃[ v ] (P v × Q v)
  → ∃[ v ] Q v
drop₂ (v , _ , q) = v , q

drop₃ : ∀ {P Q : A → Set}
  → ∃[ v ] (P v × Q v)
  → ∃[ v ] P v
drop₃ (v , p , _) = v , p

postulate
  ∑M-help : ∀ {xs : List A}
              {f : A → Maybe B}
              {g : B → Value}
              {R : Set}
              {go : ∀ {x} → x ∈ xs → R}
              {r : R → Value}
    → (∀ {x} → (x∈ : x ∈ xs) → (g <$> f x) ≡ just (r $ go x∈))
    → ∑M (map f xs) g ≡ just (∑ (mapWith∈ xs go) r)

-- ∑prevs≡ : ∀ {tx l} (vl : ValidLedger l) (vtx : IsValidTx tx l)
--         → ∑M (map (getSpentOutput l) (inputs tx)) value ≡ just (∑ (prevs vl vtx) resValue)
{-
∑prevs-∷ : ∀ {tx l} {vl : ValidLedger l} {vtx : IsValidTx tx l}
  → inputs tx ≡ i ∷ is
  → ∑ (prevs vl vtx) resValue ≡ ? ∷ ?
∑prevs-∷ refl = refl

∑prevs≡ {tx@(record {inputs = []})}     {l} vl vtx = refl
∑prevs≡ {tx@(record {inputs = i ∷ is})} {l} vl vtx
  with getSpentOutput l i | preservesValues vtx
... | nothing | ()
... | just _  | _ = {!!}
-}


{-
  ∑M-help : ∀ {H : Value → Set} {xs : List A} {f : A → Maybe B} {g : B → Value}
    → (p : ∀ {x} → x ∈ xs → ∃[ v ] ( H v
                                 × ((g <$> f x) ≡ just v) ))
    → ∑M (map f xs) g ≡ just (∑ (mapWith∈ xs (drop₃ ∘ p)) proj₁)
  ∑M-help {xs = []}     {f = f} {g} p = refl
  ∑M-help {xs = x ∷ xs} {f = f} {g} p
    with p {x} (here refl)
  ... | v , hv , gfx≡
    with f x | gfx≡
  ... | nothing | ()
  ... | just fx | refl

    rewrite ∑M-help {xs = xs} {f = f} {g} (p ∘ there)
    = {!cong (v +ᶜ_) ?!}

    = begin
        ∑M (map f (x ∷ xs)) g
      ≡⟨ {!!} ⟩
      --   ((v +ᶜ_) <$> ∑M (map f xs) g)
      -- ≡⟨ ? ⟩
      --   ((v +ᶜ_) <$> just (∑ (mapWith∈ xs (drop₃ ∘ p)) proj₁))
      -- ≡⟨ ? ⟩
        just (∑ (mapWith∈ (x ∷ xs) (drop₃ ∘ p)) proj₁)
      ∎ where open ≡-Reasoning
-}
