------------------------------------------------------------------------
-- List utilities
------------------------------------------------------------------------

module Utilities.Lists where

open import Function      using (_∋_; case_of_)
open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (⊤; tt)
open import Data.Maybe    using (Maybe; just; nothing)
open import Data.Fin      using (Fin; toℕ; fromℕ≤; inject≤)
  renaming (zero to fzero; suc to fsuc)
open import Data.Nat      using (ℕ; zero; suc; _≤_; z≤n; s≤s; pred)
open import Data.Nat.Properties using (suc-injective)
open import Data.List     using (List; []; [_]; _∷_; map; sum; length; upTo; lookup)
open import Data.List.Properties using (length-map)

open import Relation.Nullary.Decidable using (True)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

------------------------------------------------------------------------
-- Sums.

Σ-sum-syntax : ∀ {A : Set} → (A → ℕ) → List A → ℕ
Σ-sum-syntax f xs = sum (map f xs)
syntax Σ-sum-syntax f xs = Σ[ f ∈ xs ]

------------------------------------------------------------------------
-- Indexed operations.

Index : ∀ {A : Set} → (xs : List A) → Set
Index xs = Fin (length xs)

infix 3 _‼_
_‼_ : ∀ {A : Set} → (vs : List A) → Index vs → A
_‼_ = lookup

infix 3 _⁉_
_⁉_ : ∀ {A : Set} → (vs : List A) → ℕ → Maybe A
[]       ⁉ _     = nothing
(x ∷ xs) ⁉ zero  = just x
(x ∷ xs) ⁉ suc n = xs ⁉ n

remove : ∀ {A : Set} → (vs : List A) → Index vs → List A
remove []       ()
remove (_ ∷ xs) fzero    = xs
remove (x ∷ vs) (fsuc f) = x ∷ remove vs f

_at_⟨_⟩ : ∀ {A : Set} → (vs : List A) → Index vs → A → List A
[]       at ()       ⟨ _ ⟩
(_ ∷ xs) at fzero    ⟨ x ⟩ = x ∷ xs
(y ∷ vs) at (fsuc f) ⟨ x ⟩ = y ∷ (vs at f ⟨ x ⟩)

_at_⟨_⟩remove_ : ∀ {A : Set} → (vs : List A) → Index vs → A → Index vs → List A
[] at () ⟨ _ ⟩remove ()
(_ ∷ vs) at fzero  ⟨ _  ⟩remove fzero  = vs
(_ ∷ vs) at fzero  ⟨ xv ⟩remove fsuc y = xv ∷ remove vs y
(_ ∷ vs) at fsuc x ⟨ xv ⟩remove fzero  = vs at x ⟨ xv ⟩
(v ∷ vs) at fsuc x ⟨ xv ⟩remove fsuc y = v ∷ vs at x ⟨ xv ⟩remove y

indices : ∀ {A : Set} → List A → List ℕ
indices xs = upTo (length xs)

cast : ∀ {m n} → .(_ : m ≡ n) → Fin m → Fin n
cast {zero}  {zero}  eq k        = k
cast {suc m} {suc n} eq fzero    = fzero
cast {suc m} {suc n} eq (fsuc k) = fsuc (cast (cong pred eq) k)
cast {zero}  {suc n} ()
cast {suc m} {zero}  ()

just-injective : ∀ {A : Set} {x y} → (Maybe A ∋ just x) ≡ just y → x ≡ y
just-injective refl = refl

toℕ-cast : ∀ {n m} {fm : Fin m}
         → (eq : m ≡ n)
         → toℕ (cast eq fm) ≡ toℕ fm
toℕ-cast {_} {_} {fzero}   refl = refl
toℕ-cast {_} {_} {fsuc fm} refl = cong suc (toℕ-cast refl)

‼-suc : ∀ {A} {x : A} {xs : List A} {i : Index xs}
  → (x ∷ xs ‼ fsuc i)
  ≡ (xs ‼ i)
‼-suc = refl

‼-map : ∀ {A B} {f : A → B} {xs : List A} {i : Index xs}
  → (map f xs ‼ cast (sym (length-map f xs)) i)
  ≡ f (xs ‼ i)
‼-map {A} {B} {f} {[]} {()}
‼-map {A} {B} {f} {x ∷ xs} {fzero} = refl
‼-map {A} {B} {f} {x ∷ xs} {fsuc i}
  rewrite ‼-suc {A} {x} {xs} {i}
        = ‼-map {A} {B} {f} {xs} {i}

‼→⁉ : ∀ {A} {xs : List A} {ix : Index xs}
    → just (xs ‼ ix) ≡ (xs ⁉ toℕ ix)
‼→⁉ {_} {[]}     {()}
‼→⁉ {_} {x ∷ xs} {fzero}   = refl
‼→⁉ {A} {x ∷ xs} {fsuc ix} = ‼→⁉ {A} {xs} {ix}

⁉→‼ : ∀ {A} {xs ys : List A} {ix : Index xs}
    → (len≡ : length xs ≡ length ys)
    → (xs ⁉ toℕ ix) ≡ (ys ⁉ toℕ ix)
    → (xs ‼ ix) ≡ (ys ‼ cast len≡ ix)
⁉→‼ {A} {[]}     {[]}      {ix}      len≡ eq   = refl
⁉→‼ {A} {[]}     {x ∷ ys}  {ix}      () eq
⁉→‼ {A} {x ∷ xs} {[]}      {ix}      () eq
⁉→‼ {A} {x ∷ xs} {.x ∷ ys} {fzero}   len≡ refl = refl
⁉→‼ {A} {x ∷ xs} {y ∷ ys}  {fsuc ix} len≡ eq
  rewrite ‼-suc {A} {x} {xs} {ix}
        = ⁉→‼ {A} {xs} {ys} {ix} (suc-injective len≡) eq

-- ‼-≡ : ∀ {A} {l r : List A} {iₗ : Index l} {iᵣ : Index r}
--     → l ≡ r
--     → toℕ iₗ ≡ toℕ iᵣ
--     → (Maybe A ∋ just (l ‼ iₗ)) ≡ (Maybe A ∋ just (r ‼ iᵣ))
-- ‼-≡ {A} {l} {r} {il} {ir} refl to≡
--   rewrite -- just-injective {x = l ‼ il} {y = r ‼ ir}
--           ‼→⁉ {A} {l} {il}
--         | ‼→⁉ {A} {r} {ir}
--         = {!!}

------------------------------------------------------------------------
-- Prefix relation.
-- (T0D0: upgrade stdlib and get from Data.List.Relation.Binary.Prefix)

data Prefix {A : Set} : List A → List A → Set where
  []  : ∀ {bs} → Prefix [] bs
  _∷_ : ∀ {as bs} → (a : A) → Prefix as bs → Prefix (a ∷ as) (a ∷ bs)

prefix-length : ∀ {A} {as bs : List A} → Prefix as bs → length as ≤ length bs
prefix-length []       = z≤n
prefix-length (r ∷ rs) = s≤s (prefix-length rs)
