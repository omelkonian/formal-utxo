------------------------------------------------------------------------
-- List utilities
------------------------------------------------------------------------

module Utilities.Lists where

open import Function      using (_∋_; case_of_)
open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (⊤; tt)
open import Data.Product  using (_×_)
open import Data.Maybe    using (Maybe; just; nothing)
open import Data.Fin      using (Fin; toℕ; fromℕ≤; inject≤)
  renaming (zero to fzero; suc to fsuc)
open import Data.Nat      using (ℕ; zero; suc; _≤_; z≤n; s≤s; pred)
open import Data.Nat.Properties using (suc-injective)
open import Data.List.Properties using (length-map)

open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import Data.List public
  using (List; []; [_]; _∷_; _∷ʳ_; map; concatMap; length; sum; upTo; lookup)
open import Data.List.Membership.Propositional using (_∈_)

------------------------------------------------------------------------
-- Indexed operations.

Index : ∀ {ℓ} {A : Set ℓ} → (xs : List A) → Set
Index xs = Fin (length xs)

infix 3 _‼_
_‼_ : ∀ {ℓ} {A : Set ℓ} → (vs : List A) → Index vs → A
_‼_ = lookup

infix 3 _⁉_
_⁉_ : ∀ {ℓ} {A : Set ℓ} → (vs : List A) → ℕ → Maybe A
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

indices : ∀ {ℓ} {A : Set ℓ} → List A → List ℕ
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

‼-suc : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} {i : Index xs}
  → (x ∷ xs ‼ fsuc i)
  ≡ (xs ‼ i)
‼-suc = refl

‼-map : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} {xs : List A} {i : Index xs}
  → (map f xs ‼ cast (sym (length-map f xs)) i)
  ≡ f (xs ‼ i)
‼-map {_} {_} {A} {B} {f} {[]} {()}
‼-map {_} {_} {A} {B} {f} {x ∷ xs} {fzero} = refl
‼-map {_} {_} {A} {B} {f} {x ∷ xs} {fsuc i}
  rewrite ‼-suc {_} {A} {x} {xs} {i}
        = ‼-map {_} {_} {A} {B} {f} {xs} {i}

‼→⁉ : ∀ {ℓ} {A : Set ℓ} {xs : List A} {ix : Index xs}
    → just (xs ‼ ix) ≡ (xs ⁉ toℕ ix)
‼→⁉ {_} {_} {[]}     {()}
‼→⁉ {_} {_} {x ∷ xs} {fzero}   = refl
‼→⁉ {_} {A} {x ∷ xs} {fsuc ix} = ‼→⁉ {_} {A} {xs} {ix}

⁉→‼ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} {ix : Index xs}
    → (len≡ : length xs ≡ length ys)
    → (xs ⁉ toℕ ix) ≡ (ys ⁉ toℕ ix)
    → (xs ‼ ix) ≡ (ys ‼ cast len≡ ix)
⁉→‼ {_} {A} {[]}     {[]}      {ix}      len≡ eq   = refl
⁉→‼ {_} {A} {[]}     {x ∷ ys}  {ix}      () eq
⁉→‼ {_} {A} {x ∷ xs} {[]}      {ix}      () eq
⁉→‼ {_} {A} {x ∷ xs} {.x ∷ ys} {fzero}   len≡ refl = refl
⁉→‼ {_} {A} {x ∷ xs} {y ∷ ys}  {fsuc ix} len≡ eq
  rewrite ‼-suc {_} {A} {x} {xs} {ix}
        = ⁉→‼ {_} {A} {xs} {ys} {ix} (suc-injective len≡) eq

