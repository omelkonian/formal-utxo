------------------------------------------------------------------------
-- List utilities
------------------------------------------------------------------------

module Utilities.Lists where

open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (⊤; tt)
open import Data.List using (List; []; [_]; _∷_; map; sum; length)
open import Data.Nat  using (ℕ; _<?_)
open import Data.Fin           using (Fin)
  renaming (zero to fzero; suc to fsuc)

open import Relation.Nullary.Decidable using (True)

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
[]     ‼ ()
x ∷ _  ‼ fzero    = x
_ ∷ vs ‼ (fsuc f) = vs ‼ f

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
