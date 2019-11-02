------------------------------------------------------------------------
-- Naive hashing functions for UTxO types.

-- NB: uses meta-programming to be able to hash values of any type, by:
--     1. Quoting the given expression to get a `Term`
--     2. Showing the term to get a `String`
--     3. Naively converting the string to a number
--
-- EDIT: Does not work, since meta-programs are restricted to 2 stages..
------------------------------------------------------------------------
module UTxO.Hashing.MetaHash where

open import Function      using (_∘_)
open import Data.Unit     using (⊤)
open import Data.Bool     using (Bool; true; false)
open import Data.Product  using (_×_; _,_)
open import Data.List     using (List; []; _∷_; _∷ʳ_; [_]; length; sum; map)
open import Data.Nat      using (ℕ; _+_; _*_; _∸_; suc)
open import Data.Nat.Show using (show)
open import Data.Fin      using (toℕ)
open import Data.String   using (String; toList; _++_)
open import Data.Char     using (Char; toNat)

open import Relation.Binary.PropositionalEquality using (_≡_)

open import Reflection

open import UTxO.Hashing.Base


Show : Set → Set
Show A = A → String

infixl 20 _◇_
_◇_ : String → String → String
s ◇ s′ = s ++ " " ++ s′

showList : ∀ {A : Set} → Show A → Show (List A)
showList showA []       = ""
showList showA (x ∷ xs) = showA x ◇ showList showA xs

showRelevance : Show Relevance
showRelevance relevant   = "relevant"
showRelevance irrelevant = "irrelevant"

showVisibility : Show Visibility
showVisibility visible   = "visible"
showVisibility hidden    = "hidden"
showVisibility instance′ = "instance"

showArg : ∀ {A : Set} → Show A → Show (Arg A)
showArg showA (arg (arg-info v r) x) = "arg" ◇ showVisibility v ◇ showRelevance r ◇ showA x

showPat : Show Pattern
showClause : Show Clause
showSort : Show Sort
showTerm : Show Term

showPats : Show (List (Arg Pattern))
showPats = showList (showArg showPat)

showArgs : Show (List (Arg Term))
showArgs = showList (showArg showTerm)

{-# TERMINATING #-}
showPat (con c ps) = "con" ◇ showName c ◇ showPats ps
showPat dot        = "dot"
showPat (var s)    = "var" ◇ s
showPat (lit l)    = "lit" ◇ showLiteral l
showPat (proj f)   = "proj" ◇ showName f
showPat absurd     = "absurd"

{-# TERMINATING #-}
showTerm (var x args)      = "var" ◇ show x ◇ showArgs args
showTerm (con c args)      = "con" ◇ showName c ◇ showArgs args
showTerm (def f args)      = "def" ◇ showName f ◇ showArgs args
showTerm (lam v (abs s e)) = "lam" ◇ showVisibility v ◇ "abs" ◇ s ◇ showTerm e
showTerm (pat-lam cs args) = "pat-lam" ◇ showList showClause cs ◇ showArgs args
showTerm (pi e (abs s e′)) = "pi" ◇ showArg showTerm e ◇ "abs" ◇ s ◇ showTerm e′
showTerm (sort s)          = "sort" ◇ showSort s
showTerm (lit l)           = showLiteral l
showTerm (meta m es)       = "meta" ◇ showMeta m ◇ showList (showArg showTerm) es
showTerm unknown           = "_"

showSort (set t) = showTerm t
showSort (lit n) = show n
showSort unknown = "_"

showClause (clause ps t)      = "clause" ◇ showPats ps ◇ showTerm t
showClause (absurd-clause ps) = "absurd-clause" ◇ showPats ps

-- Finally, the meta hashing function.

-- macro
--   metaHash : Term → Term → TC ⊤
--   metaHash (var n []) hole = do
--     ctx ← getContext
--     typeError [ strErr (show n) ]
--   metaHash t          _    = typeError [ termErr t ]
-- ← getDefinition
-- do `s ← quoteTC (showTerm t)
--    unify hole `s

-- !!! DOES NOT WORK, I need runtime reflection :(
-- _♯ : ∀ {ℓ} {A : Set ℓ} → Hash A
-- x ♯ = (metaHash x) ♯ₛₜᵣ

postulate
  _♯ : ∀ {ℓ} {A : Set ℓ} → Hash A
  ♯-injective : ∀ {ℓ} {A : Set ℓ} → Injective {ℓ} {A} _♯
