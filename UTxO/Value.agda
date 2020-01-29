------------------------------------------------------------------------
-- No multi-currency support.
------------------------------------------------------------------------
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import UTxO.Hashing.Base

module UTxO.Value
  (Address : Set)
  (_♯ₐ : Hash Address)
  (_≟ₐ_ : Decidable {A = Address} _≡_)
  where

open import Data.Bool using (Bool)
open import Data.List using (List; sum;[];_∷_)
open import Data.Nat  using (ℕ) renaming(_+_ to _+ℕ_)
  renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (_≥?_)
open import Data.Product using (_×_;_,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes;no)
open import Relation.Nullary.Decidable            using (⌊_⌋;True)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List.Relation.Unary.Any using (here;there)
open import Data.List.Membership.Propositional using (_∈_; mapWith∈)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Maybe using (Maybe;maybe;fromMaybe;just;nothing;_>>=_)
open import Function using (id)

Value = ℕ -- synomy for Quantity?

$0 : Value
$0 = 0

$ : ℕ → Value
$ v = v

_+ᶜ_ : Value → Value → Value
_+ᶜ_ = _+ℕ_

sumᶜ : List Value → Value
sumᶜ = sum

infix 4 _≟ᶜ_
_≟ᶜ_ : Decidable {A = Value} _≡_
_≟ᶜ_ = _≟ℕ_

_≥ᶜ_ : Value → Value → Bool
v ≥ᶜ v′ = ⌊ v ≥? v′ ⌋

Token : Set
Token = Address

-- a rough approximation of a map/finitely supported function

Quantities : Set
Quantities = List (Token × Value)

-- this version of + throws away anything that doesn't match exactly

_+_ : Quantities → Quantities → Quantities
[]                + []                   = []
[]                + (_ ∷ _)              = []
(_ ∷ _)           + []                   = []
((tok , val) ∷ q) + ((tok' , val') ∷ q') with tok ≟ₐ tok'
... | yes p = (tok , val +ℕ val') ∷ q + q'
... | no ¬p = q + q'

∑∈ : {X : Set}(xs : List X) → ((x : X) → x ∈ xs → Quantities) → Quantities 
∑∈ []       f = []
∑∈ (i ∷ is) f = f i (here refl) + ∑∈ is λ i p → f i (there p)

∑ : {X : Set}(xs : List X) → ((x : X) → Quantities) → Quantities 
∑ []       f = []
∑ (i ∷ is) f = f i + ∑ is f

-- unit on failure
∑M' : {X : Set}(xs : List X) → ((x : X) → Maybe Quantities) → Quantities 
∑M' []       f = []
∑M' (i ∷ is) f = fromMaybe [] (f i) + ∑M' is f

-- if one fails everything fails
∑M : {X : Set}(xs : List X) → ((x : X) → Maybe Quantities) → Maybe Quantities 
∑M []       f = just []
∑M (i ∷ is) f = f i >>= λ q → ∑M is f >>= λ qs → just (q + qs)


_≥_ : Quantities → Value → Set
[]      ≥ v′ = ⊥
((_ , v) ∷ Q) ≥ v′ = True (v ≥? v′) × Q ≥ v′

_≟_ : Decidable {A = Quantities} _≡_
[]                 ≟ []                    = yes refl
[]                 ≟ (_ ∷ qs)              = no λ ()
(_ ∷ qs)           ≟ []                    = no λ ()
((tok , val) ∷ qs) ≟ ((tok' , val') ∷ qs')
  with tok ≟ₐ tok' | val ≟ᶜ val' | qs ≟ qs' 
... | no ¬p    | _        | _        = no λ{refl → ¬p refl}
... | yes p    | no ¬q    | r        = no λ{refl → ¬q refl}
... | yes p    | yes q    | no ¬r    = no λ{refl → ¬r refl}
... | yes refl | yes refl | yes refl = yes refl
