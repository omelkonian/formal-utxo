{-# OPTIONS --allow-unsolved-metas #-}
open import UTxO.Hashing.Base

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
--open import Data.List.Relation.Unary.Any          using (Any)
open import Data.List.Relation.Unary.All          using (All)
import Data.List.Relation.Unary.Any as L
open import Data.List.Membership.Propositional    using (_∈_;mapWith∈)
import Data.Maybe.Relation.Unary.Any as M         using (Any;drop-just;map)
open import Data.Sum                              using (_⊎_)
open import Data.Product                          using (proj₁)
open import Data.Maybe
  using (Maybe;Is-just) renaming (map to _<$>_)
open import Data.Bool                             using (true)
open import Relation.Nullary using (yes;no)
open import Data.Nat     using (ℕ; zero; suc; _<_) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (suc-injective)
open import Data.Fin     using (Fin; toℕ; fromℕ<)

module UTxO.MaybeValidity
  (Address : Set)
  (_♯ₐ : Hash Address)
  (_≟ₐ_ : Decidable {A = Address} _≡_)
  where

open import UTxO.Value       Address _♯ₐ _≟ₐ_
open import UTxO.Types       Address _♯ₐ _≟ₐ_
open import UTxO.Ledger      Address _♯ₐ _≟ₐ_
open import UTxO.Hashing.Tx  Address _♯ₐ _≟ₐ_
open import UTxO.TxUtilities Address _♯ₐ _≟ₐ_
open import UTxO.Hashing.MetaHash using (_♯)

open import Data.List     using (List;[]; _∷_; length; map; filter)

data ValidLedger : Ledger → Set

-- The definitions here make use of `All` for lists, i.e. that every
-- element in a list satisifies a particular property and `AllN` which
-- gives the predicate access to the position of the element in the
-- list ass well as the element itself.

-- Additionally we make use of `M.Any`. `Any` and `All` for `Maybe` are
-- analogous to the same notions for lists. We can consider a `Maybe` as
-- a zero or one element list. `Any` gives us the notion of a property
-- that holds when we have a `just`, it cannot hold when we have
-- `nothing`. In contrast `All` for Maybe holds vacuously for nothing.

record IsValidTx (tx : Tx) (l : Ledger)(vl : ValidLedger l) : Set where
  field
    -- prop1 : validityInterval

    prop2 : All (λ o → value o ≥ 0)                      (outputs tx)

    prop3 : All (λ i → outputRef i ∈ map outRef (utxo l)) (inputs tx)

    prop4 : forge tx ≥ 0 → l ≡ []

    prop5 :
      M.Any (λ q → forge tx + q ≡ fee tx + ∑ (outputs tx) value)
            (∑M (inputs tx) (λ i → value <$> getSpentOutput i l))

    prop6 : AllN (λ i n → validator i (toPendingTx l tx n) (redeemer i) (dataVal i) ≡ true) (inputs tx)

    prop7 : AllN (λ i n → validator i (toPendingTx l tx n) (dataVal i) (redeemer i) ≡ true) (inputs tx)

    prop8 : All (λ i → M.Any (λ o → validator i ♯ ≡ (address o ♯ₐ)) (getSpentOutput i l)) (inputs tx)

data ValidLedger where

  ∙ : ValidLedger []

  _⊕_∶-_ : ∀ {l}
         → (vl : ValidLedger l)
         → (t : Tx)
         → IsValidTx t l vl
         → ValidLedger (t ∷ l)

infixl 5 _⊕_∶-_

open import Data.Unit

-- below is an incomplete attempt to prove the following: if prop 3 is
-- satisfied then all the operations in the prop 5--8 that can fail,
-- won't.

-- if membership is satisfied then lookup cannot fail

just∈ : ∀{X}(x : X)(xs : List X)(p : x ∈ xs) → Is-just (xs [ toℕ (L.index p) ])
just∈ x .(_ ∷ _) (L.here px) = M.Any.just tt
just∈ x .(_ ∷ _) (L.there p) = just∈ x _ p

map∈ :  ∀{A B : Set} x (xs : List A)(f : ∀ {x} → x ∈ xs → B)
  → (p : x ∈ xs)
  → f p ∈ mapWith∈ xs f
map∈ x .(_ ∷ _) f (L.here refl) = L.here refl
map∈ x .(_ ∷ _) f (L.there p) = L.there (map∈ x _ (λ p → f (L.there p)) p)

-- if a output is a member of a list of outputs then its outputRef is
-- a member of the list of outputRefs

o2oref : ∀ tx (o : TxOutput) → (os : List TxOutput)
  → (p : o ∈ os)
  → (tx ♯ₜₓ) indexed-at toℕ (L.index p)
    ∈ mapWith∈ os (λ p → (tx ♯ₜₓ) indexed-at toℕ (L.index p))
o2oref tx o os p = map∈ o os (λ p → (tx ♯ₜₓ) indexed-at toℕ (L.index p)) p

scopeSafeIndex : ∀ tx (or : TxOutputRef) → (os : List TxOutput)
  → (p : or ∈ mapWith∈ os (λ p → (tx ♯ₜₓ) indexed-at toℕ (L.index p)))
  → Is-just (mapWith∈ os (λ p → (tx ♯ₜₓ) indexed-at toℕ (L.index p)) [ toℕ (L.index p) ])
scopeSafeIndex tx or os p = just∈ _ _ p

scopeSafeLem : (l : Ledger)(vl : ValidLedger l)(i : TxInput)
  → outputRef i ∈ map outRef (utxo l)
  → Is-just (getSpentOutput i l)
scopeSafeLem (tx ∷ l) vl i p with id (outputRef i) ≟ℕ tx ♯ₜₓ
-- does our output come from tx?
scopeSafeLem (tx ∷ l) vl i p | yes q = {!p!}
-- yes, so, it must be one of the ones that gets added
-- if our input points to the current tx, then looking it up by it's
-- index should work
scopeSafeLem (tx ∷ l) vl i p | no ¬q = {!!}
-- no, so it's the filtered utxo, which means its in the unfiltered
-- one for l

scopeSafe : (l : Ledger)(vl : ValidLedger l)(is : List TxInput)
  -- if prop3 is satisfied
  → All (λ i → outputRef i ∈ map outRef (utxo l)) is
  -- all inputs refer to legit outputs from the ledger
  → All (λ i → Is-just (getSpentOutput i l)) is
scopeSafe l vl [] All.[] = All.[]
scopeSafe l vl (i ∷ is) (px All.∷ pxs) =
  scopeSafeLem l vl i px All.∷ scopeSafe l vl is pxs
