module UTxO.Validity where

open import Function using (_∘_)

open import Data.Sum             using (_⊎_)
open import Data.Product         using (_×_; _,_; proj₁)
open import Data.Maybe           using (Maybe;Is-just)
  renaming (map to _<$>_)
open import Data.Bool            using (T; true)
open import Data.Bool.Properties using (T?)
open import Data.Nat             using (ℕ; zero; suc; _<_)
  renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties  using (suc-injective)
open import Data.Fin             using (Fin; toℕ; fromℕ<)
open import Data.List            using (List; []; _∷_; map; length)

open import Data.List.Relation.Unary.Any as L             using (Any; any)
open import Data.List.Relation.Unary.All                  using (All; all)
open import Data.List.Membership.Propositional            using (_∈_;mapWith∈)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.Maybe.Relation.Unary.Any as M                 using (Any;drop-just;map)

open import Data.Maybe.Relation.Unary.All using () renaming (dec to all?)
open import Data.Maybe.Relation.Unary.Any using () renaming (dec to any?)

open import Relation.Nullary                      using (Dec; ¬_; yes; no)
open import Relation.Nullary.Decidable            using (True; toWitness)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists using (enumerate)

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types
open import UTxO.TxUtilities

-- The definitions here make use of `All` for lists, i.e. that every
-- element in a list satisifies a particular property and `AllN` which
-- gives the predicate access to the position of the element in the
-- list ass well as the element itself.

-- Additionally we make use of `M.Any`. `Any` and `All` for `Maybe` are
-- analogous to the same notions for lists. We can consider a `Maybe` as
-- a zero or one element list. `Any` gives us the notion of a property
-- that holds when we have a `just`, it cannot hold when we have
-- `nothing`. In contrast `All` for Maybe holds vacuously for nothing.

record IsValidTx (tx : Tx) (l : Ledger) {- (vl : ValidLedger l) -} : Set where
  field
    withinInterval :
      T (range tx ∋ length l)

    validOutputRefs :
      All (λ i → outputRef i ∈ map outRef (utxo l))
          (inputs tx)

    preservesValues :
      M.Any (λ q → forge tx +ᶜ q ≡ fee tx +ᶜ ∑ (outputs tx) value)
            (∑M (inputs tx) (λ i → value <$> getSpentOutput i l))

    noDoubleSpending :
      Unique (outputRefs tx)

    allInputsValidate :
      All (λ{ (n , i) → T (validator i (toPendingTx l tx n) (redeemer i) (dataVal i)) })
          (enumerate (inputs tx))

    validateValidHashes :
      All (λ i → M.Any ((validator i ♯ ≡_) ∘ address) (getSpentOutput i l))
          (inputs tx)

    forging :
      All (λ c → Any (λ i → M.Any ((c ≡_) ∘ address) (getSpentOutput i l)) (inputs tx))
          (currencies (forge tx))

open IsValidTx public

data ValidLedger : Ledger → Set where

  ∙ : ValidLedger []

  _⊕_∶-_ : ∀ {l}
    → ValidLedger l
    → (t : Tx)
    → IsValidTx t l
      -------------------
    → ValidLedger (t ∷ l)

infixl 5 _⊕_∶-_

----------------------
-- Decision Procedure.

infixl 5 _⊕_
_⊕_ : ∀ {l}
  → ValidLedger l
  → (tx : Tx)
  → {wi  : True (T? (range tx ∋ length l))}
  → {vor : True (all (λ i → outputRef i SETₒ.∈? map outRef (utxo l)) (inputs tx))}
  → {pv  : True (any? (λ q → forge tx +ᶜ q ≟ᶜ fee tx +ᶜ ∑ (outputs tx) value)
                      (∑M (inputs tx) (λ i → value <$> getSpentOutput i l)))}
  → {ndp : True (SETₒ.unique? (outputRefs tx))}
  → {aiv : True (all (λ{ (n , i) → T? (validator i (toPendingTx l tx n) (redeemer i) (dataVal i))})
                     (enumerate (inputs tx)))}
  → {vvh : True (all (λ i → any? ((validator i ♯ ≟ℕ_) ∘ address) (getSpentOutput i l))
                     (inputs tx))}
  → {frg : True (all (λ c → any (λ i → any? ((c ≟ℕ_) ∘ address) (getSpentOutput i l)) (inputs tx))
                     (currencies (forge tx)))}
  → ValidLedger (tx ∷ l)
(vl ⊕ tx) {wi} {vor} {pv} {ndp} {aiv} {vvh} {frg}
  = vl ⊕ tx ∶- record { withinInterval      = toWitness wi
                      ; validOutputRefs     = toWitness vor
                      ; preservesValues     = toWitness pv
                      ; noDoubleSpending    = toWitness ndp
                      ; allInputsValidate   = toWitness aiv
                      ; validateValidHashes = toWitness vvh
                      ; forging             = toWitness frg }

{-
open import Data.Unit

-- below is an incomplete attempt to prove the following: if `validOutputRefs` is
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
  -- if `validOutputRefs` is satisfied
  → All (λ i → outputRef i ∈ map outRef (utxo l)) is
  -- all inputs refer to legit outputs from the ledger
  → All (λ i → Is-just (getSpentOutput i l)) is
scopeSafe l vl [] All.[] = All.[]
scopeSafe l vl (i ∷ is) (px All.∷ pxs) =
  scopeSafeLem l vl i px All.∷ scopeSafe l vl is pxs
-}
