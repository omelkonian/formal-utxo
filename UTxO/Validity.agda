module UTxO.Validity where

open import Function using (_∘_; flip)

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

open import Data.List.Relation.Unary.Any as L              using (Any; any)
open import Data.List.Relation.Unary.All                   using (All; all)
open import Data.List.Membership.Propositional             using (_∈_;mapWith∈)
open import Data.List.Relation.Unary.Unique.Propositional  using (Unique)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)

open import Data.Maybe.Relation.Unary.Any as M using ()
  renaming (dec to any?)

open import Relation.Nullary                      using (Dec; ¬_; yes; no)
open import Relation.Nullary.Product              using (_×-dec_)
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
      outputRefs tx ⊆ map outRef (utxo l)

    preservesValues :
      M.Any (λ q → forge tx +ᶜ q ≡ fee tx +ᶜ ∑ (outputs tx) value)
            (∑M (map (getSpentOutput l) (inputs tx)) value)

    noDoubleSpending :
      Unique (outputRefs tx)

    allInputsValidate :
      All (λ{ (n , i) → T (validator i (toPendingTx l tx n) (redeemer i) (datum i)) })
          (enumerate (inputs tx))

    allPoliciesValidate :
      All (λ f → T (f (toPendingMPS l tx (f ♯))))
          (policies tx)

    validateValidHashes :
      All (λ i → M.Any (λ o → (address o ≡ validator i ♯) × (datumHash o ≡ datum i ♯ᵈ)) (getSpentOutput l i))
          (inputs tx)

    forging :
      All (λ c → Any (λ f → c ≡ f ♯) (policies tx))
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
  → {vor : True (outputRefs tx SETₒ.⊆? map outRef (utxo l))}
  → {pv  : True (any? (λ q → forge tx +ᶜ q ≟ᶜ fee tx +ᶜ ∑ (outputs tx) value)
                      (∑M (map (getSpentOutput l) (inputs tx)) value))}
  → {ndp : True (SETₒ.unique? (outputRefs tx))}
  → {aiv : True (all (λ{ (n , i) → T? (validator i (toPendingTx l tx n) (redeemer i) (datum i))})
                     (enumerate (inputs tx)))}
  → {apv : True (all (λ f → T? (f (toPendingMPS l tx (f ♯))))
                     (policies tx))}
  → {vvh : True (all (λ i → any? (λ o → (address o ≟ℕ validator i ♯) ×-dec (datumHash o ≟ℕ datum i ♯ᵈ))
                                 (getSpentOutput l i))
                     (inputs tx))}
  → {frg : True (all (λ c → any (λ f → c ≟ℕ f ♯) (policies tx))
                     (currencies (forge tx)))}
  → ValidLedger (tx ∷ l)
(vl ⊕ tx) {wi} {vor} {pv} {ndp} {aiv} {apv} {vvh} {frg}
  = vl ⊕ tx ∶- record { withinInterval      = toWitness wi
                      ; validOutputRefs     = toWitness vor
                      ; preservesValues     = toWitness pv
                      ; noDoubleSpending    = toWitness ndp
                      ; allInputsValidate   = toWitness aiv
                      ; allPoliciesValidate = toWitness apv
                      ; validateValidHashes = toWitness vvh
                      ; forging             = toWitness frg }
