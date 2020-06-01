module UTxO.Validity where

open import Level    using (0ℓ)
open import Function using (_∘_; flip; _$_)

open import Data.Sum             using (_⊎_)
open import Data.Product         using (_×_; _,_; proj₁; ∃)
open import Data.Maybe           using (Maybe; Is-just; just)
  renaming (map to _<$>_)
open import Data.Fin             using (Fin; toℕ; fromℕ<)

open import Data.Bool            using (Bool; T; true)
open import Data.Bool.Properties using (T?)

open import Data.Nat            using (ℕ; zero; suc; _<_; _≤_)
  renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (suc-injective; ≤-trans)

open import Data.List            using (List; []; _∷_; map; length)
open import Data.List.Relation.Unary.Any as Any            using (Any; any; here; there)
open import Data.List.Relation.Unary.All                   using (All; all)
open import Data.List.Membership.Propositional             using (_∈_; _∉_; mapWith∈)
open import Data.List.Membership.Propositional.Properties  using (∈-map⁻; ∈-map⁺)
open import Data.List.Relation.Unary.Unique.Propositional  using (Unique)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (Suffix; here; there; tail)
open import Data.List.Relation.Binary.Pointwise            using (_∷_; Pointwise-≡⇒≡)

import Data.Maybe.Relation.Unary.Any as M

open import Relation.Nullary                      using (Dec; ¬_; yes; no)
open import Relation.Nullary.Product              using (_×-dec_)
open import Relation.Nullary.Decidable            using (True; toWitness)
open import Relation.Binary                       using (Rel; Transitive; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; subst; inspect)
  renaming ([_] to ≡[_])

open import Prelude.Lists

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

  run : Script → Bool
  run f = ⟦ f ⟧ (f ♯ , tx , mapWith∈ (inputs tx) (out ∘ proj₁ ∘ ∈-map⁻ outRef ∘ validOutputRefs ∘ ∈-map⁺ outputRef))

  field
    preservesValues :
      M.Any (λ q → forge tx +ᶜ q ≡ ∑ (outputs tx) value) (∑M (map (getSpentOutput l) (inputs tx)) value)

    noDoubleSpending :
      Unique (outputRefs tx)

    allInputsValidate :
      All (T ∘ run ∘ validator) (inputs tx)

    allPoliciesValidate :
      All (T ∘ run) (policies tx)

    validateValidHashes :
      All (λ i → M.Any (λ o → address o ≡ validator i ♯) (getSpentOutput l i)) (inputs tx)

    forging :
      All (λ c → Any (λ f → c ≡ f ♯) (policies tx)) (supp (forge tx))

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

vor→utxo : ∀ {tx l}
  → outputRefs tx ⊆ map outRef (utxo l)
  → List TxOutput
vor→utxo {tx}{l} or⊆ = mapWith∈ (inputs tx) (out ∘ proj₁ ∘ ∈-map⁻ outRef ∘ or⊆ ∘ ∈-map⁺ outputRef)

infixl 5 _⊕_
_⊕_ : ∀ {l}
  → ValidLedger l
  → (tx : Tx)
  → {wi  : True (T? (range tx ∋ length l))}
  → {vor : True (outputRefs tx SETₒ.⊆? map outRef (utxo l))}
  → {pv  : True (M.dec (λ q → forge tx +ᶜ q ≟ᶜ ∑ (outputs tx) value)
                       (∑M (map (getSpentOutput l) (inputs tx)) value))}
  → {ndp : True (SETₒ.unique? (outputRefs tx))}
  → {aiv : True (all (λ i → T? $ ⟦ validator i ⟧ (validator i ♯ , tx , vor→utxo {tx}{l} (toWitness vor)))
                     (inputs tx))}
  → {apv : True (all (λ f → T? $ ⟦ f ⟧ (f ♯ , tx , vor→utxo {tx}{l} (toWitness vor))) (policies tx))}
  → {vvh : True (all (λ i → M.dec (λ o → address o ≟ℕ validator i ♯) (getSpentOutput l i)) (inputs tx))}
  → {frg : True (all (λ c → any (λ f → c ≟ℕ f ♯) (policies tx)) (supp (forge tx)))}
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
