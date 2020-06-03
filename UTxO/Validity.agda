module UTxO.Validity where

open import Level    using (0ℓ)
open import Function using (_∘_; flip; _$_)

open import Data.Sum             using (_⊎_)
open import Data.Product         using (_×_; _,_; proj₁; ∃)
open import Data.Maybe           using (Maybe; Is-just; just)
  renaming (map to _<$>_)
open import Data.Bool            using (T; true)
open import Data.Bool.Properties using (T?)
open import Data.Nat             using (ℕ; zero; suc; _<_; _≤_)
  renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties  using (suc-injective; ≤-trans)
open import Data.Fin             using (Fin; toℕ; fromℕ<)
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
open import Relation.Binary.PropositionalEquality
  renaming ([_] to ≡[_])

open import Prelude.Lists

open import UTxO.Hashing
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
      M.Any (λ q → forge tx +ᶜ q ≡ ∑ (outputs tx) value)
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
  → {pv  : True (M.dec (λ q → forge tx +ᶜ q ≟ᶜ ∑ (outputs tx) value)
                       (∑M (map (getSpentOutput l) (inputs tx)) value))}
  → {ndp : True (SETₒ.unique? (outputRefs tx))}
  → {aiv : True (all (λ{ (n , i) → T? (validator i (toPendingTx l tx n) (redeemer i) (datum i))})
                     (enumerate (inputs tx)))}
  → {apv : True (all (λ f → T? (f (toPendingMPS l tx (f ♯))))
                     (policies tx))}
  → {vvh : True (all (λ i → M.dec (λ o → (address o ≟ℕ validator i ♯) ×-dec (datumHash o ≟ℕ datum i ♯ᵈ))
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

----------------------
-- Utilities.

outputsₘ : ∃ ValidLedger → List TxOutput
outputsₘ ([]     , _) = []
outputsₘ (tx ∷ _ , _) = outputs tx

_∈′_ : Tx → ∃ ValidLedger → Set
tx ∈′ (l , _) = tx ∈ l

--------------------------------------------------------
-- Well-founded recursion on suffixes of the ledger.

open import Induction
open import Induction.WellFounded

infix 4 _≼_ _≼′_ _≺_ _≺′_

_≼_ : Rel Ledger 0ℓ
_≼_ = Suffix≡

_≺_ : Rel Ledger 0ℓ
l′ ≺ l = ∃ λ tx → tx ∷ l′ ≼ l

_≼′_ : Rel (∃ ValidLedger) 0ℓ
(l′ , _) ≼′ (l , _) = l′ ≼ l

_≺′_ : Rel (∃ ValidLedger) 0ℓ
(l , _) ≺′ (l′ , _) = l ≺ l′

postulate
  ≺-trans  : Transitive _≺_
  ≺-transˡ : ∀ {x y z} → x ≼ y → y ≺ z → x ≺ z
  ≺-∑forge : ∀ {l′ l} → l′ ≺ l → T $ ∑ l forge ≥ᶜ ∑ l′ forge

≺′⇒≼′ : ∀ {l l′} → l′ ≺′ l → l′ ≼′ l
≺′⇒≼′ (_ , p) = tail p

≺-wf : WellFounded _≺_
≺-wf l = acc $ go l
  where
    go : ∀ l l′ → l′ ≺ l → Acc _≺_ l′
    go (_ ∷ l) l′ (_ , here (refl ∷ eq)) = acc λ y y<l′ → go l y (subst (y ≺_) (Pointwise-≡⇒≡ eq) y<l′)
    go (_ ∷ l) l′ (_ , there l′<l)       = acc λ y y<l′ → go l y (≺-trans y<l′ (_ , l′<l))

≺′-wf : WellFounded _≺′_
≺′-wf vl = vl ≺′⇒≺ ≺-wf (proj₁ vl)
  where
    _≺′⇒≺_ : ∀ vl → Acc _≺_ (proj₁ vl) → Acc _≺′_ vl
    (l , _) ≺′⇒≺ acc w = acc λ{ (l′ , _) l′<l → (l′ , _) ≺′⇒≺ w l′ l′<l }

≺′-rec = All.wfRec ≺′-wf 0ℓ

----------------------
-- Properties.

≼⇒valid : ∀ {l l′}
  → ValidLedger l
  → l′ ≼ l
  → ValidLedger l′
≼⇒valid vl            (here eq)   rewrite Pointwise-≡⇒≡ eq = vl
≼⇒valid (vl ⊕ t ∶- x) (there suf) = ≼⇒valid vl suf

tx∈⇒valid : ∀ {L tx}
  → (tx∈ : tx ∈′ L)
  → IsValidTx tx (proj₁ $ ∈⇒Suffix tx∈)
tx∈⇒valid {L = _ , vl} {tx = tx} tx∈
  with l , l≺         ← ∈⇒Suffix tx∈
  with _ ⊕ .tx ∶- vtx ← ≼⇒valid vl l≺
     = vtx

-- An output spent in a previous transaction cannot be spent again.
postulate
  suf-utxo : ∀ {tx l l′ x}
    → ValidLedger l
    → Suffix≡ (tx ∷ l′) l
    → x ∈ map outRef (utxo l′)
    → x ∈ outputRefs tx
    → x ∉ map outRef (utxo l)
-- suf-utxo {tx} {l = x ∷ l} vl (here (refl ∷ p)) x∈′ x∈refs x∈
--   rewrite Pointwise-≡⇒≡ p
--         = {!!}
-- suf-utxo {tx} {l = x ∷ l} vl (there suf) x∈′ x∈refs x∈ = {!!}

-- traceRef : ∀ {tx l}
--   → ValidLedger (tx ∷ l)
--   → ∀ o → o ∈ outputRefs tx
--   → ∃[ tx′ ] ( (tx′ ∈ l)
--              × (tx′ ♯ ≡ id o) )
-- traceRef {tx} {l} (vl ⊕ .tx ∶- vtx) o o∈ = {!!}


--------------------------------------------------------
-- Packing up useful information about all predecessors
-- (i.e. the inputs of a transaction)

record Res {tx : Tx} {l : Ledger} (vl : ValidLedger l) (vtx : IsValidTx tx l) : Set where
  field
    prevTx   : Tx
    l′       : Ledger
    prevOut  : TxOutput
    vl′      : ValidLedger (prevTx ∷ l′)
    prevOut∈ : prevOut ∈ outputs prevTx
    vl′≺vl   : (prevTx ∷ l′ , vl′) ≺′ (tx ∷ l , vl ⊕ tx ∶- vtx)
    spent≡   : ∃ λ i → (i ∈ inputs tx) × (getSpentOutput l i ≡ just prevOut)

    -- ≈ prevTx ↝⟦ {-value prevOut ◆-} ⟧ tx
    or∈      : Any ((prevTx ♯ₜₓ ≡_) ∘ id) (outputRefs tx)
    ⁉≡just   : outputs prevTx ⟦ index (Any.lookup or∈) ⟧ ≡ just prevOut

resValue : ∀ {tx l} {vl : ValidLedger l} {vtx : IsValidTx tx l} → Res vl vtx → Value
resValue = value ∘ Res.prevOut

prevs : ∀ {tx l} (vl : ValidLedger l) (vtx : IsValidTx tx l) → List (Res vl vtx)
prevs {tx} {l} vl vtx
  = mapWith∈ (inputs tx) go
  module P₀ where
    go : ∀ {i} → i ∈ inputs tx → Res vl vtx
    go {i} i∈
      with outRef∈                 ← validOutputRefs vtx (∈-map⁺ outputRef i∈)
      with u , u∈ , refl           ← ∈-map⁻ outRef outRef∈
      with prev∈ , prevOut∈ , refl ← ∈utxo⇒outRef≡ {l = l} u∈
      with l′ , suf                ← ∈⇒Suffix prev∈
        = record { prevTx   = prevTx u
                 ; l′       = l′
                 ; prevOut  = out u
                 ; vl′      = vl′
                 ; prevOut∈ = prevOut∈
                 ; vl′≺vl   = vl′≺vl
                 ; spent≡   = i , i∈ , utxo-getSpent {l = l} u∈
                 ; or∈      = or∈
                 ; ⁉≡just   = ⁉≡just
                 }
        where
          id≡ : prevTx u ♯ₜₓ ≡ id (outputRef i)
          id≡ = sym $ ⟨⟩≡just {l}{outputRef i}{prevTx u} (utxo-[] {l} u∈)

          P⊆Q : ∀ {or} → outputRef i ≡ or → prevTx u ♯ₜₓ ≡ id or
          P⊆Q refl = id≡

          or∈ : Any ((prevTx u ♯ₜₓ ≡_) ∘ id) (outputRefs tx)
          or∈ = Any.map P⊆Q (∈-map⁺ outputRef i∈)

          outRef≡ : Any.lookup or∈ ≡ outputRef i
          outRef≡ = begin Any.lookup or∈                   ≡⟨ Any-lookup∘map P⊆Q (∈-map⁺ outputRef i∈) ⟩
                          Any.lookup (∈-map⁺ outputRef i∈) ≡⟨ lookup∘∈-map⁺ {f = outputRef} i∈ ⟩
                          outputRef i                      ∎
                    where open ≡-Reasoning

          ⁉≡just : (outputs (prevTx u) ⁉ index (Any.lookup or∈)) ≡ just (out u)
          ⁉≡just rewrite outRef≡ = utxo-⟨⟩ {l} u∈

          v   = value $ out u
          vl′ = ≼⇒valid vl suf

          vl′≺vl : (prevTx u ∷ l′ , vl′) ≺′ (tx ∷ l , vl ⊕ tx ∶- vtx)
          vl′≺vl = ≺-transˡ suf (tx , suffix-refl (tx ∷ l))
          -- NB. suf ≈ (prevTx u ∷ l′) ≼ l

∑prevs≡ : ∀ {tx l} (vl : ValidLedger l) (vtx : IsValidTx tx l)
        → ∑M (map (getSpentOutput l) (inputs tx)) value ≡ just (∑ (prevs vl vtx) resValue)
∑prevs≡ {tx} {l} vl vtx = ∑M-help {A = TxInput} {xs = inputs tx} {f = getSpentOutput l} {g = value}
                                  {R = Res vl vtx} {go = go} {r = resValue} (cong (value <$>_) ∘ s≡)
  where
    open P₀ vl vtx

    i′≡ : ∀ {i} i∈ → proj₁ (Res.spent≡ $ go {i} i∈) ≡ i
    i′≡ {i} i∈
      with u , u∈ , refl           ← ∈-map⁻ outRef (validOutputRefs vtx (∈-map⁺ outputRef i∈))
      with prev∈ , prevOut∈ , refl ← ∈utxo⇒outRef≡ {l = l} u∈
      with l′ , suf                ← ∈⇒Suffix prev∈
         = refl

    s≡ : ∀ {i} i∈ → getSpentOutput l i ≡ just (Res.prevOut $ go {i} i∈)
    s≡ {i} i∈
      with Res.spent≡ (go {i} i∈) | inspect Res.spent≡ (go {i} i∈)
    ... | i′ , _ , spent≡ | ≡[ go≡ ]
         = trans (cong (getSpentOutput l) i≡) spent≡
      where
        i≡ : i ≡ i′
        i≡ = trans (sym $ i′≡ {i} i∈) (cong proj₁ go≡)

prevs⊆utxo : ∀ {tx l} {vl : ValidLedger l} {vtx : IsValidTx tx l}
  → map resValue (prevs vl vtx)
  ⊆ map (value ∘ out) (utxo l)
prevs⊆utxo {tx}{l}{vl}{vtx} v∈
  with _ , pr∈ , refl ← ∈-map⁻ resValue v∈
  with _ , i∈  , refl ← ∈-mapWith∈⁻ {f = P₀.go vl vtx} pr∈
  with _ , u∈  , refl ← ∈-map⁻ outRef (validOutputRefs vtx (∈-map⁺ outputRef i∈))
  with _ , _   , refl ← ∈utxo⇒outRef≡ {l = l} u∈
  = ∈-map⁺ (value ∘ out) u∈

-- Non-fungibility
NonFungible : ∃ ValidLedger → TokenClass → Set
NonFungible (l , _) nft = ∑ l forge ◇ nft ≤ 1

NF-weaken : ∀ {nft l l′} → l′ ≺′ l → NonFungible l nft → NonFungible l′ nft
NF-weaken {nft}{l , _}{l′ , _} vl′≺ = ≤-trans (≥ᶜ-◆ {x = ∑ l forge} {y = ∑ l′ forge} $ ≺-∑forge vl′≺)
  where open FocusTokenClass nft
