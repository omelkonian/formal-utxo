------------------------------------------------------------------------
-- Combining valid ledgers.
------------------------------------------------------------------------
open import Function using (_∘_; case_of_)

open import Data.Bool    using (T)
open import Data.Product using (_×_; _,_; map₁; map₂; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Nat     using (ℕ; suc; _<_)

open import Data.List using (_++_; filter; applyUpTo)

open import Data.List.Membership.Propositional using (_∈_; mapWith∈; find)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)

open import Data.List.Relation.Unary.Any using (Any; there; here)

open import Data.List.Relation.Pointwise using (Pointwise; Pointwise-≡⇒≡; ≡⇒Pointwise-≡)

open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
import Data.List.Relation.Ternary.Interleaving as I₀
import Data.List.Relation.Ternary.Interleaving.Properties as IP
open import Data.List.Relation.Ternary.Interleaving.Propositional as I using (Interleaving; consˡ; consʳ; swap)

open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint; contractₗ; contractᵣ)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary                       using (Decidable)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨_⟩_; _≡⟨⟩_; _∎)

open import UTxO.Types
open import Hashing.Base
open import Hashing.Types
open import Hashing.MetaHash

module UTxO.Combining
  (Address : Set)
  (_♯ₐ : Hash Address)
  (_≟ₐ_ : Decidable {A = Address} _≡_)
  where


sym# : ∀ {A : Set} {l l′ : List A} → Disjoint l l′ → Disjoint l′ l
sym# {l} {l′} l#l′ (∈l′ , ∈l) = l#l′ (∈l , ∈l′)


open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⊎; map₁ to map⊎₁; map₂ to map⊎₂)

interleave⊎ : ∀ {A : Set} {l1 l2 l3 : List A}
  → Interleaving l1 l2 l3
  → (∀ x → x ∈ l3 → (x ∈ l1) ⊎ (x ∈ l2))
interleave⊎ {_} {x ∷ _} {_}   {x ∷ _}  (consˡ i) x (here refl) = inj₁ (here refl)
interleave⊎ {_} {_} {x ∷ _}   {x ∷ _}  (consʳ i) x (here refl) = inj₂ (here refl)
interleave⊎ {_} {a ∷ l1} {l2} {a ∷ l3} (consˡ i) x (there x∈)  = map⊎ there (λ x → x) (interleave⊎ i x x∈)
interleave⊎ {_} {l1} {a ∷ l2} {a ∷ l3} (consʳ i) x (there x∈)  = map⊎ (λ x → x) there (interleave⊎ i x x∈)

interleave⊆ : ∀ {A : Set} → {l1 l2 l3 : List A}
  → Interleaving l1 l2 l3
  → l1 ⊆ l3
interleave⊆ I₀.[]         ()
interleave⊆ (consˡ inter) (here refl) = here refl
interleave⊆ (consˡ inter) (there ∈1)  = there (interleave⊆ inter ∈1)
interleave⊆ (consʳ inter) ∈1          = there (interleave⊆ inter ∈1)

open import UTxO.Validity Address _♯ₐ _≟ₐ_
open SETₒ using (fromList; list; _∈?_)

_─_ : List TxOutputRef → List TxOutputRef → List TxOutputRef
xs ─ ys = filter (¬? ∘ (_∈? ys)) xs

_∪_ : List TxOutputRef → List TxOutputRef → List TxOutputRef
xs ∪ ys = xs ++ (ys ─ xs)

eq : ∀ {xs l1 l2 l3}
   → Disjoint xs l2
   → Interleaving l1 l2 l3
   → xs ─ l1 ≡ xs ─ l3
eq {[]}     {_}  {_} {_}  _ _ = refl
eq {x ∷ xs} {l1} {_} {l3} d i with (x ∈? l1) | (x ∈? l3)
... | no ¬p1 | no ¬p3 = cong (x ∷_) (eq (contractₗ d) i)
... | yes p1 | yes p3 = eq (contractₗ d) i
... | yes p1 | no ¬p3 = ⊥-elim (¬p3 (interleave⊆ i p1))
... | no ¬p1 | yes p3 with interleave⊎ i x p3
... | inj₁ p1 = ⊥-elim (¬p1 p1)
... | inj₂ p2 = ⊥-elim (d (here refl , p2))

h : ∀ {l1 l2 l3 xs : List TxOutputRef}
  → Disjoint xs l2
  → Interleaving l1 l2 l3
  → Interleaving (l1 ─ xs) l2 (l3 ─ xs)
h _ I.[] = I.[]
h {a ∷ _} {_} {a ∷ _} {xs} d (consˡ i)
  with a ∈? xs
... | yes p = h d i
... | no ¬p = consˡ (h d i)
h {_} {a ∷ _} {a ∷ _} {xs} d (consʳ i)
  with a ∈? xs
... | yes p = ⊥-elim (d (p , here refl))
... | no ¬p = consʳ (h (contractᵣ d) i)

any-interleave : ∀ {l l′ l″} {P : Tx → Set} → Interleaving l l′ l″ → Any P l → Any P l″
any-interleave (consˡ i) (here px) = here px
any-interleave (consˡ i) (there p) = there (any-interleave i p)
any-interleave (consʳ i) p         = there (any-interleave i p)

utxo   = list ∘ unspentOutputs
utxoTx = list ∘ unspentOutputsTx
spent  = list ∘ spentOutputsTx

hh : ∀ {l1 l2 l3 xs : List TxOutputRef}
    → Disjoint xs l2
    → Interleaving l1 l2 l3
    → Interleaving (l1 ∪ xs) l2 (l3 ∪ xs)
hh {l1} {l2} {l3} {xs} d i = res
  where

    t1 : Interleaving (xs ─ l1) [] (xs ─ l3)
    t1 rewrite (eq {xs} {l1} {l2} {l3} d i) = I₀.left (≡⇒Pointwise-≡ refl)

    t2 : Interleaving (l1 ++ (xs ─ l1)) (l2 ++ []) (l3 ++ (xs ─ l3))
    t2 = IP.++⁺ i t1

    open import Data.List.Properties using (++-identityʳ)
    ++[] : l2 ≡ l2 ++ []
    ++[] = sym (++-identityʳ l2)

    res : Interleaving (l1 ++ (xs ─ l1)) l2 (l3 ++ (xs ─ l3))
    res rewrite ++[] = t2


hhh : ∀ {i j tx xs}
  → (i indexed-at j) ∈ map ((tx ♯ₜₓ) indexed-at_) xs
  → i ≡ tx ♯ₜₓ
hhh {xs = []} ()
hhh {xs = x ∷ xs} (here refl) = refl
hhh {i} {j} {tx} {xs = x ∷ xs} (there p) = hhh {i} {j} {tx} {xs = xs} p

utxo-∈ : ∀ {tx txs o}
  → o ∈ utxo (tx ∷ txs)
  → o ∈ utxo txs ⊎ o ∈ utxoTx tx
utxo-∈ {tx} {txs} {o} p =
  map⊎₁ (SETₒ.∈-─ {o} {unspentOutputs txs} {spentOutputsTx tx})
        (SETₒ.∈-∪ {o} {unspentOutputs txs SETₒ.─ spentOutputsTx tx} {unspentOutputsTx tx} p)

help-∈ : ∀ {l tx₀}
  → tx₀ ∈ utxo l
  → ∃[ tx ] ((tx ♯ₜₓ ≡ id tx₀) × (tx ∈ l))

help-∈′ : ∀ {l a tx₀}
  → a ∈ l
  → tx₀ ∈ utxoTx a
  → ∃[ tx ] ((tx ♯ₜₓ ≡ id tx₀) × (tx ∈ l))

help-∈″ : ∀ {l a tx₀}
  → ValidLedger l
  → a ∈ l
  → tx₀ ∈ spent a
  → ∃[ tx ] ((tx ♯ₜₓ ≡ id tx₀) × (tx ∈ l))

help-∈ {l = x ∷ l} {tx₀} p with utxo-∈ {x} {l} {tx₀} p
... | inj₁ p₁ = map₂ (map₂ there) (help-∈ {l} {tx₀} p₁)
... | inj₂ p₂ = help-∈′ {x ∷ l} {x} (here refl) p₂

import Data.Set' as SET
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; _≟_)
module SETₙ = SET {A = ℕ} _≟_

nd-contract : ∀ {x xs}
  → SETₙ.noDuplicates (x ∷ xs)
  → SETₙ.noDuplicates xs
nd-contract {x} {xs} nd
  with x SETₙ.∈? xs
... | yes _ = ⊥-elim nd
... | no  _ = nd

nd-indices : ∀ {A : Set} {xs : List A}
  → SETₙ.noDuplicates (indices xs)
nd-indices {A} {[]} = tt
nd-indices {A} {x ∷ xs} with 0 SETₙ.∈? applyUpTo ((λ x → x) ∘ suc) (length xs)
... | yes p = {!!}
... | no ¬p = {!!} -- nd-contract {0} {applyUpTo ((λ x → x) ∘ suc) (length xs)} (nd-indices {A} {xs})

nd-map : ∀ {xs tx}
  → SETₙ.noDuplicates xs
  → SETₒ.noDuplicates (map ((tx ♯ₜₓ) indexed-at_) xs)
nd-map {[]}     {_}  _ = tt
nd-map {x ∷ xs} {tx} nd
  with ((tx ♯ₜₓ) indexed-at x) ∈? map ((tx ♯ₜₓ) indexed-at_) xs
... | yes p = {!!}
... | no ¬p = {!!}

valid-∈ : ∀ {l a}
  → a ∈ l
  → ValidLedger l
  → ∃[ l′ ] ((l′ ⊆ l) × IsValidTx a l′)
valid-∈ {a ∷ l} (here refl) (vl ⊕ .a ∶- x) = l , there , x
valid-∈ {_ ∷ l} (there a∈)  (vl ⊕ t ∶- x) with valid-∈ a∈ vl
... | l′ , l′⊆ , v = l′ , (λ l′∈ → there (l′⊆ l′∈)) , v

vtx∃ : ∀ {l h}
  → Any (λ tx → tx ♯ₜₓ ≡ h) l
  → ∃[ tx ] ((tx ♯ₜₓ ≡ h) × tx ∈ l)
vtx∃ (here {tx} refl) = tx , refl , here refl
vtx∃ (there p) with vtx∃ p
... | tx , refl , tx∈ = tx , refl , there tx∈

validTxRefs∃ : ∀ {l l′ tx}
  → l′ ⊆ l
  → IsValidTx tx l′
  → ∀ i → i ∈ inputs tx →
      ∃[ tx′ ] ((tx′ ♯ₜₓ ≡ id (outputRef i)) × (tx′ ∈ l))
validTxRefs∃ {l} {l′} {tx} l′⊆ (record { validTxRefs = vtx }) i i∈
  with vtx∃ (vtx i i∈)
... | tx′ , refl , tx′∈ = tx′ , refl , l′⊆ tx′∈

help-∈′ {l} {a} {tx₀} a∈ p
  rewrite SETₒ.from↔to {map ((a ♯ₜₓ) indexed-at_) (indices (outputs a))}
                       (nd-map {xs = indices (outputs a)} {tx = a} (nd-indices {xs = outputs a}))
  with ∈-map⁻ ((a ♯ₜₓ) indexed-at_) {y = tx₀} {xs = indices (outputs a)} p
... | j , j∈ , refl = a , refl , a∈

help-∈″ {l} {a} {tx₀} vl a∈ p
  rewrite SETₒ.from↔to {map outputRef (inputs a)} (noDoubleSpending (proj₂ (proj₂ (valid-∈ a∈ vl))))
  with ∈-map⁻ outputRef {y = tx₀} {xs = inputs a} p
... | x , x∈ , refl
  with valid-∈ a∈ vl
... | l′ , l′⊆ , valid = validTxRefs∃ l′⊆ valid x x∈

spent# : ∀ {l l′ a}
  → a ∈ l
  → ValidLedger l
  → Disjoint l l′
  → Disjoint (spent a) (utxo l′)
spent# {l} {l′} {a} a∈ vl l#l′ {tx₀} (p , q)
  with help-∈″ vl a∈ p
... | t₁ , eq₁ , t₁∈
  with help-∈ {l′} {tx₀} q
... | t₂ , eq₂ , t₂∈ = ⊥-elim (l#l′ (t₁∈ , t₁∈′))
  where t₁∈′ : t₁ ∈ l′
        t₁∈′ rewrite injective♯ₜₓ {t₁} {t₂} (trans eq₁ (sym eq₂)) = t₂∈

unspent# : ∀ {l l′ a}
  → a ∈ l
  → Disjoint l l′
  → Disjoint (utxoTx a) (utxo l′)
unspent# {l} {l′} {a} a∈ l#l′ {tx₀} (p , q)
  with help-∈′ a∈ p
... | t₁ , eq₁ , t₁∈
  with help-∈ {l′} {tx₀} q
... | t₂ , eq₂ , t₂∈ = ⊥-elim (l#l′ (t₁∈ , t₁∈′))
  where t₁∈′ : t₁ ∈ l′
        t₁∈′ rewrite injective♯ₜₓ {t₁} {t₂} (trans eq₁ (sym eq₂)) = t₂∈

utxo-interleave : ∀ {l l′ l″}
  → ValidLedger l
  → ValidLedger l′
  → Disjoint l l′
  → Interleaving l l′ l″
  → Interleaving (utxo l) (utxo l′) (utxo l″)
utxo-interleave _ _ _ I.[]      = I.[]
utxo-interleave {a ∷ l} {l′} {a ∷ l″} vl@(v ⊕ _ ∶- _) vl′ l#l′ (consˡ inter) =
  hh {l1 = utxo l ─ spent a} {l2 = utxo l′} d₂ (h {l1 = utxo l} {l2 = utxo l′} d₁ rec)
  where
    rec : Interleaving (utxo l) (utxo l′) (utxo l″)
    rec = utxo-interleave v vl′ (contractₗ l#l′) inter

    d₁ : Disjoint (spent a) (utxo l′)
    d₁ = spent# (here refl) vl l#l′

    d₂ : Disjoint (utxoTx a) (utxo l′)
    d₂ = unspent# (here refl) l#l′


utxo-interleave {l} {a ∷ l′} {a ∷ l″} vl vl′@(v ⊕ _ ∶- _) l#l′ (consʳ inter) =
  swap (hh {l1 = utxo l′ ─ spent a} {l2 = utxo l} d₂ (h {l1 = utxo l′} {l2 = utxo l} d₁ rec))
  where
    rec : Interleaving (utxo l′) (utxo l) (utxo l″)
    rec = swap (utxo-interleave vl v (contractᵣ l#l′) inter)

    d₁ : Disjoint (spent a) (utxo l)
    d₁ = spent# (here refl) vl′ (sym# l#l′)

    d₂ : Disjoint (utxoTx a) (utxo l)
    d₂ = unspent# (here refl) (sym# l#l′)

find≡ : ∀ {l : Ledger} {o : TxOutputRef} {P : Tx → Set}
  → (p : Any P l)
  → P (proj₁ (find p))
find≡ {_ ∷ l} {o} {P} p with p
... | here  p′ = p′
... | there p′ = find≡ {l} {o} {P} p′

any≡ : ∀ {l l″ : Ledger} (out : TxOutputRef)
  → (p″ : Any (λ tx → tx ♯ₜₓ ≡ id out) l″)
  → (p  : Any (λ tx → tx ♯ₜₓ ≡ id out) l)
  → proj₁ (find p″) ≡ proj₁ (find p)
any≡ {l} {l″} o p″ p = injective♯ₜₓ eq♯
  where
    eq♯ : (proj₁ (find p″)) ♯ₜₓ ≡ (proj₁ (find p)) ♯ₜₓ
    eq♯ rewrite find≡ {l″} {o} {(_≡ id o) ∘ _♯ₜₓ} p″ | find≡ {l} {o} {P = (_≡ id o) ∘ _♯ₜₓ} p = refl

open import Data.List.Relation.Binary.Prefix.Heterogeneous as Pr using () renaming (Prefix to Prefix′)
Prefix : ∀ {A : Set} → List A → List A → Set
Prefix {A} = Prefix′ {A = A} {B = A} _≡_

∈-tail : ∀ {A : Set} {P : A → Set} {xs : List A}
  → Any P xs
  → List A
∈-tail {xs = _ ∷ xs} (here _)  = xs
∈-tail {xs = _ ∷ xs} (there p) = ∈-tail {xs = xs} p

PV : (l : Ledger) {l′ : Ledger} → (l″ : Ledger) → Interleaving l l′ l″ → Set
PV l₀ l″₀ inter =
  ∀ tx → (tx∈ : tx ∈ l₀) →
    let l  = ∈-tail tx∈
        l″ = ∈-tail (interleave⊆ inter tx∈)
    in ∀ {ptx i out vds} →
         runValidation ptx i out vds (getState l″)
       ≡ runValidation ptx i out vds (getState l)

pv-contract : ∀ {a l l′ l″ inter}
  → PV (a ∷ l) {l′} (a ∷ l″) (consˡ inter)
  → PV l {l′} l″ inter
pv-contract {a} {l} {l″} {inter} pv tx tx∈ {ptx} {i} {out} {vds} = pv tx (there tx∈) {ptx} {i} {out} {vds}

pv-contractᵣ : ∀ {a l l′ l″ inter}
  → PV l′ {a ∷ l} (a ∷ l″) (consʳ inter)
  → PV l′ {l} l″ inter
pv-contractᵣ {a} {l} {l″} {inter} pv tx tx∈ {ptx} {i} {out} {vds} = pv tx tx∈ {ptx} {i} {out} {vds}

combineDisjointLedgers : ∀ {l l′ l″ tx}
  → (d : Disjoint l l′)
  → ValidLedger l
  → ValidLedger l′
  → Interleaving l l′ l″
  → (v : IsValidTx tx l)
  → (∀ i i∈ →
       let out = lookupOutput l (outputRef i) (validTxRefs v i i∈) (validOutputIndices v i i∈)
           ptx = mkPendingTx l tx (validTxRefs v) (validOutputIndices v)
       in runValidation ptx i out (validDataScriptTypes v i i∈) (getState l″)
        ≡ runValidation ptx i out (validDataScriptTypes v i i∈) (getState l))
  → IsValidTx tx l″
combineDisjointLedgers {l} {l′} {l″} {tx} d v₀ v′ inter
    (record { validTxRefs          = vtx₀
            ; validOutputIndices   = voi₀
            ; validOutputRefs      = vor₀
            ; validDataScriptTypes = vds₀
            ; preservesValues      = pv₀
            ; noDoubleSpending     = nds₀
            ; allInputsValidate    = aiv₀
            ; validateValidHashes  = vvh₀
            ; forging              = frg₀ })
    AIV
  = record { validTxRefs          = vtx
           ; validOutputIndices   = voi
           ; validOutputRefs      = vor
           ; validDataScriptTypes = vds
           ; preservesValues      = pv
           ; noDoubleSpending     = nds
           ; allInputsValidate    = aiv
           ; validateValidHashes  = vvh
           ; forging              = frg }
  where
    vtx : ∀ i → i ∈ inputs tx →
      Any (λ t → t ♯ₜₓ ≡ id (outputRef i)) l″
    vtx i i∈ = any-interleave inter (vtx₀ i i∈)

    voi : ∀ i → (i∈ : i ∈ inputs tx) →
      index (outputRef i) < length (outputs (lookupTx l″ (outputRef i) (vtx i i∈)))
    voi i i∈ rewrite any≡ (outputRef i) (vtx i i∈) (vtx₀ i i∈) = voi₀ i i∈

    vor : ∀ i → i ∈ inputs tx →
      outputRef i SETₒ.∈′ unspentOutputs l″
    vor i i∈ = interleave⊆ (utxo-interleave v₀ v′ d inter) (vor₀ i i∈)

    vds : ∀ i → (i∈ : i ∈ inputs tx) →
      D i ≡ Data (lookupOutput l″ (outputRef i) (vtx i i∈) (voi i i∈))
    vds i i∈ rewrite any≡ (outputRef i) (vtx i i∈) (vtx₀ i i∈) = vds₀ i i∈

    lookupValue≡ : ∀ {i i∈} →
        lookupValue l″ i (vtx i i∈) (voi i i∈)
      ≡ lookupValue l i (vtx₀ i i∈) (voi₀ i i∈)
    lookupValue≡ {i} {i∈} rewrite any≡ (outputRef i) (vtx i i∈) (vtx₀ i i∈) = refl

    map∈-cong : ∀ {A : Set} {xs : List TxInput}
      → (f : ∀ {i} → i ∈ xs → A)
      → (g : ∀ {i} → i ∈ xs → A)
      → (∀ {i} → (i∈ : i ∈ xs) → f i∈ ≡ g i∈)
      → Pointwise _≡_ (mapWith∈ xs f) (mapWith∈ xs g)
    map∈-cong {xs = []}     f g cong = Pointwise.[]
    map∈-cong {xs = x ∷ xs} f g cong =
      cong (here refl)
        Pointwise.∷
      map∈-cong (f ∘ there) (g ∘ there) λ {i} i∈ → cong (there i∈)

    mapLookupValue≡ :
        mapWith∈ (inputs tx) (λ {i} i∈ → lookupValue l″ i (vtx i i∈) (voi i i∈))
      ≡ mapWith∈ (inputs tx) (λ {i} i∈ → lookupValue l i (vtx₀ i i∈) (voi₀ i i∈))
    mapLookupValue≡ =
      Pointwise-≡⇒≡ (map∈-cong
        (λ {i} i∈ → lookupValue l″ i (vtx i i∈) (voi i i∈))
        (λ {i} i∈ → lookupValue l i (vtx₀ i i∈) (voi₀ i i∈))
        (λ {i} i∈ → lookupValue≡ {i} {i∈}))

    pv : forge tx +ᶜ sumᶜ (mapWith∈ (inputs tx) λ {i} i∈ → lookupValue l″ i (vtx i i∈) (voi i i∈))
       ≡ fee tx +ᶜ sumᶜ (map value (outputs tx))
    pv rewrite mapLookupValue≡ = pv₀

    nds : SETₒ.noDuplicates (map outputRef (inputs tx))
    nds = nds₀

    ptxIn≡ : ∀ {i i∈} →
        mkPendingTxIn l″ i (vtx i i∈) (voi i i∈)
      ≡ mkPendingTxIn l i (vtx₀ i i∈) (voi₀ i i∈)
    ptxIn≡ {i} {i∈} =
      begin
        mkPendingTxIn l″ i (vtx i i∈) (voi i i∈)
      ≡⟨ cong (λ x → record { value         = x
                            ; validatorHash = (validator i) ♯
                            ; redeemerHash  = (redeemer i) ♯ }
               ) (lookupValue≡ {i} {i∈}) ⟩
        mkPendingTxIn l i (vtx₀ i i∈) (voi₀ i i∈)
      ∎ -- rewrite any≡ (outputRef i) (vtx i i∈) (vtx₀ i i∈) = {!!}

    mapPtxIn≡ :
        mapWith∈ (inputs tx) (λ {i} i∈ → mkPendingTxIn l″ i (vtx i i∈) (voi i i∈))
      ≡ mapWith∈ (inputs tx) (λ {i} i∈ → mkPendingTxIn l i (vtx₀ i i∈) (voi₀ i i∈))
    mapPtxIn≡ =
      Pointwise-≡⇒≡ (map∈-cong
        (λ {i} i∈ → mkPendingTxIn l″ i (vtx i i∈) (voi i i∈))
        (λ {i} i∈ → mkPendingTxIn l i (vtx₀ i i∈) (voi₀ i i∈))
        (λ {i} i∈ → ptxIn≡ {i} {i∈}))

    ptx≡ :
        mkPendingTx l″ tx vtx voi
      ≡ mkPendingTx l tx vtx₀ voi₀
    ptx≡ =
      begin
        mkPendingTx l″ tx vtx voi
      ≡⟨ cong (λ x → record { txHash  = tx ♯ₜₓ
                             ; inputs  = x
                             ; outputs = map mkPendingTxOut (outputs tx)
                             ; forge   = forge tx
                             ; fee     = fee tx }
               ) mapPtxIn≡ ⟩
        mkPendingTx l tx vtx₀ voi₀
      ∎ -- rewrite mapPtxIn≡ = {!!}

    aiv : ∀ i → (i∈ : i ∈ inputs tx) →
      let out = lookupOutput l″ (outputRef i) (vtx i i∈) (voi i i∈)
          ptx = mkPendingTx l″ tx vtx voi
      in T (runValidation ptx i out (vds i i∈) (getState l″))
    aiv i i∈ rewrite any≡ (outputRef i) (vtx i i∈) (vtx₀ i i∈)
                   | ptx≡
                   | AIV i i∈
                   = aiv₀ i i∈

    vvh : ∀ i → (i∈ : i ∈ inputs tx) →
      let out = lookupOutput l″ (outputRef i) (vtx i i∈) (voi i i∈)
      in (address out) ♯ₐ ≡ (validator i) ♯
    vvh i i∈ rewrite any≡ (outputRef i) (vtx i i∈) (vtx₀ i i∈) = vvh₀ i i∈

    frg : ∀ c → c ∈ keys (forge tx) →
      ∃[ i ] ∃ λ (i∈ : i ∈ inputs tx) →
        let out = lookupOutput l″ (outputRef i) (vtx i i∈) (voi i i∈)
        in (address out) ♯ₐ ≡ c
    frg c c∈ with frg₀ c c∈
    ... | i , i∈ , p = i , i∈ , go p
      where
        go : let out = lookupOutput l (outputRef i) (vtx₀ i i∈) (voi₀ i i∈)
             in (address out) ♯ₐ ≡ c
           → let out = lookupOutput l″ (outputRef i) (vtx i i∈) (voi i i∈)
             in (address out) ♯ₐ ≡ c
        go p rewrite any≡ (outputRef i) (vtx i i∈) (vtx₀ i i∈) = p

-- If two ledgers are disjoint, i.e. they do not share any transactions,
-- any of their possible interleavings is also a valid ledger.
_↔_⊢_,_,_,_ : ∀ {l l′ l″ : Ledger}

  → ValidLedger l
  → ValidLedger l′
  → (i : Interleaving l l′ l″)
  → Disjoint l l′
  → PV l {l′} l″ i
  → PV l′ {l} l″ (swap i)
    -----------------------------
  → ValidLedger l″

_↔_⊢_,_,_,_ _ _ I.[] _ _ _ = ∙

_↔_⊢_,_,_,_ {tx ∷ l} {l′} {tx ∷ l″} v@(v₀ ⊕ _ ∶- vt) v′ (consˡ inter) d AIVₗ AIVᵣ =
    v₀ ↔ v′ ⊢ inter
            , (d ∘ map₁ there)
            , pv-contract {tx} {l} {l′} {l″} {inter} AIVₗ
            , pv-contractᵣ {tx} {l} {l′} {l″} {swap inter} AIVᵣ
  ⊕ tx
  ∶- combineDisjointLedgers (contractₗ d) v₀ v′ inter vt aiv
  where
    aiv : ∀ (i : TxInput) (i∈ : i ∈ inputs tx) →
      let out = lookupOutput l (outputRef i) (validTxRefs vt i i∈) (validOutputIndices vt i i∈)
          ptx = mkPendingTx l tx (validTxRefs vt) (validOutputIndices vt)
          vds = validDataScriptTypes vt i i∈
      in runValidation ptx i out vds (getState l″)
       ≡ runValidation ptx i out vds (getState l)
    aiv i i∈ =
      let out = lookupOutput l (outputRef i) (validTxRefs vt i i∈) (validOutputIndices vt i i∈)
          ptx = mkPendingTx l tx (validTxRefs vt) (validOutputIndices vt)
          vds = validDataScriptTypes vt i i∈
      in AIVₗ tx (here refl) {ptx} {i} {out} {vds}

_↔_⊢_,_,_,_ {l′} {tx ∷ l} {tx ∷ l″} v′ v@(v₀ ⊕ _ ∶- vt) (consʳ inter) d AIVₗ AIVᵣ =
    v′ ↔ v₀ ⊢ inter
            , (d ∘ map₂ there)
            , pv-contractᵣ {tx} {l} {l′} {l″} {inter} AIVₗ
            , pv-contract {tx} {l} {l′} {l″} {swap inter} AIVᵣ
  ⊕ tx
  ∶- combineDisjointLedgers (sym# (contractᵣ d)) v₀ v′ (swap inter) vt aiv
  where
    aiv : ∀ (i : TxInput) (i∈ : i ∈ inputs tx) →
      let out = lookupOutput l (outputRef i) (validTxRefs vt i i∈) (validOutputIndices vt i i∈)
          ptx = mkPendingTx l tx (validTxRefs vt) (validOutputIndices vt)
          vds = validDataScriptTypes vt i i∈
      in runValidation ptx i out vds (getState l″)
       ≡ runValidation ptx i out vds (getState l)
    aiv i i∈ =
      let out = lookupOutput l (outputRef i) (validTxRefs vt i i∈) (validOutputIndices vt i i∈)
          ptx = mkPendingTx l tx (validTxRefs vt) (validOutputIndices vt)
          vds = validDataScriptTypes vt i i∈
      in AIVᵣ tx (here refl) {ptx} {i} {out} {vds}

{-
-}
----------------------------
-- Demonstrative example.

{-

module Ledger1 where

  data A : Set where
    Alice Bob Charlie : A

  _♯ᵃ : Hash A
  Alice   ♯ᵃ = 1
  Bob     ♯ᵃ = 2
  Charlie ♯ᵃ = 3

  _≟ᵃ : Decidable {A = A} _≡_
  x ≟ᵃ y = ?

  open import UTxO.Validity A _♯ᵃ _≟ᵃ_

  t₁ᵃ : Tx
  t₁ᵃ = record { inputs  = ?
               ; outputs = ?
               ; forge   = ?
               ; fee     = ? }
  t₂ᵃ : Tx
  t₂ᵃ = record { inputs  = ?
               ; outputs = ?
               ; forge   = ?
               ; fee     = ? }
  t₃ᵃ : Tx
  t₃ᵃ = record { inputs  = ?
               ; outputs = ?
               ; forge   = ?
               ; fee     = ? }

  lᵃ : ValidLedger (t₃ᵃ ∷ t₂ᵃ ∷ t₁ᵃ ∷ cᵃ ∷ [])


module Ledger2 where

  open import Data.Nat using (ℕ; _≟_)

  B : Set
  B = ℕ

  _♯ᵇ : Hash B
  _♯ᵇ = λ x → x

  _≟ᵇ_ : Decidable {A = B} _≡_
  _≟ᵇ_ = _≟_

  open import UTxO.Validity B _♯ᵇ _≟ᵇ_

  t₁ᵇ : Tx
  t₁ᵇ = record { inputs  = ?
               ; outputs = ?
               ; forge   = ?
               ; fee     = ? }
  t₂ᵇ : Tx
  t₂ᵇ = record { inputs  = ?
               ; outputs = ?
               ; forge   = ?
               ; fee     = ? }
  t₃ᵇ : Tx
  t₃ᵇ = record { inputs  = ?
               ; outputs = ?
               ; forge   = ?
               ; fee     = ? }

  lᵇ : ValidLedger (t₃ᵇ ∷ t₂ᵇ ∷ t₁ᵇ ∷ cᵇ ∷ [])


Combine them: there is no sharing of transactions, but sharing of addresses
open Ledger1
open Ledger2

l : ValidLedger (t₃ᵇ ∷ t₂ᵇ ∷ t₁ᵇ ∷ ... ∷ cᵃ ∷ cᵇ ∷ [])
l = weaken lᵃ ↔ lᵇ
  where
    A↪B = ... ♯ᵃ ...

    open import Weakening A _♯ᵃ _≟ᵃ_ B _♯ᵇ _≟ᵇ_ A↪B

-}
