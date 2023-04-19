open import Prelude.Init
open L.NE using (head; last)
open import Prelude.General
open import Prelude.Nats.Postulates
open import Prelude.Lists
open import Prelude.Lists.Postulates
open import Prelude.Membership
open import Prelude.ToN
open import Prelude.Bifunctor
open import Prelude.Ord

open import UTxO.Hashing
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities
open import UTxO.Validity


module UTxO.TokenProvenance (nft : TokenClass) where

open FocusTokenClass nft

private
  variable
    L  : ∃ ValidLedger
    tx : Tx
    n  : Quantity

-- Definitions.

_↝⟦_⟧_ : Tx → Quantity → Tx → Set
tx ↝⟦ n ⟧ tx′ = Σ[ or∈ ∈ Any ((tx ♯ₜₓ ≡_) ∘ hid) (outputRefs tx′) ]
                  ∃[ o ] ( ((outputs tx ⁉ index (L.Any.lookup or∈)) ≡ just o)
                         × (value o ◆ ≥ n) )

data X (n : Quantity) : List⁺ Tx → Set where
  root :

      (tx : Tx)
    → forge tx ◆ ≥ n
      ---------------
    → X n (tx ∷ [])

  cons : ∀ {txs tx}

    → X n txs
    → head txs ↝⟦ n ⟧ tx
      -------------------
    → X n (tx ∷⁺ txs)

weakenX : ∀ {n n′ txs} → n′ ≤ n → X n txs → X n′ txs
weakenX n′< (root tx n<)                = root tx (≤-trans n′< n<)
weakenX n′< (cons x (or∈ , o , p , n<)) = cons (weakenX n′< x) (or∈ , o , p , ≤-trans n′< n<)

record Trace L (tx : Tx) (n : Quantity) : Set where
  field
    txs    : List⁺ Tx
    trace∈ : All⁺ (_∈′ L) txs
    linked : X n txs
    head≡  : head txs ≡ tx
open Trace public

record Provenance L tx (n : Quantity) : Set where
  field
    traces : List (∃ $ Trace L tx)
    sums   : ∑₁ traces ≥ n
open Provenance public

-- Utilities.

origin : Trace L tx n → Tx
origin = last ∘ txs

∣_∣ : Provenance L tx n → ℕ
∣_∣ = length ∘ traces

weaken-↝ : ∀ {tx tx′ n n′} → tx ↝⟦ n ⟧ tx′ → n′ ≤ n → tx ↝⟦ n′ ⟧ tx′
weaken-↝ {n = n}{n′} (or∈ , o , p , ≤v) n≤ = or∈ , o , p , ≤-trans {i = n′} {j = n} {k = value o ◆} n≤ ≤v

weakenTrace : ∀ {L L′} → L′ ≼′ L → Trace L′ tx n → Trace L tx n
weakenTrace L′≼ record {txs = txs; trace∈ = tr∈;                          linked = p; head≡ = h≡}
              = record {txs = txs; trace∈ = L.All.map (Suffix⇒⊆ L′≼) tr∈; linked = p; head≡ = h≡}

weakenTraceⁿ : ∀ {n n′} → n′ ≤ n → Trace L tx n → Trace L tx n′
weakenTraceⁿ n< record {txs = txs; trace∈ = tr∈; linked = p;            head≡ = h≡}
              = record {txs = txs; trace∈ = tr∈; linked = weakenX n< p; head≡ = h≡}

weakenProvenance : ∀ {L L′} → L′ ≼′ L → Provenance L′ tx n → Provenance L tx n
weakenProvenance {tx = tx} {n = n} {L = L}{L′} L≼
    record { traces = trs;              sums = p }
  = record { traces = map (map₂′ f) trs; sums = subst (_≥ n) (sym $ ∑₁-map₂ {xs = trs} {f = f}) p }
  where
    f : ∀ {n} → Trace L′ tx n → Trace L tx n
    f = weakenTrace L≼

_∷ᵗ_∶-_ :
    (tx′ : Tx)
  → (tr : Trace L tx n)
  → (tx′ ∈′ L) × (tx ↝⟦ n ⟧ tx′)
  → Trace L tx′ n
tx ∷ᵗ record {txs = txs;       trace∈ = tr∈;       linked = p;          head≡ = refl} ∶- (tx∈ , tx↝)
    = record {txs = tx ∷⁺ txs; trace∈ = tx∈ ∷ tr∈; linked = cons p tx↝; head≡ = refl}

forge◆≥ : ∀ {txs : List⁺ Tx} (x : X n txs) → forge (last txs) ◆ ≥ n
forge◆≥ (root _ frg≥)              = frg≥
forge◆≥ (cons {txs = txs}{tx} x _) rewrite last-∷ {x = tx}{txs} = forge◆≥ x

singleton-Provenance : ∀ {tx l} {vl : ValidLedger (tx ∷ l)} → Provenance (_ , vl) tx (forge tx ◆)
singleton-Provenance {tx = tx}{l}{vl} = record {traces = [ tr ]; sums = ∑≥}
  where
    tr : ∃ $ Trace (_ , vl) tx
    tr = _ , record {txs = tx ∷ []; trace∈ = here refl ∷ []; linked = root tx ≤-refl; head≡ = refl}

    ∑≥ : ∑₁ [ tr ] ≥ forge tx ◆
    ∑≥ = subst (_≥ forge tx ◆) (sym $ ∑₁-single {n = forge tx ◆} {x = tr}) ≤-refl

combine : (prs : List (∃ $ Provenance L tx)) → ∑₁ prs ≥ n → Provenance L tx n
combine [] z≤n = record {traces = []; sums = z≤n}
combine {L = L} {tx = tx} {n = n} ((n′ , pr) ∷ prs) ∑≥ = record
  { traces = traces pr ++ traces pr′
  ; sums   = ∑≥′
  }
  where
    pr′ : Provenance L tx (∑₁ prs)
    pr′ = combine {n = ∑₁ prs} prs ≤-refl

    ∑≥′ : ∑₁ (traces pr ++ traces pr′) ≥ n
    ∑≥′ = begin n                                ≤⟨ ∑≥ ⟩
                n′ + ∑₁ prs                      ≤⟨ ≥-+-swapˡʳ (sums pr) (sums pr′) ⟩
                ∑₁ (traces pr) + ∑₁ (traces pr′) ≡⟨ sym $ ∑₁-++ {xs = traces pr}{traces pr′} ⟩
                ∑₁ (traces pr ++ traces pr′)     ∎
          where open ≤-Reasoning

-- Token provenance.

provenance : ∀ {tx l} (vl : ValidLedger (tx ∷ l)) → ∀ {o} → o ∈ outputs tx → Provenance (_ , vl) tx (value o ◆)
provenance {tx}{l} vl = go vl (≺′-wf (_ , vl))
  module Provenance₀ where
    go : ∀ {tx l} (vl : ValidLedger (tx ∷ l)) → Acc _≺′_ (_ , vl)
       → (∀ {o} → o ∈ outputs tx → Provenance (_ , vl) tx (value o ◆))
    go {tx}{l} vl₀@(vl ⊕ tx ∶- vtx) (acc a) {o} o∈
      = combine allPrevs ∑≥
      module Provenance₁ where
        L₀ = _ , vl₀
        v  = value o ◆
        rs = prevs vl vtx

        fromForge : List (∃ $ Provenance L₀ tx)
        fromForge
          with ◆∈? forge tx
        ... | yes _ = [ _ , singleton-Provenance {tx = tx}{l}{vl₀} ]
        ... | no  _ = []

        res→traces : Res vl vtx → Maybe (∃ $ Provenance L₀ tx)
        res→traces r@(record { prevTx = tx′; vl′ = vl′; prevOut = o′; prevOut∈ = o∈′; vl′≺vl = vl′≺vl
                             ; or∈ = or∈; ⁉≡just = ⁉≡just })
          with ◆∈? resValue r
        ... | no  _ = nothing
        ... | yes _ = just $ _ , pr
          where
            r◆ = resValue r ◆

            ↝tx : tx′ ↝⟦ r◆ ⟧ tx
            ↝tx = or∈ , o′ , ⁉≡just , ≤-refl

            pr′ : Provenance L₀ tx′ r◆
            pr′ = weakenProvenance (≺′⇒≼′ {l = L₀}{_ , vl′} vl′≺vl) (go vl′ (a _ vl′≺vl) o∈′)

            pr : Provenance L₀ tx r◆
            pr = record { traces = limit r◆ k₁ k₂ (traces pr′)
                        ; sums = ∑₁-limit {xs = traces pr′} {k₁ = k₁} {k₂ = k₂} (sums pr′) }
              where
                k₁ : ∀ {n} → r◆ ≤ n → Trace L₀ tx′ n → Trace L₀ tx r◆
                k₁ {n} r≤ tr = tx ∷ᵗ weakenTraceⁿ r≤ tr ∶- (here refl , ↝tx)

                k₂ : ∀ {n} → n ≤ r◆ → Trace L₀ tx′ n → Trace L₀ tx n
                k₂ {n} n≤ tr = tx ∷ᵗ tr ∶- (here refl , weaken-↝ {tx = tx′}{tx} ↝tx n≤)


        fromPrevs : List (∃ $ Provenance L₀ tx)
        fromPrevs = mapMaybe res→traces rs

        allPrevs : List (∃ $ Provenance L₀ tx)
        allPrevs = fromForge ++ fromPrevs

--

        ∑prev = ∑ rs resValue
        ∑all  = forge tx +ᶜ ∑prev

        pv₀ : ∑all ≡ ∑ᵥ (outputs tx)
        pv₀ = ∑M≡just (∑prevs≡ vl vtx) (preservesValues vtx)

        pv₁ : T $ ∑all ≥ᶜ value o
        pv₁ = ≥ᶜ-trans {x = ∑all} {y = ∑ᵥ (outputs tx)} {z = value o} (≥ᶜ-refl′ pv₀) (∑-≥ᶜ {fv = value} o∈)

        pv₂ : ∑all ◆ ≥ v
        pv₂ = ≥ᶜ-◆ {x = ∑all} {y = value o} pv₁

        ∑forge≡ : ∑₁ fromForge ≡ forge tx ◆
        ∑forge≡ with ◆∈? forge tx
        ... | yes _ = Nat.+-identityʳ (forge tx ◆)
        ... | no ¬p = sym $ ¬x>0⇒x≡0 ¬p

        ∑-helper : ∑ℕ (map (_◆ ∘ resValue) rs) ≡ ∑₁ (mapMaybe res→traces rs)
        ∑-helper = ∑-mapMaybe {xs = rs} {fm = res→traces} {g = resValue} {fv = proj₁} p₁ p₂
          where
            p₁ : ∀ r → Is-nothing (res→traces r) → resValue r ◆ ≡ 0
            p₁ r rn with ◆∈? resValue r | rn
            ... | yes _ | M.All.just ()
            ... | no ¬p | _ = ¬x>0⇒x≡0 ¬p

            p₂ : ∀ r v → res→traces r ≡ just v → resValue r ◆ ≡ proj₁ v
            p₂ r v rj with ◆∈? resValue r | rj
            ... | yes _ | refl = refl
            ... | no  _ | ()

        ∑fromPrevs≡ : ∑prev ◆ ≡ ∑₁ fromPrevs
        ∑fromPrevs≡ = begin ∑prev ◆                     ≡⟨ ∑-◆ {xs = rs} {f = resValue} ⟩
                            ∑ℕ (map (_◆ ∘ resValue) rs) ≡⟨ ∑-helper ⟩
                            ∑₁ (mapMaybe res→traces rs) ≡⟨⟩
                            ∑₁ fromPrevs                ∎
                      where open ≡-Reasoning

        ∑≥ : ∑₁ allPrevs ≥ v
        ∑≥ = begin v                             ≤⟨ pv₂ ⟩
                   ∑all ◆                        ≡⟨⟩
                   (forge tx +ᶜ ∑prev) ◆         ≡⟨ +ᶜ-◆ {x = forge tx} {y = ∑prev} ⟩
                   forge tx ◆     + ∑prev ◆      ≡⟨ cong (forge tx ◆ +_) ∑fromPrevs≡ ⟩
                   forge tx ◆     + ∑₁ fromPrevs ≡⟨ cong (_+ ∑₁ fromPrevs) (sym ∑forge≡) ⟩
                   ∑₁ fromForge + ∑₁ fromPrevs   ≡⟨ sym $ ∑₁-++ {xs = fromForge}{fromPrevs} ⟩
                   ∑₁ (fromForge ++ fromPrevs)   ≡⟨⟩
                   ∑₁ allPrevs ∎
              where open ≤-Reasoning

provenance⁺ : ∀ {tx l} (vl : ValidLedger (tx ∷ l)) {o} (o∈ : o ∈ outputs tx)
  → ◆∈ value o
  → ∣ provenance vl o∈ ∣ > 0
provenance⁺ vl o∈ ◆∈v
  with provenance vl o∈
... | record {traces = []; sums = p} = ⊥-elim $ x≡0⇒¬x>0 (x≤0⇒x≡0 p) ◆∈v
... | record {traces = _ ∷ _}        = s≤s z≤n

origin∈ : (tr : Trace L tx n) → origin tr ∈′ L
origin∈ = All⁺-last ∘ trace∈

mkPendingMPS : Trace L tx n → HashId → PendingMPS
mkPendingMPS tr = toPendingMPS (proj₁ $ ∈⇒Suffix $ origin∈ tr) (origin tr)

mps≡ : ∀ {L L′} (l≺ : L′ ≼′ L) (tr : Trace L′ tx n)
  → (proj₁ $ ∈⇒Suffix $ origin∈ {L = L} $ weakenTrace l≺ tr)
  ≡ (proj₁ $ ∈⇒Suffix $ origin∈ tr)
mps≡ {L = L}{L′} l≺ tr = proj₁∘∈⇒Suffix≡ {xs = txs tr}{proj₁ L′}{proj₁ L} (trace∈ tr) l≺
