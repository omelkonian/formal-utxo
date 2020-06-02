-- {-# OPTIONS --allow-unsolved-metas #-}
open import Level          using (0ℓ)
open import Function       using (_$_; _∘_; flip; case_of_)
open import Category.Monad using (RawMonad)

open import Induction.WellFounded using (Acc; acc)

open import Data.Empty               using (⊥; ⊥-elim)
open import Data.Unit                using (⊤; tt)
open import Data.Product             using (_×_; _,_; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂; map₁; map₂)
open import Data.Sum                 using (_⊎_; inj₁; inj₂)
open import Data.Bool                using (T; if_then_else_; true; false)
open import Data.Fin                 using (toℕ)

open import Data.Nat
  renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties

open import Data.Maybe using (Maybe; just; nothing; Is-nothing)
open import Data.Maybe.Relation.Unary.All as MAll using ()
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List
  hiding (_∷ʳ_)
  renaming (sum to ∑ℕ)
open import Data.List.NonEmpty using (List⁺; _∷_; toList; _⁺++_; _++⁺_; _∷⁺_; _∷ʳ_; last)
  renaming ([_] to [_]⁺; map to map⁺; head to head⁺; tail to tail⁺)
open import Data.List.Properties
open import Data.List.Membership.Propositional             using (_∈_; mapWith∈)
open import Data.List.Membership.Propositional.Properties  using (∈-map⁻; ∈-++⁻; ∈-filter⁻; ∈-map⁺)
open import Data.List.Relation.Unary.All as All            using (All; []; _∷_; tabulate)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.Any as Any            using (Any; here; there)
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (here; there)
open import Data.List.Relation.Binary.Pointwise            using (_∷_; Pointwise-≡⇒≡)

open import Relation.Nullary                      using (¬_; yes; no; does)
open import Relation.Unary                        using (Pred)
open import Relation.Binary                       using (Transitive; Decidable; Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans; module ≡-Reasoning)

open import Prelude.General
open import Prelude.Lists

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities
open import UTxO.Validity


module UTxO.TokenProvenance (nft : TokenClass) where

open FocusTokenClass nft

Trace : Set
Trace = List⁺ Tx

origin : Trace → Tx
origin = last

latest : Trace → Tx
latest = head⁺

Provenance : Set
Provenance = List Trace

_∷ᵖ_ : Tx → Provenance → Provenance
tx ∷ᵖ pr = map (tx ∷⁺_) pr

origins : Provenance → List Tx
origins = map origin

originSet : Provenance → List Tx
originSet = deduplicate (λ x y → x ♯ ≟ℕ y ♯) ∘ origins

∑◆ : List Tx → Quantity
∑◆ = ∑ℕ ∘ map (_◆ ∘ forge)

∑ₚ : Provenance → Quantity
∑ₚ = ∑◆ ∘ originSet

∑ₚₛ : List Provenance → Quantity
∑ₚₛ = ∑ₚ ∘ concat

∑ₚ′ : Provenance → Quantity
∑ₚ′ = ∑◆ ∘ origins

∑ₚₛ′ : List Provenance → Quantity
∑ₚₛ′ = ∑ₚ′ ∘ concat

∣_∣ : Provenance → ℕ
∣_∣ = length

-- T0D0: Refer to `o ∈ utxo l` instead
provenance : ∀ L {o} → o ∈ outputsₘ L → Provenance
provenance L = go L (≺′-wf L)
  module Provenance₀ where
    go : ∀ L → Acc _≺′_ L → (∀ {o} → o ∈ outputsₘ L → Provenance)
    go L@(.tx ∷ l , vl₀@(vl ⊕ tx ∶- vtx)) (acc a) {o} o∈
      = concat allPrevs
      module Provenance₁ where
        v  = value o ◆
        rs = prevs vl vtx

        fromForge : List Provenance
        fromForge
          with ◆∈? forge tx
        ... | yes _ = [ [ [ tx ]⁺ ] ]
        ... | no  _ = []

        res→traces : Res vl vtx → Maybe Provenance
        res→traces r@(record {vl′ = vl′; prevOut∈ = o∈′; vl′≺vl = vl′≺vl})
          with ◆∈? resValue r
        ... | yes _ = just $ tx ∷ᵖ go (_ , vl′) (a _ vl′≺vl) o∈′
        ... | no  _ = nothing

        fromPrevs : List Provenance
        fromPrevs = mapMaybe res→traces rs

        allPrevs : List Provenance
        allPrevs = fromForge ++ fromPrevs

--

postulate
  ∑ₚₛ′-++ : ∀ {xs ys} → ∑ₚₛ′ (xs ++ ys) ≡ ∑ₚₛ′ xs + ∑ₚₛ′ ys

  ∑ℕ-helper : ∀ {A : Set} {xs : List A} {f : A → ℕ} {g : A → ℕ}
    → (∀ x → f x ≥ g x)
    → ∑ℕ (map f xs) ≥ ∑ℕ (map g xs)

∑ₚ′≥ : ∀ L {o} (o∈ : o ∈ outputsₘ L) → ∑ₚ′ (provenance L o∈) ≥ value o ◆
∑ₚ′≥ L = go′ L (≺′-wf L)
  module ∑₀ where
    open Provenance₀ L
    go′ : ∀ L (ac : Acc _≺′_ L) → ∀ {o} (o∈ : o ∈ outputsₘ L) → ∑ₚ′ (go {o} L ac o∈) ≥ value o ◆
    go′ L@(.tx ∷ l , vl₀@(vl ⊕ tx ∶- vtx)) (acc a) {o} o∈
      = qed
      module ∑₁ where
        open Provenance₁ {o} tx l vl vtx a {o} o∈

        ∑prev = ∑ rs resValue
        ∑all  = forge tx +ᶜ ∑prev

        pv₀ : ∑all ≡ ∑ᵥ (outputs tx)
        pv₀ = ∑M≡just (∑prevs≡ vl vtx) (preservesValues vtx)

        pv₁ : T $ ∑all ≥ᶜ value o
        pv₁ = ≥ᶜ-trans {x = ∑all} {y = ∑ᵥ (outputs tx)} {z = value o} (≥ᶜ-refl′ pv₀) (∑-≥ᶜ {fv = value} o∈)

        pv₂ : ∑all ◆ ≥ v
        pv₂ = ≥ᶜ-◆ {x = ∑all} {y = value o} pv₁

        ∑forge≡ : ∑ₚₛ′ fromForge ≡ forge tx ◆
        ∑forge≡ with ◆∈? forge tx
        ... | yes _ = +-identityʳ (forge tx ◆)
        ... | no ¬p = sym $ ¬x>0⇒x≡0 ¬p

        -- ∑-helper : ∑ℕ (map (_◆ ∘ resValue) rs) ≡ ∑ₚₛ′ (mapMaybe res→traces rs)
        -- ∑-helper = ∑-mapMaybe {xs = rs} {fm = res→traces} {g = resValue} {fv = ∑ₚ′} p₁ p₂
        --   where
        --     p₁ : ∀ r → Is-nothing (res→traces r) → resValue r ◆ ≡ 0
        --     p₁ r rn with ◆∈? resValue r | rn
        --     ... | yes _ | MAll.just ()
        --     ... | no ¬p | _           = ¬x>0⇒x≡0 ¬p

        --     p₂ : ∀ r v → res→traces r ≡ just v → resValue r ◆ ≡ ∑ₚ′ v
        --     p₂ r v rj with ◆∈? resValue r | rj
        --     ... | yes _ | refl = refl
        --     ... | no  _ | ()

        fv : Res vl vtx → Quantity
        fv r = case res→traces r of λ
          { nothing   → 0
          ; (just pr) → ∑ₚ′ pr }

        h₁ : ∑ℕ (map (_◆ ∘ resValue) rs) ≤ ∑ℕ (map fv rs)
        h₁ = ∑ℕ-helper {xs = rs} {f = fv} {g = _◆ ∘ resValue} h₁′
          where
            h₁′ : ∀ r → resValue r ◆ ≤ fv r
            h₁′ r@(record {vl′ = vl′; prevOut = o′; prevOut∈ = o∈′; vl′≺vl = vl′≺vl})
              -- with pr ← go {o′} (_ , vl′) (a _ vl′≺vl) o∈′
              with ◆∈? resValue r
            ... | yes _ = {!!} -- go′ (_ , vl′) (a _ vl′≺vl) o∈′
            ... | no ¬p rewrite ¬x>0⇒x≡0 ¬p = z≤n

        h₂ : ∑ₚₛ′ (mapMaybe res→traces rs) ≡ ∑ℕ (map fv rs)
        h₂ with rs
        ... | [] = refl
        ... | r ∷ rs
          with ◆∈? resValue r
        ... | yes _ = {!!}
        ... | no  _ = {!!}
        -- ∑ℕ $ map (λ r → case res→traces of λ{ nothing → 0; just pr → ∑ℕ (map (_◆ ∘ forge) (origins pr)}) rs
        -- ∑ℕ $ map (λ r → case res→traces of λ{ nothing → 0; just pr → ∑ₚ′ pr}) rs
        -- ∑ℕ $ map (_◆ ∘ forge) $ origins $ concat $ mapMaybe res→traces rs
        -- ∑ₚₛ′ (mapMaybe res→traces rs)

        ∑fromPrevs≥ : ∑prev ◆ ≤ ∑ₚₛ′ fromPrevs
        ∑fromPrevs≥ = begin ∑prev ◆                       ≡⟨ ∑-◆ {xs = rs} {f = resValue} ⟩
                            ∑ℕ (map (_◆ ∘ resValue) rs)   ≤⟨ h₁ ⟩
                            ∑ℕ (map fv rs)                ≡⟨ sym h₂ ⟩
                            ∑ₚₛ′ (mapMaybe res→traces rs) ≡⟨⟩
                            ∑ₚₛ′ fromPrevs                ∎
                      where open ≤-Reasoning

        qed : ∑ₚₛ′ allPrevs ≥ v
        qed = begin v                               ≤⟨ pv₂ ⟩
                    ∑all ◆                          ≡⟨⟩
                    (forge tx +ᶜ ∑prev) ◆           ≡⟨ +ᶜ-◆ {x = forge tx} {y = ∑prev} ⟩
                    forge tx ◆     + ∑prev ◆        ≤⟨ ≥-+-swapʳ {x = forge tx ◆} ∑fromPrevs≥ ⟩
                    forge tx ◆     + ∑ₚₛ′ fromPrevs ≡⟨ cong (_+ ∑ₚₛ′ fromPrevs) (sym ∑forge≡) ⟩
                    ∑ₚₛ′ fromForge + ∑ₚₛ′ fromPrevs ≡⟨ sym $ ∑ₚₛ′-++ {xs = fromForge}{fromPrevs} ⟩
                    ∑ₚₛ′ (fromForge ++ fromPrevs)   ≡⟨⟩
                    ∑ₚₛ′ allPrevs ∎
              where open ≤-Reasoning

∑ₚ≥ : ∀ L {o} (o∈ : o ∈ outputsₘ L) → ∑ₚ (provenance L o∈) ≥ value o ◆
∑ₚ≥ L = go′ L (≺′-wf L)
  where
    open Provenance₀ L
    go′ : ∀ L (ac : Acc _≺′_ L) → ∀ {o} (o∈ : o ∈ outputsₘ L) → ∑ₚ (go {o} L ac o∈) ≥ value o ◆
    go′ L@(.tx ∷ l , vl₀@(vl ⊕ tx ∶- vtx)) (acc a) {o} o∈
      = qed
      where
        open Provenance₁ {o} tx l vl vtx a {o} o∈

        ∑prev = ∑ rs resValue
        ∑all  = forge tx +ᶜ ∑prev

        pv₀ : ∑all ≡ ∑ᵥ (outputs tx)
        pv₀ = ∑M≡just (∑prevs≡ vl vtx) (preservesValues vtx)

        pv₁ : T $ ∑all ≥ᶜ value o
        pv₁ = ≥ᶜ-trans {x = ∑all} {y = ∑ᵥ (outputs tx)} {z = value o} (≥ᶜ-refl′ pv₀) (∑-≥ᶜ {fv = value} o∈)

        pv₂ : ∑all ◆ ≥ v
        pv₂ = ≥ᶜ-◆ {x = ∑all} {y = value o} pv₁

        ∑-helper : ∑ℕ (map (_◆ ∘ resValue) rs) ≡ ∑ₚₛ fromPrevs
        ∑-helper = begin ∑ℕ (map (_◆ ∘ resValue) rs)          ≡⟨ {!!} ⟩
                         ∑ₚ (concat $ mapMaybe res→traces rs) ≡⟨⟩
                         ∑ₚₛ (mapMaybe res→traces rs)         ≡⟨⟩
                         ∑ₚₛ fromPrevs                        ∎
                   where open ≡-Reasoning

        ∑fromPrevs≡ : ∑prev ◆ ≡ ∑ₚₛ fromPrevs
        ∑fromPrevs≡ = begin ∑prev ◆                                 ≡⟨ ∑-◆ {xs = rs} {f = resValue} ⟩
                            ∑ℕ (map (_◆ ∘ resValue) rs)             ≡⟨ ∑-helper ⟩
                            ∑ₚₛ fromPrevs                           ∎
                      where open ≡-Reasoning

        ∑allPrevs≡ : ∑ₚₛ allPrevs ≡ ∑all ◆
        ∑allPrevs≡ = begin ∑ₚₛ allPrevs                 ≡⟨⟩
                           ∑ₚₛ (fromForge ++ fromPrevs) ≡⟨ {!!} ⟩
                           forge tx ◆ + ∑ₚₛ fromPrevs   ≡⟨ cong (forge tx ◆ +_) (sym ∑fromPrevs≡) ⟩
                           forge tx ◆ + ∑prev ◆         ≡⟨ sym $ +ᶜ-◆ {x = forge tx} {y = ∑prev} ⟩
                           (forge tx +ᶜ ∑prev) ◆        ≡⟨⟩
                           ∑all ◆                       ∎
                     where open ≡-Reasoning

        qed : ∑ₚₛ allPrevs ≥ v
        qed = subst (_≥ v) (sym ∑allPrevs≡) pv₂

provenance⁺ : ∀ L {o} (o∈ : o ∈ outputsₘ L)
  → ◆∈ value o
  → ∣ provenance L o∈ ∣ > 0
provenance⁺ L o∈ ◆∈v with provenance L o∈ | ∑ₚ′≥ L o∈
... | []    | p = ⊥-elim $ x≡0⇒¬x>0 (x≤0⇒x≡0 p) ◆∈v
... | _ ∷ _ | _ = s≤s z≤n

_↝⟦_⟧_ : Tx → Quantity → Tx → Set
tx ↝⟦ n ⟧ tx′ = Σ[ or∈ ∈ Any ((tx ♯ₜₓ ≡_) ∘ id) (outputRefs tx′) ]
                  ∃[ o ] ( ((outputs tx ⁉ index (Any.lookup or∈)) ≡ just o)
                         × (value o ◆ ≥ n) )

data X (n : Quantity) : List⁺ Tx → Set where
  root :

      (tx : Tx)
      -------------
    → X n (tx ∷ [])

  cons : ∀ {txs tx}

    → X n txs
    → head⁺ txs ↝⟦ n ⟧ tx
      -------------------
    → X n (tx ∷⁺ txs)

record ValidTrace L (tr : Trace) : Set where
  field
    trace∈ : All⁺ (_∈′ L) tr
    linked : X (forge (origin tr) ◆) tr
open ValidTrace public

weakenValidTrace : ∀ {L L′ tr} → L′ ≼′ L → ValidTrace L′ tr → ValidTrace L tr
weakenValidTrace L′≼ record {trace∈ = tr∈; linked = p} = record {trace∈ = All.map (Suffix⇒⊆ L′≼) tr∈; linked = p}

postulate
  ∈-concat-++⁻ : ∀ {A : Set} {x : A} {xs ys : List (List A)}
    → x ∈ concat (xs ++ ys)
    → x ∈ concat xs
    ⊎ x ∈ concat ys

  ∈-concat⁻ :  ∀ {A : Set} {x : A} {xss : List (List A)}
    → x ∈ concat xss
    → ∃ λ xs → (x ∈ xs) × (xs ∈ xss)

validTraces : ∀ L {o} (o∈ : o ∈ outputsₘ L)
  → All (ValidTrace L) (provenance L o∈)
validTraces L = go′ L (≺′-wf L)
  where
    open Provenance₀ L

    go′ : ∀ L (ac : Acc _≺′_ L) → ∀ {o} (o∈ : o ∈ outputsₘ L) → All (ValidTrace L) (go {o} L ac o∈)
    go′ L@(.tx ∷ l , vl₀@(vl ⊕ tx ∶- vtx)) (acc a) {o} o∈
      = All.tabulate qed
      where
        open Provenance₁ {o} tx l vl vtx a {o} o∈

        qed : ∀ {tr} → tr ∈ concat allPrevs → ValidTrace L tr
        qed {tr} tr∈
          with ∈-concat-++⁻ {xs = fromForge}{fromPrevs} tr∈

        qed {tr} tr∈ | inj₁ tr∈ˡ
          with ◆∈? forge tx | tr∈ˡ
        ... | yes _ | here refl
            = record { trace∈ = here refl ∷ [] ; linked = root tx }
        ... | no  _ | ()

        qed {tr} tr∈ | inj₂ tr∈ʳ
          with pr , tr∈pr , pr∈ ← ∈-concat⁻ tr∈ʳ
          with r@(record { vl′ = vl′; prevTx = ptx; prevOut = o′; prevOut∈ = o∈′
                         ; vl′≺vl = vl′≺vl; or∈ = or∈; ⁉≡just = ⁉≡just })
             , r∈ , rj ← ∈-mapMaybe⁻ {xs = rs} {f = res→traces} pr∈
          with ◆∈? resValue r | rj
        ... | yes ◆∈v | refl
            = All.lookup h′ tr∈pr
          where
            pr′ : Provenance
            pr′ = go {o′} (_ , vl′) (a _ vl′≺vl) o∈′

            h : All (ValidTrace L) pr′
            h = All.map (weakenValidTrace (≺′⇒≼′ {l = L}{_ , vl′} vl′≺vl)) (go′ (_ , vl′) (a _ vl′≺vl) o∈′)

            ∀head≡ : All ((_≡ ptx) ∘ head⁺) pr′
            ∀head≡ = {!!}

            hh : ∀ {tr} → tr ∈ pr′ → ValidTrace L (tx ∷⁺ tr)
            hh {tr₀} tr∈₀
              with tr₀ | All.lookup ∀head≡ tr∈₀ | tr∈₀
            ... | .ptx ∷ txs | refl | tr∈
              -- rewrite All.lookup ∀head≡ tr∈
              = vtr′
              where
                tr′ = ptx ∷ txs
                tx₀ = origin $ tx ∷⁺ ptx ∷ txs

                vtr : ValidTrace L tr′
                vtr = All.lookup h tr∈

                lnk : X (forge tx₀ ◆) tr′
                lnk rewrite last-∷ {x = tx}{ptx}{tail⁺ tr′} = linked vtr

                v≥ : value o′ ◆ ≥ forge tx₀ ◆
                v≥ = {!!}

                tx↝ : ptx ↝⟦ forge tx₀ ◆ ⟧ tx
                tx↝ = or∈ , o′ , ⁉≡just , v≥

                lnk′ : X (forge tx₀ ◆) (tx ∷⁺ tr′)
                lnk′ = cons lnk tx↝

                vtr′ : ValidTrace L (tx ∷⁺ tr′)
                vtr′ = record {trace∈ = here refl ∷ trace∈ vtr; linked = lnk′}

            h′ : All (ValidTrace L) (tx ∷ᵖ pr′)
            h′ = All.map⁺ {f = tx ∷⁺_} $ All.tabulate hh

private
  variable
    L : ∃ ValidLedger
    tr : Trace

origin∈ : ValidTrace L tr → origin tr ∈′ L
origin∈ = All⁺-last ∘ trace∈

mkPendingMPS : ValidTrace L tr → HashId → PendingMPS
mkPendingMPS {tr = tr} vtr = toPendingMPS (proj₁ $ ∈⇒Suffix $ origin∈ vtr) (origin tr)
