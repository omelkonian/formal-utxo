open import Level          using (0ℓ)
open import Function       using (_$_; _∘_; flip)
open import Category.Monad using (RawMonad)

open import Induction.WellFounded using (Acc; acc)

open import Data.Empty               using (⊥; ⊥-elim)
open import Data.Unit                using (⊤; tt)
open import Data.Product             using (_×_; _,_; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂; map₁; map₂)
open import Data.Sum                 using (_⊎_; inj₁; inj₂)
open import Data.Bool                using (T; if_then_else_)
open import Data.Fin                 using (toℕ)

open import Data.Nat
open import Data.Nat.Properties

open import Data.Maybe using (Maybe; just; nothing; Is-nothing)
open import Data.Maybe.Relation.Unary.All as MAll using ()
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List
  renaming (sum to ∑ℕ)
open import Data.List.NonEmpty using (List⁺; _∷_; head; toList; _⁺++_; _++⁺_; _∷⁺_)
  renaming ([_] to [_]⁺)
open import Data.List.Properties
open import Data.List.Membership.Propositional             using (_∈_; mapWith∈)
open import Data.List.Membership.Propositional.Properties  using (∈-map⁻; ∈-++⁻; ∈-filter⁻; ∈-map⁺)
open import Data.List.Relation.Unary.All as All            using (All; []; _∷_; tabulate)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.Any as Any            using (Any; here; there)
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (here; there)
open import Data.List.Relation.Binary.Pointwise            using (_∷_; Pointwise-≡⇒≡)

open import Relation.Nullary                            using (¬_; yes; no)
open import Relation.Unary                              using (Pred)
open import Relation.Binary                             using (Transitive)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; sym; subst; cong; trans; inspect)
  renaming ([_] to ≡[_])
open Eq.≡-Reasoning

open import Prelude.General
open import Prelude.Lists

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities
open import UTxO.Validity


module UTxO.FocusedProvenance (nft : TokenClass) where

open FocusTokenClass nft

private
  variable
    n : Quantity

-- ** Definitions

ForgingTx : Quantity → Set
ForgingTx n = ∃ λ tx → (forge tx ◆ ≥ n) × ∃ (IsValidTx tx)

mkForgingTx : ∀ {l} tx → IsValidTx tx l → ForgingTx (forge tx ◆)
mkForgingTx tx vtx = tx , ≤-refl , _ , vtx

record Origins (n : Quantity) : Set where
  field
    origins : List (∃ ForgingTx)
    sums    : ∑₁ origins ≥ n
open Origins public

record Origins⁺ (n : Quantity) : Set where
  field
    origins⁺ : List⁺ (∃ ForgingTx)
    sums⁺    : ∑₁⁺ origins⁺ ≥ n
open Origins⁺ public

---------------
-- Utilities

emptyOrigins : ∀ {n} → n ≡ 0 → Origins n
emptyOrigins refl = record {origins = []; sums = z≤n}

singleOrigins : ∀ {l} tx → IsValidTx tx l → Origins⁺ (forge tx ◆)
origins⁺ (singleOrigins tx vtx) = [ _ , mkForgingTx tx vtx ]⁺
sums⁺    (singleOrigins tx _) rewrite +-identityʳ (forge tx ◆) = ≤-refl

origins⇒origins⁺ : (os : Origins n) → ¬Null (origins os) → Origins⁺ n
origins⇒origins⁺ {n = n} record {origins = os; sums = ∑≥} os≢[] = record
  { origins⁺ = toList⁺ os os≢[]
  ; sums⁺    = subst ((_≥ n) ∘ ∑₁) (sym $ toList∘toList⁺ os os≢[]) ∑≥
  }

origins⁺⇒origins : Origins⁺ n → Origins n
origins⁺⇒origins record {origins⁺ = os;         sums⁺ = ∑≥}
               = record {origins  = toList os ; sums  = ∑≥}

merge : (oss : List (∃ Origins⁺))
      → ∑₁ oss ≥ n
      → Origins n

merge⁺ : (oss : List⁺ (∃ Origins⁺))
       → ∑₁⁺ oss ≥ n
       → Origins⁺ n

merge {.0} [] z≤n                = emptyOrigins {0} refl
merge  {n} ((osᵥ , os) ∷ oss) ∑≥ = origins⁺⇒origins $ merge⁺ {n} ((osᵥ , os) ∷ oss) ∑≥
merge⁺ {n} ((osᵥ , os) ∷ oss) ∑≥ = qed
  where
    ossᵥ = ∑₁ oss

    os′ : Origins ossᵥ
    os′ = merge {n = ossᵥ} oss ≤-refl

    p : ∑₁⁺ (origins⁺ os) ≥ osᵥ
    p = sums⁺ os

    p₀′ : ∑₁⁺ (origins⁺ os) + ossᵥ ≥ ∑₁⁺ ((osᵥ , os) ∷ oss)
    p₀′ = ≥-+-swapˡ {x = ∑₁⁺ (origins⁺ os)} {x′ = osᵥ} {y = ossᵥ} (sums⁺ os)

    p₀ : ∑₁⁺ (origins⁺ os) + ossᵥ ≥ n
    p₀ = ≥-trans {i = ∑₁⁺ (origins⁺ os) + ossᵥ} {j = ∑₁⁺ ((osᵥ , os) ∷ oss)} {k = n} p₀′ ∑≥

    p₁ : ∑₁⁺ (origins⁺ os) + ∑₁ (origins os′) ≥ n
    p₁ = ≥-trans {i = ∑₁⁺ (origins⁺ os) + ∑₁ (origins os′)} {j = ∑₁⁺ (origins⁺ os) + ossᵥ} {k = n}
                 (≥-+-swapʳ {x = ∑₁⁺ (origins⁺ os)} {y = ∑₁ (origins os′)} {y′ = ossᵥ} (sums os′))
                 p₀

    qed : Origins⁺ n
    qed = record
      { origins⁺ = origins⁺ os ⁺++ origins os′
      ; sums⁺    = subst (_≥ n) (sym $ ∑₁-⁺++ {xs = origins⁺ os} {ys = origins os′}) p₁
      }

-- ** Provenance

provenance : ∀ l
  → ∀ {o} → o ∈ outputsₘ l
  → ◆∈ value o
  → Origins⁺ (value o ◆)
provenance l = go l (≺′-wf l)
  module Provenance₀ where
    go : ∀ l → Acc _≺′_ l → (∀ {o} → o ∈ outputsₘ l → ◆∈ value o → Origins⁺ (value o ◆))
    go (.tx ∷ l , vl₀@(vl ⊕ tx ∶- vtx)) (acc a) {o} o∈ ◆∈v
      = qed
      module Provenance₁ where
        v  = value o ◆
        rs = prevs vl vtx

        ∃Origins>0 : Set
        ∃Origins>0 = ∃ λ n → Origins⁺ n × (n > 0)

        fromForge : List (∃ Origins⁺)
        fromForge
          with forge tx ◆ >? 0
        ... | yes p = [ _ , singleOrigins tx vtx ]
        ... | no ¬p = []

        res→origins : Res vl vtx → Maybe (∃ Origins⁺)
        res→origins r@(record {vl′ = vl′; prevOut∈ = prevOut∈; vl′≺vl = vl′≺vl})
          with resValue r ◆ >? 0
        ... | yes p = just $ _ , go (_ , vl′) (a _ vl′≺vl) prevOut∈ p
        ... | no  _ = nothing

        fromPrevs : List (∃ Origins⁺)
        fromPrevs = mapMaybe res→origins rs

        allPrevs : List (∃ Origins⁺)
        allPrevs = fromForge ++ fromPrevs

--
        ∑prev = ∑ rs resValue
        ∑all  = forge tx +ᶜ ∑prev

        pv₀ : ∑all ≡ fee tx +ᶜ ∑ᵥ (outputs tx)
        pv₀ = ∑M≡just (∑prevs≡ vl vtx) (preservesValues vtx)

        pv₁ : T $ ∑all ≥ᶜ ∑ᵥ (outputs tx)
        pv₁ = +ᶜ-≡⇒≥ᶜ {x = ∑all} {z = fee tx} {w = ∑ᵥ (outputs tx)} (≥ᶜ-refl′ pv₀)

        pv₂ : T $ ∑all ≥ᶜ value o
        pv₂ = ≥ᶜ-trans {x = ∑all} {y = ∑ᵥ (outputs tx)} {z = value o} pv₁ (∑-≥ᶜ {fv = value} o∈)

        ∑forge≡ : ∑₁ fromForge ≡ forge tx ◆
        ∑forge≡ with forge tx ◆ >? 0
        ... | yes _ = +-identityʳ (forge tx ◆)
        ... | no ¬p = sym $ ¬x>0⇒x≡0 ¬p

        ∑-helper : ∑ℕ (map (_◆ ∘ resValue) rs) ≡ ∑₁ (mapMaybe res→origins rs)
        ∑-helper = ∑-mapMaybe {xs = rs} {fm = res→origins} {g = resValue} p₁ p₂
          where
            p₁ : ∀ r → Is-nothing (res→origins r) → resValue r ◆ ≡ 0
            p₁ r rn with resValue r ◆ >? 0 | rn
            ... | yes _ | MAll.just ()
            ... | no ¬p | _           = ¬x>0⇒x≡0 ¬p

            p₂ : ∀ r v → res→origins r ≡ just v → resValue r ◆ ≡ proj₁ v
            p₂ r v rj with resValue r ◆ >? 0 | rj
            ... | yes _ | refl = refl
            ... | no  _ | ()

        ∑fromPrevs≡ : ∑₁ fromPrevs ≡ ∑prev ◆
        ∑fromPrevs≡ = sym
                    $ begin ∑prev ◆                                  ≡⟨ ∑-◆ {xs = rs} {f = resValue} ⟩
                            ∑ℕ (map (_◆ ∘ resValue) rs)              ≡⟨ ∑-helper ⟩
                            ∑ℕ (map proj₁ (mapMaybe res→origins rs)) ≡⟨⟩
                            ∑₁ (mapMaybe res→origins rs)             ≡⟨⟩
                            ∑₁ fromPrevs                             ∎

        ∑allPrevs≡ : ∑₁ allPrevs ≡ ∑all ◆
        ∑allPrevs≡ = begin ∑₁ allPrevs                 ≡⟨ ∑₁-++ {xs = fromForge} {ys = fromPrevs} ⟩
                           ∑₁ fromForge + ∑₁ fromPrevs ≡⟨ cong (_+ ∑₁ fromPrevs) ∑forge≡ ⟩
                           forge tx ◆   + ∑₁ fromPrevs ≡⟨ cong (forge tx ◆ +_)   ∑fromPrevs≡ ⟩
                           forge tx ◆   + ∑prev ◆      ≡⟨ sym $ +ᶜ-◆ {x = forge tx} {y = ∑prev} ⟩
                           (forge tx +ᶜ ∑prev) ◆       ≡⟨⟩
                           ∑all ◆                      ∎

        allPrevs≢[] : ¬Null allPrevs
        allPrevs≢[] ap≡[] = x≡0⇒¬x>0 {value o ◆} v≡0 ◆∈v
          where
            null× : Null fromForge × Null fromPrevs
            null× = Null-++⁻ {xs = fromForge} {ys = fromPrevs} ap≡[]

            l≡0 : forge tx ◆ ≡ 0
            l≡0 with forge tx ◆ >? 0 | proj₁ null×
            ... | yes p | ()
            ... | no ¬p | _  = ¬x>0⇒x≡0 ¬p

            p₀ : All (Is-nothing ∘ res→origins) rs
            p₀ = mapMaybe≡[]⇒All-nothing $ proj₂ null×

            p₁ : All (_≡ 0) (map (_◆ ∘ resValue) rs)
            p₁ = All.map⁺ $ All.map {P = Is-nothing ∘ res→origins} {Q = (_≡ 0) ∘ _◆ ∘ resValue} P⇒Q p₀
              where
                P⇒Q : ∀ {r} → Is-nothing (res→origins r) → resValue r ◆ ≡ 0
                P⇒Q {r} ≡nothing with resValue r ◆ >? 0 | ≡nothing
                ... | yes _ | MAll.just ()
                ... | no ¬p | _ = ¬x>0⇒x≡0 ¬p

            r≡0 : ∑prev ◆ ≡ 0
            r≡0 rewrite ∑-◆ {xs = rs} {f = resValue} = ∑ℕ-∀≡0 p₁

            ∑≡0 : forge tx ◆ + ∑prev ◆ ≡ 0
            ∑≡0 rewrite l≡0 | r≡0 = refl

            ∑≡0′ : ∑all ◆ ≡ 0
            ∑≡0′ = trans (+ᶜ-◆ {x = forge tx} {y = ∑prev}) ∑≡0

            pv₂′ : ∑all ◆ ≥ v
            pv₂′ = ≥ᶜ-◆ {x = ∑all} {y = value o} pv₂

            v≡0 : v ≡ 0
            v≡0 = x≤0⇒x≡0 (subst (_≥ v) ∑≡0′ pv₂′)
--

        ∑≥ : ∑₁ allPrevs ≥ v
        ∑≥ = subst (_≥ v) (sym ∑allPrevs≡) (≥ᶜ-◆ {x = ∑all} {y = value o} pv₂)

        allPrevs⁺ : List⁺ (∃ Origins⁺)
        allPrevs⁺ = toList⁺ allPrevs allPrevs≢[]

        ∑≥′ : ∑₁⁺ allPrevs⁺ ≥ v
        ∑≥′ = subst ((_≥ v) ∘ ∑₁) (sym $ toList∘toList⁺ allPrevs allPrevs≢[]) ∑≥

        qed : Origins⁺ v
        qed = merge⁺ allPrevs⁺ ∑≥′
