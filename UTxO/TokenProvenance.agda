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
  renaming ([_] to [_]⁺; map to map⁺)
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


module UTxO.TokenProvenance (nft : TokenClass) where

open FocusTokenClass nft

private
  variable
    n : Quantity

-- ** Definitions

ForgingTx : ∃ ValidLedger → Quantity → Set
ForgingTx L n = ∃ λ tx → (forge tx ◆ ≥ n) × (tx ∈′ L)

mkForgingTx : ∀ {tx l} → (vl : ValidLedger (tx ∷ l)) → ForgingTx (_ , vl) (forge tx ◆)
mkForgingTx (vl ⊕ tx ∶- _) = tx , ≤-refl , here refl

mkPendingMPS : ∀ {L} → ForgingTx L n → HashId → PendingMPS
mkPendingMPS (tx , _ , tx∈) = toPendingMPS (proj₁ $ ∈⇒Suffix tx∈) tx

record Origins (L : ∃ ValidLedger) (n : Quantity) : Set where
  field
    origins : List (∃ $ ForgingTx L)
    sums    : ∑₁ origins ≥ n
open Origins public

record Origins⁺ (L : ∃ ValidLedger) (n : Quantity) : Set where
  field
    origins⁺ : List⁺ (∃ $ ForgingTx L)
    sums⁺    : ∑₁⁺ origins⁺ ≥ n
open Origins⁺ public

---------------
-- Utilities

weakenForgingTx : ∀ {L L′} → L′ ≼′ L → ForgingTx L′ n → ForgingTx L n
weakenForgingTx L′≼ (tx , frg≥ , tx∈) = tx , frg≥ , Suffix⇒⊆ L′≼ tx∈

weakenOrigins : ∀ {L L′} → L′ ≼′ L → Origins L′ n → Origins L n
weakenOrigins {n} {L} {L′} L′≼ record {origins = os; sums = sums} = record { origins = os′; sums = sums′ }
  where
    os′ : List (∃ $ ForgingTx L)
    os′ = map (map₂ $ weakenForgingTx {L = L}{L′} L′≼) os

    ∑≡ : ∑₁ os′ ≡ ∑₁ os
    ∑≡ = ∑₁-map₂ {X = ForgingTx L′} {Y = ForgingTx L} {xs = os}
                 {f = λ {n} frgTx → weakenForgingTx {L = L}{L′} L′≼ frgTx}

    sums′ : ∑₁ os′ ≥ n
    sums′ rewrite ∑≡ = sums

weakenOrigins⁺ : ∀ {L L′} → L′ ≼′ L → Origins⁺ L′ n → Origins⁺ L n
weakenOrigins⁺ {n} {L} {L′} L′≼ record {origins⁺ = os; sums⁺ = sums} = record {origins⁺ = os′; sums⁺ = sums′}
  where
    os′ : List⁺ (∃ $ ForgingTx L)
    os′ = map⁺ (map₂ $ weakenForgingTx {L = L}{L′} L′≼) os


    ∑≡ : ∑₁⁺ os′ ≡ ∑₁⁺ os
    ∑≡ rewrite ∑₁-map₂ {X = ForgingTx L′} {Y = ForgingTx L} {xs = toList os}
                       {f = λ {n} frgTx → weakenForgingTx {L = L}{L′} L′≼ frgTx}
             = refl

    sums′ : ∑₁⁺ os′ ≥ n
    sums′ rewrite ∑≡ = sums

emptyOrigins : ∀ {L n} → n ≡ 0 → Origins L n
emptyOrigins refl = record {origins = []; sums = z≤n}

singleOrigins : ∀ {tx l} → (vl : ValidLedger (tx ∷ l)) → Origins⁺ (_ , vl) (forge tx ◆)
origins⁺ (singleOrigins vl) = [ _ , mkForgingTx vl ]⁺
sums⁺    (singleOrigins {tx = tx} _) rewrite +-identityʳ (forge tx ◆) = ≤-refl

origins⇒origins⁺ : ∀ {L} → (os : Origins L n) → ¬Null (origins os) → Origins⁺ L n
origins⇒origins⁺ {n = n} record {origins = os; sums = ∑≥} os≢[] = record
  { origins⁺ = toList⁺ os os≢[]
  ; sums⁺    = subst ((_≥ n) ∘ ∑₁) (sym $ toList∘toList⁺ os os≢[]) ∑≥ }

origins⁺⇒origins : ∀ {L} → Origins⁺ L n → Origins L n
origins⁺⇒origins record {origins⁺ = os;         sums⁺ = ∑≥}
               = record {origins  = toList os ; sums  = ∑≥}

merge : ∀ {L}
  → (oss : List (∃ $ Origins⁺ L))
  → ∑₁ oss ≥ n
  → Origins L n

merge⁺ : ∀ {L}
  → (oss : List⁺ (∃ $ Origins⁺ L))
  → ∑₁⁺ oss ≥ n
  → Origins⁺ L n

merge  {n = .0} {L = L} [] z≤n                = emptyOrigins {n = 0} refl
merge  {n = n}  {L = L} ((osᵥ , os) ∷ oss) ∑≥ = origins⁺⇒origins $ merge⁺ {n} ((osᵥ , os) ∷ oss) ∑≥
merge⁺ {n = n}  {L = L} ((osᵥ , os) ∷ oss) ∑≥ = qed
  where
    ossᵥ = ∑₁ oss

    os′ : Origins L ossᵥ
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

    qed : Origins⁺ L n
    qed = record
      { origins⁺ = origins⁺ os ⁺++ origins os′
      ; sums⁺    = subst (_≥ n) (sym $ ∑₁-⁺++ {xs = origins⁺ os} {ys = origins os′}) p₁ }

-- ** Provenance

provenance : ∀ L
  → ∀ {o} → o ∈ outputsₘ L
  → ◆∈ value o
  → Origins⁺ L (value o ◆)
provenance L = go L (≺′-wf L)
  module Provenance₀ where
    go : ∀ L → Acc _≺′_ L → (∀ {o} → o ∈ outputsₘ L → ◆∈ value o → Origins⁺ L (value o ◆))
    go L@(.tx ∷ l , vl₀@(vl ⊕ tx ∶- vtx)) (acc a) {o} o∈ ◆∈v
      = qed
      module Provenance₁ where
        v  = value o ◆
        rs = prevs vl vtx

        fromForge : List (∃ $ Origins⁺ L)
        fromForge
          with forge tx ◆ >? 0
        ... | yes p = [ _ , singleOrigins vl₀ ]
        ... | no ¬p = []

        res→origins : Res vl vtx → Maybe (∃ $ Origins⁺ L)
        res→origins r@(record {vl′ = vl′; prevOut∈ = prevOut∈; vl′≺vl = vl′≺vl})
          with resValue r ◆ >? 0
        ... | yes p = just os′
          where
            L′ : ∃ ValidLedger
            L′ = _ , vl′

            os : ∃ $ Origins⁺ L′
            os = _ , go L′ (a _ vl′≺vl) prevOut∈ p

            os′ : ∃ $ Origins⁺ L
            os′ = map₂ (weakenOrigins⁺ (≺′⇒≼′ {l = L}{L′} vl′≺vl)) os

        ... | no  _ = nothing

        fromPrevs : List (∃ $ Origins⁺ L)
        fromPrevs = mapMaybe res→origins rs

        allPrevs : List (∃ $ Origins⁺ L)
        allPrevs = fromForge ++ fromPrevs

--
        ∑prev = ∑ rs resValue
        ∑all  = forge tx +ᶜ ∑prev

        pv₀ : ∑all ≡ ∑ᵥ (outputs tx)
        pv₀ = ∑M≡just (∑prevs≡ vl vtx) (preservesValues vtx)

        pv₁ : T $ ∑all ≥ᶜ value o
        pv₁ = ≥ᶜ-trans {x = ∑all} {y = ∑ᵥ (outputs tx)} {z = value o} (≥ᶜ-refl′ pv₀) (∑-≥ᶜ {fv = value} o∈)

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

            pv₂ : ∑all ◆ ≥ v
            pv₂ = ≥ᶜ-◆ {x = ∑all} {y = value o} pv₁

            v≡0 : v ≡ 0
            v≡0 = x≤0⇒x≡0 (subst (_≥ v) ∑≡0′ pv₂)
--

        ∑≥ : ∑₁ allPrevs ≥ v
        ∑≥ = subst (_≥ v) (sym ∑allPrevs≡) (≥ᶜ-◆ {x = ∑all} {y = value o} pv₁)

        allPrevs⁺ : List⁺ (∃ $ Origins⁺ L)
        allPrevs⁺ = toList⁺ allPrevs allPrevs≢[]

        ∑≥′ : ∑₁⁺ allPrevs⁺ ≥ v
        ∑≥′ = subst ((_≥ v) ∘ ∑₁) (sym $ toList∘toList⁺ allPrevs allPrevs≢[]) ∑≥

        qed : Origins⁺ L v
        qed = merge⁺ allPrevs⁺ ∑≥′
