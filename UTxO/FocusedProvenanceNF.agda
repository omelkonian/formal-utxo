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

open import Data.Maybe using (Maybe; just; nothing; Is-just; Is-nothing)
open import Data.Maybe.Relation.Unary.All as MAll using ()
open import Data.Maybe.Relation.Unary.Any as MAny using ()
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List hiding (tail)
  renaming (sum to ∑ℕ)
open import Data.List.NonEmpty using (List⁺; _∷_; head; tail; toList; _⁺++_; _++⁺_; _∷⁺_)
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
open import Relation.Unary as Unary                     using (Pred)
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
open import UTxO.GlobalPreservation


module UTxO.FocusedProvenanceNF (nft : TokenClass) where

open FocusTokenClass nft
open import UTxO.FocusedProvenance nft

-- ** Definitions

NonFungible : ∃ ValidLedger → TokenClass → Set
NonFungible (l , _) nft = ∑ l forge ◇ nft ≤ 1

SingleOrigin : ∀ {n} → Origins n → Set
SingleOrigin = Singleton ∘ origins

SingleOrigin⁺ : ∀ {n} → Origins⁺ n → Set
SingleOrigin⁺ = Singleton⁺ ∘ origins⁺

SingleOrigin² : List (∃ Origins⁺) → Set
SingleOrigin² os = Singleton os × All (SingleOrigin⁺ ∘ proj₂) os

SingleOrigin²⁺ : List⁺ (∃ Origins⁺) → Set
SingleOrigin²⁺ os = Singleton⁺ os × All⁺ (SingleOrigin⁺ ∘ proj₂) os

destruct-SingleOrigin⁺ : ∀ {n} {os : Origins⁺ n}
  → SingleOrigin⁺ os
  → Σ[ tx ∈ ∃ ForgingTx ] (origins⁺ os ≡ [ tx ]⁺)
destruct-SingleOrigin⁺ {n} {os} s-os
  with tx , refl ← destruct-Singleton⁺ s-os
     = tx , refl

-- ** Lemmas

singleOrigin²⇒singleOrigin²⁺ : ∀ {oss : List (∃ Origins⁺)} {p : ¬Null oss}
  → SingleOrigin² oss
  → SingleOrigin²⁺ (toList⁺ oss p)
singleOrigin²⇒singleOrigin²⁺ {oss} {p} (s-oss , ∀p) = singleton⇒singleton⁺ {xs≢[] = p} s-oss , All⇒All⁺ ∀p

singleOrigin-merge : ∀ {n} {oss : List⁺ (∃ Origins⁺)} {p : ∑₁⁺ oss ≥ n}
  → SingleOrigin²⁺ oss
  → SingleOrigin⁺ (merge⁺ oss p)
singleOrigin-merge {n = n} {oss} {p} (s-oss , ∀-oss)
  with destruct-Singleton⁺ s-oss | ∀-oss
... | (_ , os) , refl | s-os ∷ []
  rewrite ++-identityʳ (tail $ origins⁺ os)
        | proj₂ $ destruct-Singleton⁺ s-os
        = tt

NF-weaken : ∀ {l l′} → l′ ≺′ l → NonFungible l nft → NonFungible l′ nft
NF-weaken {l , _} {l′ , _} vl′≺ = ≤-trans (≥ᶜ-◆ {x = ∑ l forge} {y = ∑ l′ forge} $ ≺-∑forge vl′≺)

nf-prevs : ∀ {tx l} {vl : ValidLedger l} {vtx : IsValidTx tx l}
  → NonFungible (_ , vl ⊕ tx ∶- vtx) nft
  → count (◆∈?_ ∘ resValue) (prevs vl vtx) + forge tx ◆ ≤ 1
nf-prevs {tx} {l} {vl} {vtx} nf
  = qed
  where
    rs  = prevs vl vtx

    ∑utxo = ∑ (utxo l) (value ∘ out)
    ∑frg  = ∑ l forge

    frg≥utxo : T $ ∑frg ≥ᶜ ∑utxo
    frg≥utxo = +ᶜ-≡⇒≤ᶜ {v₁ = ∑ l fee} {v₂ = ∑utxo} $ globalPreservation {l} {vl}

    lookup≤ₗ : ∑frg ◆ ≥ ∑utxo ◆
    lookup≤ₗ = ≥ᶜ-◆ {x = ∑frg} {y = ∑utxo} frg≥utxo

    count≤ₗ : count ◆∈?_ (map resValue rs) ≤ count ◆∈?_ (map (value ∘ out) (utxo l))
    count≤ₗ = ⊆⇒count≤ ◆∈?_ (prevs⊆utxo {tx} {l} {vl} {vtx})

    frg≤1 : forge tx ◆ ≤ 1
    frg≤1 = ≤-+ˡ {x = forge tx ◆} {y = ∑ l forge ◆} {z = 1}
               $ subst (_≤ 1) (+ᶜ-◆ {x = forge tx} {y = ∑ l forge}) nf


    qed : count (◆∈?_ ∘ resValue) rs + (forge tx ◆) ≤ 1
    qed
      with ◆∈? forge tx
    ... | no ¬p
        rewrite ¬x>0⇒x≡0 ¬p | +-identityʳ $ count (◆∈?_ ∘ resValue) rs
        = subst (_≤ 1) (sym $ count-map⁺ {xs = rs} {f = resValue} {P? = ◆∈?_}) qed′
      where
        lookup≤ᵣ : ∑frg ◆ ≤ 1
        lookup≤ᵣ = subst (_≤ 1) (◆-+ᶜ-reject {v = forge tx} {vs = ∑frg} ¬p) nf

        lookup≤ : ∑utxo ◆ ≤ 1
        lookup≤ = ≤-trans lookup≤ₗ lookup≤ᵣ

        count≤ᵣ : count ◆∈?_ (map (value ∘ out) (utxo l)) ≤ 1
        count≤ᵣ = ∑◆≤1⇒count≤1 {vs = map (value ∘ out) (utxo l)} lookup≤

        qed′ : count ◆∈?_ (map resValue rs) ≤ 1
        qed′ = ≤-trans count≤ₗ count≤ᵣ

    ... | yes p = qed′
      where
        ∑frg≤0 : ∑frg ◆ ≤ 0
        ∑frg≤0 = ◆-≤-weaken {v = forge tx} {vs = ∑frg} {n = 0} nf p

        ∑utxo≡0 : ∑utxo ◆ ≡ 0
        ∑utxo≡0 = x≤0⇒x≡0 $ ≤-trans lookup≤ₗ ∑frg≤0

        count≡0″ : count ◆∈?_ (map (value ∘ out) (utxo l)) ≡ 0
        count≡0″ = ∑◆≡0⇒count≡0 {vs = map (value ∘ out) (utxo l)} ∑utxo≡0

        count≡0′ : count ◆∈?_ (map resValue rs) ≡ 0
        count≡0′ = x≤0⇒x≡0′ count≡0″ count≤ₗ

        count≡0 : count (◆∈?_ ∘ resValue) rs ≡ 0
        count≡0 = subst (_≡ 0) (sym $ count-map⁺ {xs = rs} {f = resValue} {P? = ◆∈?_}) count≡0′

        qed′ : count (◆∈?_ ∘ resValue) rs + forge tx ◆ ≤ 1
        qed′ rewrite count≡0 | +-identityˡ (forge tx ◆) = frg≤1

-- ** Provenance for non-fungible tokens

provenanceNF : ∀ l → ∀ {o} → (o∈ : o ∈ outputsₘ l)
  → (◆∈v : ◆∈ value o)
  → NonFungible l nft
  → SingleOrigin⁺ (provenance l o∈ ◆∈v)
provenanceNF l = go′ l (≺′-wf l)
  where
    open Provenance₀ l

    go′ : ∀ l → (ac : Acc _≺′_ l)
        → ∀ {o} (o∈ : o ∈ outputsₘ l)
        → (◆∈v : ◆∈ value o)
        → NonFungible l nft
        → SingleOrigin⁺ (go {o} l ac {o} o∈ ◆∈v)
    go′ (.tx ∷ l , vl₀@(vl ⊕ tx ∶- vtx)) (acc a) {o} o∈ ◆∈v nf
      = qed′
      where
        open Provenance₁ {o} tx l vl vtx a {o} o∈ ◆∈v

        s-allPrevs₂ : ∀ {y} → y ∈ allPrevs → SingleOrigin⁺ (proj₂ y)
        s-allPrevs₂ {y} y∈ with ∈-++⁻ fromForge y∈

        s-allPrevs₂ {y} y∈ | inj₁ y∈ˡ
          with ◆∈? forge tx | y∈ˡ
        ... | yes _ | here refl = tt
        ... | no  _ | ()

        s-allPrevs₂ {y} y∈ | inj₂ y∈ʳ
          with r@(record {vl′ = vl′; prevOut∈ = prevOut∈; vl′≺vl = vl′≺vl})
             , r∈ , rj ← ∈-mapMaybe⁻ {xs = rs} {f = res→origins} y∈ʳ
          with resValue r ◆ >? 0 | rj
        ... | yes p | refl = go′ (_ , vl′) (a _ vl′≺vl) prevOut∈ p nf′
          where
            nf′ : NonFungible (_ , vl′) nft
            nf′ = NF-weaken {l = _ , vl₀} {l′ = _ , vl′} vl′≺vl nf
        ... | no  _ | ()

        nf′ : count (◆∈?_ ∘ resValue) (prevs vl vtx) + forge tx ◆ ≤ 1
        nf′ = nf-prevs {tx}{l}{vl}{vtx} nf

        s-allPrevs₁ : Singleton allPrevs
        s-allPrevs₁
          with ◆∈? forge tx | allPrevs≢[]
        ... | yes p | _ = fin
          where
            fromForge′ = [ forge tx ◆ , singleOrigins tx vtx ]

            frg≤1 : forge tx ◆ ≤ 1
            frg≤1 = ≤-+ˡ {x = forge tx ◆} {y = ∑ l forge ◆} {z = 1}
                       $ subst (_≤ 1) (+ᶜ-◆ {x = forge tx} {y = ∑ l forge}) nf

            frg≡1 : forge tx ◆ ≡ 1
            frg≡1 = x>0,x≤1⇒x≡1 p frg≤1

            count≡0 : count (◆∈?_ ∘ resValue) rs ≡ 0
            count≡0 = x+y≤y⇒x≡0 {x = count (◆∈?_ ∘ resValue) rs} {y = 1}
                              $ subst (λ x → count (◆∈?_ ∘ resValue) rs + x ≤ 1) frg≡1 nf′

            p₁ : All (¬_ ∘ ◆∈_ ∘ resValue) rs
            p₁ = count≡0⇒All¬ {xs = rs} (◆∈?_ ∘ resValue) count≡0

            p₂ : All Is-nothing (map res→origins rs)
            p₂ = All.map⁺ $ All-map {P = ¬_ ∘ ◆∈_ ∘ resValue} {Q = Is-nothing ∘ res→origins} P⇒Q p₁
              where
                P⇒Q : ∀ r → ¬ ◆∈ (resValue r) → Is-nothing (res→origins r)
                P⇒Q r ◆∉r with ◆∈? resValue r
                ... | yes ◆∈r = ⊥-elim $ ◆∉r ◆∈r
                ... | no  _   = MAll.nothing

            fromPrevs≡[] : Null fromPrevs
            fromPrevs≡[] = All-nothing⇒mapMaybe≡[] p₂

            fin : Singleton $ fromForge′ ++ fromPrevs
            fin rewrite fromPrevs≡[] | ++-identityʳ fromForge′ = tt

        ... | no ¬p | ¬n rewrite ++-identityˡ fromPrevs = s-fromPrevs
          where
            count≤ : count (◆∈?_ ∘ resValue) rs ≤ 1
            count≤ = ≤-+ˡ {y = forge tx ◆} {z = 1} nf′

            r>0⇒just : ∀ r → ◆∈ resValue r → Is-just (res→origins r)
            r>0⇒just r r>0 with ◆∈? resValue r
            ... | yes _   = MAny.just tt
            ... | no ¬r>0 = ⊥-elim $ ¬r>0 r>0

            ams-fromPrevs : AtMostSingleton fromPrevs
            ams-fromPrevs = ams-count {P? = ◆∈?_ ∘ resValue} {xs = rs} {f = res→origins}
                                      r>0⇒just count≤

            s-fromPrevs : Singleton fromPrevs
            s-fromPrevs = am-¬null⇒singleton ams-fromPrevs ¬n

        s-allPrevs : SingleOrigin² allPrevs
        s-allPrevs = s-allPrevs₁ , All.tabulate s-allPrevs₂

        s-allPrevs⁺ : SingleOrigin²⁺ allPrevs⁺
        s-allPrevs⁺ = singleOrigin²⇒singleOrigin²⁺ s-allPrevs

        qed′ : SingleOrigin⁺ qed
        qed′ = singleOrigin-merge {n = v} {p = ∑≥′} s-allPrevs⁺
