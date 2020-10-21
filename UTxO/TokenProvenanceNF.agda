open import Data.Nat.Properties
open import Data.List.Properties
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)

open import Prelude.Init
open import Prelude.General
open import Prelude.Lists
open import Prelude.ToN

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities
open import UTxO.Validity
open import UTxO.GlobalPreservation


module UTxO.TokenProvenanceNF (nft : TokenClass) where

open FocusTokenClass nft
open import UTxO.TokenProvenance nft

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
    frg≥utxo = ≥ᶜ-refl′ $ globalPreservation {l} {vl}

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

private
  variable
    L  : ∃ ValidLedger
    tx : Tx
    n  : Quantity

Singletonᵖ : Provenance L tx n → Set
Singletonᵖ = Singleton ∘ traces

Singletonᵖ² : List (∃ $ Provenance L tx) → Set
Singletonᵖ² xs = Singleton xs × All (Singletonᵖ ∘ proj₂) xs

singleton-combine : ∀ {xs : List (∃ $ Provenance L tx)} {∑≥ : ∑₁ xs ≥ n}
  → Singletonᵖ² xs
  → Singletonᵖ (combine xs ∑≥)
singleton-combine {xs = []}            (() , _)
singleton-combine {xs = (n , pr) ∷ []} (tt , s-pr ∷ [])
  rewrite ++-identityʳ (traces pr)
        = s-pr
singleton-combine {xs = _ ∷ _ ∷ _}     (() , _)

provenanceNF : ∀ {tx l} (vl : ValidLedger (tx ∷ l)) {o} (o∈ : o ∈ outputs tx)
  → (◆∈v : ◆∈ value o)
  → NonFungible (_ , vl) nft
  → ∣ provenance vl o∈ ∣ ≡ 1
provenanceNF vl = go′ vl (≺′-wf (_ , vl))
  where
    open Provenance₀ vl

    go′ : ∀ {tx l} (vl : ValidLedger (tx ∷ l)) (ac : Acc _≺′_ (_ , vl)) {o} (o∈ : o ∈ outputs tx)
        → (◆∈v : ◆∈ value o)
        → NonFungible (_ , vl) nft
        → ∣ go {o} vl ac {o} o∈ ∣ ≡ 1
    go′ {l = l} vl₀@(vl ⊕ tx ∶- vtx) (acc a) {o} o∈ ◆∈v nf
      = comb≡
      where
        open Provenance₁ {o} vl vtx a {o} o∈

        s-allPrevs₂ : ∀ {pr} → pr ∈ allPrevs → Singletonᵖ (proj₂ pr)
        s-allPrevs₂ {pr} pr∈ with ∈-++⁻ fromForge pr∈

        s-allPrevs₂ {pr} pr∈ | inj₁ pr∈ˡ
          with ◆∈? forge tx | pr∈ˡ
        ... | no  _ | ()
        ... | yes _ | here refl = tt

        s-allPrevs₂ {pr} pr∈ | inj₂ pr∈ʳ
          with r@(record {prevTx = tx′; vl′ = vl′; prevOut = o′; prevOut∈ = o∈′; vl′≺vl = vl′≺vl})
             , r∈ , rj ← ∈-mapMaybe⁻ res→traces {xs = rs} pr∈ʳ
          with ◆∈? resValue r | rj
        ... | no  _ | ()
        ... | yes p | refl = singleton-map $ singleton-map len≡1
          where
            nf′ : NonFungible (_ , vl′) nft
            nf′ = NF-weaken {l = _ , vl₀}{_ , vl′} vl′≺vl nf

            pr′ : Provenance (_ , vl′) tx′ (resValue r ◆)
            pr′ = go {o′} vl′ (a _ vl′≺vl) o∈′

            len≡1 : Singletonᵖ pr′
            len≡1 = len≡⇒Singleton {xs = traces pr′} $ go′ vl′ (a _ vl′≺vl) o∈′ p nf′

        nf′ : count (◆∈?_ ∘ resValue) (prevs vl vtx) + forge tx ◆ ≤ 1
        nf′ = nf-prevs {tx}{l}{vl}{vtx} nf

        allPrevs≢[] : ¬Null allPrevs
        allPrevs≢[] ap≡ = ≡0⇒◆∉ {v = value o} (x≤0⇒x≡0 v≤0) ◆∈v
          where
            v≤0 : 0 ≥ v
            v≤0 = subst (λ x → ∑₁ x ≥ v) ap≡ ∑≥

        s-allPrevs₁ : Singleton allPrevs
        s-allPrevs₁
          with ◆∈? forge tx | allPrevs≢[]
        ... | yes p | _ = fin
          where
            fromForge′ = [ _ , singleton-Provenance {tx = tx}{l}{vl₀} ]

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

            p₂ : All Is-nothing (map res→traces rs)
            p₂ = L.All.map⁺ $ All-map {P = ¬_ ∘ ◆∈_ ∘ resValue} {Q = Is-nothing ∘ res→traces} P⇒Q p₁
              where
                P⇒Q : ∀ r → ¬ ◆∈ (resValue r) → Is-nothing (res→traces r)
                P⇒Q r ◆∉r with ◆∈? resValue r
                ... | yes ◆∈r = ⊥-elim $ ◆∉r ◆∈r
                ... | no  _   = M.All.nothing

            fromPrevs≡[] : Null fromPrevs
            fromPrevs≡[] = All-nothing⇒mapMaybe≡[] p₂

            fin : Singleton $ fromForge′ ++ fromPrevs
            fin rewrite fromPrevs≡[] | ++-identityʳ fromForge′ = tt

        ... | no ¬p | ¬n rewrite ++-identityˡ fromPrevs = s-fromPrevs
          where
            count≤ : count (◆∈?_ ∘ resValue) rs ≤ 1
            count≤ = ≤-+ˡ {y = forge tx ◆} {z = 1} nf′

            r>0⇒just : ∀ r → ◆∈ resValue r → Is-just (res→traces r)
            r>0⇒just r r>0 with ◆∈? resValue r
            ... | yes _   = M.Any.just tt
            ... | no ¬r>0 = ⊥-elim $ ¬r>0 r>0

            ams-fromPrevs : AtMostSingleton fromPrevs
            ams-fromPrevs = ams-count {P? = ◆∈?_ ∘ resValue} {xs = rs} {f = res→traces}
                                      r>0⇒just count≤

            s-fromPrevs : Singleton fromPrevs
            s-fromPrevs = am-¬null⇒singleton ams-fromPrevs ¬n

        s-allPrevs : Singletonᵖ² allPrevs
        s-allPrevs = s-allPrevs₁ , L.All.tabulate s-allPrevs₂

        s-comb : Singletonᵖ (combine allPrevs ∑≥)
        s-comb = singleton-combine s-allPrevs

        comb≡ : ∣ combine allPrevs ∑≥ ∣ ≡ 1
        comb≡ = Singleton⇒len≡ {xs = traces $ combine allPrevs ∑≥} s-comb
