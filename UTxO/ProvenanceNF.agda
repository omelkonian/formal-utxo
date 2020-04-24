module UTxO.ProvenanceNF where

open import Function
open import Level
open import Induction.WellFounded

open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Product hiding (map)
open import Data.Bool using (T)
open import Data.Bool.Properties using (T?)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-trans)
open import Data.List
open import Data.List.NonEmpty as NE using (List⁺; _∷_)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Properties
open import Data.List.Relation.Unary.Any hiding (map)
open import Data.List.Relation.Unary.All as All hiding (map; Null; lookup)

open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Unary as Unary using (Pred; _⊆_)
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open Eq.≡-Reasoning

open import Prelude.Lists

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types
open import UTxO.TxUtilities
open import UTxO.Validity
open import UTxO.Provenance

NF-Token : Set
NF-Token = CurrencySymbol × TokenName

mkSingle : NF-Token → Value
mkSingle (c , t) = [ c , [ t , 1 ] ]

NF-Output : TxOutput → NF-Token → Set
NF-Output (record {value = v}) nft
  = (v ≡ mkSingle nft)
  × (∀ v′ → v′ -contributesTo- v → v′ ≡ v)
  -- ^ NB. We do not allow mixing the NF-token with other values

NonFungible : ∃ ValidLedger → NF-Token → Set
NonFungible (l , _) nfv = lookupQuantity nfv (∑ l forge) ≤ 1

postulate
  NF-postulate : ∀ {nft tx l} {vl : ValidLedger l} {vtx : IsValidTx tx l} {o}
    → NF-Output o nft
    → NonFungible (_ , vl ⊕ tx ∶- vtx) nft
    → AtMostSingleton $ filter (_-contributesTo?- value o) (forge tx ∷ map resValue (prevs vl vtx))

NF-weaken : ∀ {nft l l′}
  → l′ ≺′ l
  → NonFungible l nft
  → NonFungible l′ nft
NF-weaken {nft} {l , _} {l′ , _} vl′≺ nf =
  ≤-trans (≥ᶜ-lookupQuantity {v = ∑ l forge} {v′ = ∑ l′ forge} nft $ ≺-∑forge vl′≺)
          nf

nonFungibleProvenance : ∀ l → ∀ {o} (o∈ : o ∈ outputsₘ l) (nft : NF-Token)
  → NF-Output o nft
  → NonFungible l nft
    -------------------------
  → Singleton⁺ (history l o∈)

nonFungibleProvenance l
  = go′ l (≺′-wf l)
  where
    open M₁ l

    go′ : ∀ l → (ac : Acc _≺′_ l)
        → ∀ {o} (o∈ : o ∈ outputsₘ l) nft
        → NF-Output o nft
        → NonFungible l nft
        → Singleton⁺ $ go {o} l ac {o} o∈
    go′ (.tx ∷ l , vl₀@(vl ⊕ tx ∶- vtx)) a₀@(acc a) {o} o∈ nft nfo nf₀
     = qed
     where
      open M₂ {o} tx l vl vtx a {o} o∈

      nf : AtMostSingleton allPrevs
      nf = ams-filter-map {xs = allPrevs₀} {f = proj₁} {P? = _-contributesTo?- v}
         $ subst (AtMostSingleton ∘ filter (_-contributesTo?- v)) proj₁-ap≡ (NF-postulate {o = o} nfo nf₀)

      frg = forge tx
      nfv = mkSingle nft
      P?  = T? ∘ (_≥ᶜ v) ∘ ∑₁
      cv? = (_-contributesTo?- v) ∘ proj₁

      rec′ : ∀ {x} → x ∈ prevHistories → proj₁ x -contributesTo- v → Singleton⁺ (proj₂ x)
      rec′ {hᵥ , h} x∈ hᵥ-contribs
        with record {prevTx = tx′; l′ = l′; prevOut = o′; vl′ = vl′; prevOut∈ = o∈′; vl′≺vl = vl′≺}
           , r∈
           , refl ← ∈-map⁻ res→history x∈
           = s⁺-h
        where
          hᵥ≡ : hᵥ ≡ v
          hᵥ≡ = proj₂ nfo hᵥ hᵥ-contribs

          nfo′ : NF-Output o′ nft
          nfo′ = trans hᵥ≡ (proj₁ nfo) , λ v′ v′-contribs → trans (proj₂ nfo v′ (subst _ hᵥ≡ v′-contribs)) (sym hᵥ≡)

          nf₀′ : NonFungible (_ , vl′) nft
          nf₀′ = NF-weaken {l = _ , vl₀} {l′ = _ , vl′} vl′≺ nf₀

          s⁺-h : Singleton⁺ h
          s⁺-h = go′ (_ , vl′) (a _ vl′≺) {o = o′} o∈′ nft nfo′ nf₀′

      rec : All (Singleton⁺ ∘ proj₂) allPrevs
      rec = all-filter⁺ {P? = (_-contributesTo?- v) ∘ proj₁} {xs = allPrevs₀} (const tt ∷ All.tabulate rec′)

      v>0 : ¬ T ($0 ≥ᶜ v)
      v>0 rewrite proj₁ nfo = λ ()

      s-allPrevs : ∃Singleton² allPrevs
      s-allPrevs
        with frg -contributesTo?- v
      ... | yes p = construct-∃Singleton² ap≡
        where
          nfˡ : AtMostSingleton (forgeHistory ∷ filter cv? prevHistories)
          nfˡ = subst AtMostSingleton (filter-accept cv? p) nf

          filter≡ : filter cv? prevHistories ≡ []
          filter≡ = ams-single nfˡ

          ap≡ : allPrevs ≡ [ forgeHistory ]
          ap≡ = begin allPrevs                                ≡⟨ filter-accept cv? p ⟩
                      forgeHistory ∷ filter cv? prevHistories ≡⟨ cong (forgeHistory ∷_) filter≡ ⟩
                      [ forgeHistory ]                        ∎

      ... | no ¬p = s-ap , s-ap²
        where
          ap⁺ : ¬ Null allPrevs
          ap⁺ ap≡[] = validChoices≢[] validChoices≡[]
            where
              choices≡ : choices ≡ [ [] ]
              choices≡ rewrite ap≡[] = refl

              validChoices≡[] : validChoices ≡ []
              validChoices≡[] = trans (cong (filter P?) choices≡) (filter-reject P? v>0)

          s-ap : Singleton allPrevs
          s-ap = am-¬null⇒singleton nf ap⁺

          s-ap² : Singleton⁺ (proj₂ $ proj₁ $ destruct-Singleton s-ap)
          s-ap² = All.lookup rec (singleton∈ s-ap)

      ap  = destruct-∃Singleton² s-allPrevs
      hᵥ  = proj₁ ap
      h   = proj₁ $ proj₂ ap
      ap≡ = proj₂ $ proj₂ ap
      hs  = [ hᵥ , NE.[ h ] ]

      choices≡ : choices ≡ [] ∷ hs ∷ []
      choices≡ = cong subsequences ap≡

      ∑≥v : T $ ∑₁ hs ≥ᶜ v
      ∑≥v with T? $ ∑₁ hs ≥ᶜ v
      ... | yes p = p
      ... | no ¬p = ⊥-elim $ validChoices≢[] validChoices≡[]
        where
          validChoices≡[] : validChoices ≡ []
          validChoices≡[] = begin validChoices             ≡⟨ cong (filter P?) choices≡ ⟩
                                  filter P? ([] ∷ hs ∷ []) ≡⟨ filter-reject P? v>0 ⟩
                                  filter P? (hs ∷ [])      ≡⟨ filter-reject P? ¬p ⟩
                                  []                       ∎

      validChoices≡ : validChoices ≡ [ hs ]
      validChoices≡ = begin validChoices             ≡⟨ cong (filter P?) choices≡ ⟩
                            filter P? ([] ∷ hs ∷ []) ≡⟨ filter-reject P? v>0 ⟩
                            filter P? (hs ∷ [])      ≡⟨ filter-accept P? ∑≥v ⟩
                            [ hs ]                   ∎

      singleton²-combine : ∀ {v : Value} {hs : Histories} {∑≥v : T $ ∑₁ hs ≥ᶜ v}
        → ∃Singleton² hs
        → Singleton $ combine {v} hs ∑≥v
      singleton²-combine {v = v} {hs = hs} {∑≥v = ∑≥v} hs⁺
        with hᵥ , h , refl ← destruct-∃Singleton² hs⁺
        = singleton-concatMap {A = Trace hᵥ} {B = Trace v} {h = NE.[ h ]}
                              {f = λ tr → [ tr ∷ᵗ emptyTrace refl ]}
                              tt (λ _ → tt)
          where open M₀ {v} hᵥ NE.[ h ] [] ∑≥v

      qed : Singleton⁺ $ toList⁺ traces traces≢[]
      qed = singleton⇒singleton⁺
          $ singleton-concat⁺
          $ singleton²-mapWith∈ (λ {xs} xs∈ → singleton²-combine {v = v} {hs = xs})
          $ construct-Singleton³ validChoices≡
