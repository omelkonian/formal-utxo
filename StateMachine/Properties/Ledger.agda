open import Data.Sum using ([_,_])

open import Prelude.Init
open import Prelude.Default

open import UTxO.Types
open import UTxO.Validity
open import StateMachine.Base

module StateMachine.Properties.Ledger
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open CEM {sm = sm}
open import StateMachine.Properties {sm = sm}
open import StateMachine.Inductive {sm = sm}
open import Bisimulation.Completeness {sm = sm}
open import Bisimulation.Base {sm = sm}


-- to the chain!
-- trivial constraints are trivially satisfied

lemmaSat : ∀ {s l} {vl : ValidLedger l}
  → (p : vl ~ s)
  → Satisfiable {s}{l}{vl} (def Default-TxConstraints) p
lemmaSat p = refl , (refl , (λ tx → []))



-- Invariants hold on chain
lemmaP : ∀{tx l}
  → (P : S → Set)
  → (X : ∀{s s' : S} → s ↝ s' → P s → P s')
  → ∀{vtx : IsValidTx tx l}{vl : ValidLedger l}{vl′}
  → vl —→[ tx ∶- vtx ] vl′
  → ∀ s → vl ~ s
  → P s
  → (Σ S λ s′ → P s′ × (vl′ ~ s′)) ⊎ vl′ ~ s
lemmaP P X p s q v with completeness {s = s} p q
lemmaP P X p s q v | inj₁ (i , s′ , tx≡ , r , r′ , r″) =
  inj₁ (s′ , X (i , tx≡ , r) v , r′)
lemmaP P X p s q v | inj₂ r = inj₂ r

postulate ~uniq : ∀ l (vl : ValidLedger l) s s' → vl ~ s → vl ~ s' → s ≡ s'

-- a sequence of transactions from one bisimilar ledger and state pair
-- to another, starting in initial state
data X : ∀ {l l'} → ValidLedger l → S → ValidLedger l' → S → Set where
  root : ∀{l}(vl : ValidLedger l) → ∀ s → Init s → vl ~ s → X vl s vl s
  snoc : ∀{l l' s s'}{vl : ValidLedger l}{vl' : ValidLedger l'} → X vl s vl' s' → ∀{tx}{vtx : IsValidTx tx l'}{vl''} → vl' —→[ tx ∶- vtx ] vl'' → ∀ s'' → vl'' ~ s'' →
    X vl s vl'' s''

end~ : ∀{l}{s}{vl : ValidLedger l}{s'}{l'}{vl' : ValidLedger l'} → X vl s vl' s' → vl' ~ s'
end~ (root vl s p q) = q
end~ (snoc xs p s'' q) = q

forget : ∀{s s' l l'}{vl : ValidLedger l}{vl' : ValidLedger l'}(xs : X vl s vl' s') → s ↝⋆ s'
forget (root _ _ p q) = root p
forget {l = l}{l'}{vl}{vl'}(snoc {s' = s'} xs p s'' q) = Data.Sum.[ (λ {(i , s''' , tx≡ , q' , q'' , _) → snoc rs (i , tx≡ , trans q' (cong (λ x → just (x , tx≡)) (~uniq l' vl' _ _ q'' q)))}) , (λ q' → subst (_ ↝⋆_) (~uniq l' vl' _ _ q' q) rs) ] (completeness {s'} p (end~ xs)) where rs = forget xs
