open import UTxO.Types
open import StateMachine.Base

module StateMachine.Properties.Ledger
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open CEM {sm = sm}
open import UTxO.Validity
open import StateMachine.Properties {sm = sm}
open import Bisimulation.Completeness {sm = sm}

open import Relation.Binary.PropositionalEquality using (_≡_;trans;cong;subst;refl)
open import Data.Bool using (T)
open import Data.Sum using ([_,_];inj₁;inj₂;_⊎_)
open import Data.Product using (_,_;proj₁;proj₂;Σ;_×_)
open import Data.Maybe using (just)
open import Data.List using (_∷_;[])
-- to the chain!

open import Bisimulation.Base {sm = sm}

-- trivial constraints are trivially satisfied
open import Prelude.Default
open import Data.List.Relation.Unary.All

lemmaSat : ∀ {s l} {vl : ValidLedger l}
  → (p : vl ~ s)
  → Satisfiable {s}{l}{vl} (def Default-TxConstraints) p
lemmaSat p = refl , (refl , (λ tx → []))



-- Invariants hold on chain
lemmaP : ∀{tx l}
  → (P : S → Set)
  → (X : ∀{s s' : S}{i : I} → s —→[ i ]' s' → P s → P s')
  → ∀{vtx : IsValidTx tx l}{vl : ValidLedger l}{vl′}
  → vl —→[ tx ∶- vtx ] vl′
  → ∀ s → vl ~ s
  → P s
  → (Σ S λ s′ → P s′ × (vl′ ~ s′)) ⊎ vl′ ~ s
lemmaP P X p s q v with completeness {s = s} p q
lemmaP P X p s q v | inj₁ (i , s′ , tx≡ , r , r′ , r″) =
  inj₁ (s′ , X (tx≡ , r) v , r′)
lemmaP P X p s q v | inj₂ r = inj₂ r

postulate ~uniq : ∀ l (vl : ValidLedger l) s s' → vl ~ s → vl ~ s' → s ≡ s'

-- a sequence of transactions from one bisimilar ledger and state pair
-- to another, starting in initial state
data X : ∀ {l l'} → ValidLedger l → S → ValidLedger l' → S → Set where
  root : ∀{l}(vl : ValidLedger l) → ∀ s → T (initₛₘ s) → vl ~ s → X vl s vl s
  cons : ∀{l l' s s'}{vl : ValidLedger l}{vl' : ValidLedger l'} → X vl s vl' s' → ∀{tx}{vtx : IsValidTx tx l'}{vl''} → vl' —→[ tx ∶- vtx ] vl'' → ∀ s'' → vl'' ~ s'' →
    X vl s vl'' s''

end~ : ∀{l}{s}{vl : ValidLedger l}{s'}{l'}{vl' : ValidLedger l'} → X vl s vl' s' → vl' ~ s'
end~ (root vl s p q) = q
end~ (cons xs p s'' q) = q

forget : ∀{s s' l l'}{vl : ValidLedger l}{vl' : ValidLedger l'}(xs : X vl s vl' s') → RootedRun s s'
forget (root _ _ p q) = root p
forget {l = l}{l'}{vl}{vl'}(cons {s' = s'} xs p s'' q) = Data.Sum.[ (λ {(i , s''' , tx≡ , q' , q'' , _) → cons rs (tx≡ , trans q' (cong (λ x → just (x , tx≡)) (~uniq l' vl' _ _ q'' q)))}) , (λ q' → subst (RootedRun _) (~uniq l' vl' _ _ q' q) rs) ] (completeness {s'} p (end~ xs)) where rs = forget xs

-- some more properties of a trace:

-- the predicate holds somewhere in the trace

data AnyR (P : S → Set) : ∀{s s'} → RootedRun s s' → Set where
  root   : ∀ {s} → (p : T (initₛₘ s)) → P s → AnyR P (root p)
  here : ∀ {s s' i s''} (p : RootedRun s s')(q : s' —→[ i ]' s'')
    → P s'' → AnyR P (cons p q)
  there : ∀ {s s' i s''} (p : RootedRun s s')(q : s' —→[ i ]' s'')
    → AnyR P p → AnyR P (cons p q)

data AnyX (P : S → Set) : ∀ {l l'}{vl : ValidLedger l}{s}{vl' : ValidLedger l'}{s'} → X vl s vl' s' → Set where
  root : ∀{l}(vl : ValidLedger l) → ∀ s → (i : T (initₛₘ s))(p : vl ~ s) → P s → AnyX P (root vl s i p)
  here : ∀{l l' s s'}{vl : ValidLedger l}{vl' : ValidLedger l'}(xs : X vl s vl' s') → ∀{tx}{vtx : IsValidTx tx l'}{vl''}(p : vl' —→[ tx ∶- vtx ] vl'') → ∀ s'' (q : vl'' ~ s'') → P s'' → AnyX P {s = s}{s' = s''} (cons xs p s'' q)
  there : ∀{l l' s s'}{vl : ValidLedger l}{vl' : ValidLedger l'}(xs : X vl s vl' s') → ∀{tx}{vtx : IsValidTx tx l'}{vl''}(p : vl' —→[ tx ∶- vtx ] vl'') → ∀ s'' (q : vl'' ~ s'') → AnyX P xs → AnyX P {s = s}{s' = s''} (cons xs p s'' q)

any-lem-chain : (P : S → Set)
               → ∀{s s' l l'}{vl : ValidLedger l}{vl' : ValidLedger l'}(xs : X vl s vl' s') → AnyR P (forget xs) → AnyX P xs
any-lem-chain P (root _ _ p q) (root .p q') = root _ _ p q q'
any-lem-chain P (cons {s' = s'} xs {vl'' = vl''} p s'' q) p' with completeness {s'} p (end~ xs)
any-lem-chain P (cons {s' = s'} xs {vl'' = vl''} p _ q) (here .(forget xs) (.(proj₁ (proj₂ (proj₂ x))) , .(trans (proj₁ (proj₂ (proj₂ (proj₂ x)))) (cong (λ x₂ → just (x₂ , proj₁ (proj₂ (proj₂ x)))) (~uniq (_ ∷ _) _ (proj₁ (proj₂ x)) _ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ x))))) q)))) x₁) | inj₁ x = here _ p _ q x₁
any-lem-chain P (cons {s' = s'} xs {vl'' = vl''} p _ q) (there .(forget xs) (.(proj₁ (proj₂ (proj₂ x))) , .(trans (proj₁ (proj₂ (proj₂ (proj₂ x)))) (cong (λ x₁ → just (x₁ , proj₁ (proj₂ (proj₂ x)))) (~uniq (_ ∷ _) _ (proj₁ (proj₂ x)) _ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ x))))) q)))) p') | inj₁ x = there xs p _ q (any-lem-chain P xs p')
... | inj₂ y rewrite ~uniq (_ ∷ _) vl'' s' s'' y q = there xs p _ q (any-lem-chain P xs p')

{-
-- until property
-- P..P..Q..Q..
-- P holds and then Q holds
-- * P has to hold at least at the initial state, it can hold forever and then Q doesn't need to hold
-- * if Q takes over then P does not need to hold anymore. There is no enforced overlap

data UntilR (P Q : CounterState → Set) : ∀{s s'} → RootedRun s s' → Set where
  prefix : ∀{s s'}(xs : RootedRun s s') → AllR P xs → UntilR P Q xs
  suffix : ∀{s s' i s''}(xs : RootedRun s s') → UntilR P Q xs → (x : s' —→[ i ] s'') → Q s'' → UntilR P Q (cons xs x)

data UntilX (P Q : CounterState → Set) : ∀ {l l'}{vl : ValidLedger l}{s}{vl' : ValidLedger l'}{s'} → X vl s vl' s' → Set where
  prefix : ∀ {l l'}{vl : ValidLedger l}{s}{vl' : ValidLedger l'}{s'}(xs : X vl s vl' s') → AllX P xs → UntilX P Q xs
  suffix : ∀ {l l'}{vl : ValidLedger l}{s}{vl' : ValidLedger l'}{s'}(xs : X vl s vl' s') → UntilX P Q xs
    → ∀{tx}{vtx : IsValidTx tx l'}{vl''}(p : vl' —→[ tx ∶- vtx ] vl'') → ∀ s'' (q : vl'' ~ s'') → Q s'' → UntilX P Q (cons xs p s'' q)

{-
identity : (P Q : CounterState → Set) → ∀{s s'}(xs : RootedRun s s') → UntilR P Q xs → UntilR P Q xs
identity P Q xs (prefix .xs x) = {!!}
identity P Q .(cons xs x) (suffix xs p x x₁) = {!!}
-}

subst-UntilR : (P Q : CounterState → Set) → ∀{s s' s''}(xs : RootedRun s s')(xs' : RootedRun s s'')(p : s'' ≡ s') → subst (RootedRun s) p xs' ≡ xs → UntilR P Q xs → UntilR P Q xs'
subst-UntilR P Q xs xs' refl refl p = p

until-lem-chain : (P Q : CounterState → Set)
               → ∀{s s' l l'}{vl : ValidLedger l}{vl' : ValidLedger l'}(xs : X vl s vl' s') → UntilR P Q (forget' xs) → UntilX P Q xs
until-lem-chain P Q xs p with forget' xs | inspect forget' xs
until-lem-chain P Q xs (prefix .(root x) x₁) | root x | remember eq = prefix _ (all-lem-chain' P xs (subst (AllR P) (sym eq) x₁))
until-lem-chain P Q xs (prefix .(cons q x) x₁) | cons q x | remember eq = prefix _ (all-lem-chain' P xs (subst (AllR P) (sym eq) x₁))
until-lem-chain P Q (cons {s' = s'} xs x₂ _ x₃) (suffix .q p .x x₁) | cons q x | remember eq with  completeness {s'} x₂ (end~' xs)
until-lem-chain P Q (cons {s' = s'} xs x₂ _ x₃) (suffix .q p .x x₁) | cons q x | remember refl | inj₁ x₄ = suffix xs (until-lem-chain P Q xs p) x₂ _ x₃ x₁
until-lem-chain P Q (cons {s' = s'} xs x₂ _ x₃) (suffix .q p .x x₁) | cons q x | remember eq | inj₂ y = suffix xs (until-lem-chain P Q xs (subst-UntilR P Q (cons q x) (forget' xs) _ eq (UntilR.suffix _ p x x₁))) x₂ _ x₃ x₁

-}
