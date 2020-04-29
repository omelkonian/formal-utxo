module StateMachine.TeaCoffee where

open import StateMachine.Base
open import UTxO.Types
open import Prelude.Default

open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Product
open import Data.Bool
open import Data.Unit

data State : Set where
  P₁ P₂ P₃ P₄ : _

data Input : Set where
  coin request-tea request-coffee coffee tea : _

instance
  IsData-CS : IsData State
  toData   ⦃ IsData-CS ⦄ P₁ = CONSTR 1 []
  toData   ⦃ IsData-CS ⦄ P₂ = CONSTR 2 []
  toData   ⦃ IsData-CS ⦄ P₃ = CONSTR 3 []
  toData   ⦃ IsData-CS ⦄ P₄ = CONSTR 4 []
  
  fromData ⦃ IsData-CS ⦄ (CONSTR 1 []) = just P₁
  fromData ⦃ IsData-CS ⦄ (CONSTR 2 []) = just P₂
  fromData ⦃ IsData-CS ⦄ (CONSTR 3 []) = just P₃
  fromData ⦃ IsData-CS ⦄ (CONSTR 4 []) = just P₄  
  fromData ⦃ IsData-CS ⦄ _ = nothing
  
  from∘to  ⦃ IsData-CS ⦄ P₁ = refl
  from∘to  ⦃ IsData-CS ⦄ P₂ = refl
  from∘to  ⦃ IsData-CS ⦄ P₃ = refl
  from∘to  ⦃ IsData-CS ⦄ P₄ = refl

  from-inj ⦃ IsData-CS ⦄ (CONSTR 1 []) P₁ p = refl
  from-inj ⦃ IsData-CS ⦄ (CONSTR 2 []) P₂ p = refl
  from-inj ⦃ IsData-CS ⦄ (CONSTR 3 []) P₃ p = refl
  from-inj ⦃ IsData-CS ⦄ (CONSTR 4 []) P₄ p = refl
  from-inj ⦃ IsData-CS ⦄ (CONSTR 0 []) s ()
  from-inj ⦃ IsData-CS ⦄ (CONSTR (suc (suc (suc (suc (suc 0))))) []) s ()
  from-inj ⦃ IsData-CS ⦄ (I i) s ()
  from-inj ⦃ IsData-CS ⦄ (H n) s ()
  from-inj ⦃ IsData-CS ⦄ (LIST xs) s ()
  from-inj ⦃ IsData-CS ⦄ (MAP xs) s ()
  
  IsData-CI : IsData Input
  toData   ⦃ IsData-CI ⦄ coin = CONSTR 0 []
  toData   ⦃ IsData-CI ⦄ request-tea = CONSTR 1 []
  toData   ⦃ IsData-CI ⦄ request-coffee = CONSTR 2 []
  toData   ⦃ IsData-CI ⦄ tea = CONSTR 3 []
  toData   ⦃ IsData-CI ⦄ coffee = CONSTR 4 []
  
  fromData ⦃ IsData-CI ⦄ (CONSTR 0 []) = just coin
  fromData ⦃ IsData-CI ⦄ (CONSTR 1 []) = just request-tea
  fromData ⦃ IsData-CI ⦄ (CONSTR 2 []) = just request-coffee
  fromData ⦃ IsData-CI ⦄ (CONSTR 3 []) = just tea
  fromData ⦃ IsData-CI ⦄ (CONSTR 4 []) = just coffee
  fromData ⦃ IsData-CI ⦄ _ = nothing

  from∘to  ⦃ IsData-CI ⦄ coin = refl
  from∘to  ⦃ IsData-CI ⦄ request-tea = refl
  from∘to  ⦃ IsData-CI ⦄ request-coffee = refl
  from∘to  ⦃ IsData-CI ⦄ tea = refl
  from∘to  ⦃ IsData-CI ⦄ coffee = refl

  from-inj ⦃ IsData-CI ⦄ (CONSTR 0 []) coin p = refl
  from-inj ⦃ IsData-CI ⦄ (CONSTR 1 []) request-tea p = refl
  from-inj ⦃ IsData-CI ⦄ (CONSTR 2 []) request-coffee p = refl
  from-inj ⦃ IsData-CI ⦄ (CONSTR 3 []) tea p = refl
  from-inj ⦃ IsData-CI ⦄ (CONSTR 4 []) coffee p = refl
  from-inj ⦃ IsData-CI ⦄ (CONSTR (suc (suc (suc (suc (suc 0))))) []) s ()
  from-inj ⦃ IsData-CI ⦄ (I i) s ()
  from-inj ⦃ IsData-CI ⦄ (H n) s ()
  from-inj ⦃ IsData-CI ⦄ (LIST xs) s ()
  from-inj ⦃ IsData-CI ⦄ (MAP xs) s ()

SM : StateMachine State Input
isInitial SM s = false -- can you return to the initial state? P₁ would work
isFinal SM s = false
step SM P₁ coin  = just (P₂ , def Default-TxConstraints)
step SM P₁ _ = nothing
step SM P₂ request-tea = just (P₃ , def Default-TxConstraints)
step SM P₂ request-coffee = just (P₄ , def Default-TxConstraints)
step SM P₂ _ = nothing
step SM P₃ tea = just (P₁ , def Default-TxConstraints)
step SM P₃ _ = nothing
step SM P₄ coffee = just (P₁ , def Default-TxConstraints)
step SM P₄ _ = nothing
origin SM = nothing

_—→[_]_ : State → Input → State → Set
s —→[ i ] s′ =
    Σ TxConstraints λ tx≡ → step SM s i ≡ just (s′ , tx≡)

-- all states are valid here

Valid : State → Set
Valid s = ⊤

lemma-step : ∀{s s' : State}{i : Input} → s —→[ i ] s' → Valid s → Valid s'
lemma-step p _ = _

-- completeness already gives us that a step from a state machine
-- state goes to a state machine state

-- a trace of execution

data _—→[_]+_ s : List Input → State → Set where
  one  : ∀{i s'} → s —→[ i ] s' → s —→[ i ∷ [] ]+ s'
  cons : ∀{i s' is s''} → s —→[ i ] s' → s' —→[ is ]+ s'' → s —→[ i ∷ is ]+ s''

-- predicate on the incoming state holding somewhere in a trace

data Any—→S {s} : ∀{is s'} → (P : State → Set) → s —→[ is ]+ s' → Set where
  here : ∀{i s' P} → P s → (p : s —→[ i ] s') → Any—→S P (one p)
  there : ∀{i s' is s'' P}(p : s —→[ i ] s')(ps : s' —→[ is ]+ s'')
    → Any—→S P ps
    → Any—→S P (cons p ps)

data Any—→I {s} : ∀{is s'} → (P : Input → Set) → s —→[ is ]+ s' → Set where
  here : ∀{i s' P} → P i → (p : s —→[ i ] s') → Any—→I P (one p)
  there : ∀{i s' is s'' P}(p : s —→[ i ] s')(ps : s' —→[ is ]+ s'')
    → Any—→I P ps
    → Any—→I P (cons p ps)


-- predicate on the input holding somewhere in a trace

open import Relation.Nullary


data All—→I {s} : ∀{is s'} → (P : Input → Set) → s —→[ is ]+ s' → Set where
  one : ∀{i s' P} → P i → (p : s —→[ i ] s') → All—→I P (one p)
  cons : ∀{i s' is s'' P} → P i → (p : s —→[ i ] s')(ps : s' —→[ is ]+ s'')
    → All—→I P ps → All—→I P (cons p ps)

-- sequence of predicates on the input ...P...Q...R... holding
-- sequentially in a trace


data Any—→Is {s} : ∀{is s'} → (Ps : List (Input → Set)) → s —→[ is ]+ s' → Set
  where
  here-cons : ∀{i s' is s'' P Ps}(p : P i)(q : s —→[ i ] s')(qs : s' —→[ is ]+ s'')
    → Any—→Is Ps qs → Any—→Is (P ∷ Ps) (cons q qs)
  nothere : ∀{i s' is s'' P Ps}(notp : ¬ (P i))(q : s —→[ i ] s')(qs : s' —→[ is ]+ s'')
    → Any—→Is (P ∷ Ps) qs → Any—→Is (P ∷ Ps) (cons q qs)
  here-one : ∀{i s' P}(p : P i)(q : s —→[ i ] s') → Any—→Is (P ∷ []) (one q)
  end-one : ∀{i s'}(q : s —→[ i ] s') → Any—→Is [] (one q)
  end-cons : ∀{i s' is s''}(q : s —→[ i ] s')(qs : s' —→[ is ]+ s'') → Any—→Is [] (cons q qs)

open import Data.Empty

lemma-simple : P₁ —→[ coin ∷ request-coffee ∷ [] ]+ P₄ → P₄ —→[ coffee ] P₁
lemma-simple _ = _ , refl

lemma : ∀{s is}(ps : P₁ —→[ is ]+ s)
  -- if you paid and chose coffee
  → Any—→Is ((_≡ coin) ∷ (_≡ request-coffee) ∷ []) ps
  -- and you haven't chosen tea
  → All—→I (λ i → ¬ (i ≡ request-tea)) ps
  -- and you haven't had it already
  → All—→I (λ i → ¬ (i ≡ coffee)) ps
  -- you can have a coffee
  → s —→[ coffee ] P₁

lemma (cons {coin} {P₂} x (one {request-tea} x₁)) p (cons x₂ .x .(one x₁) (one x₃ .x₁)) r = ⊥-elim (x₃ refl)
lemma {P₄} (cons {coin} {P₂} x (one {request-coffee} x₁)) p q r = _ , refl
lemma (cons {coin} {P₂} x (cons {request-tea} x₁ ps)) p (cons x₂ .x .(cons x₁ ps) (cons x₃ .x₁ .ps q)) r = ⊥-elim (x₃ refl)
lemma (cons {coin} {P₂} x (cons {request-coffee} {P₄} x₁ (one {coffee} x₂))) p q (cons x₃ .x .(cons x₁ (one x₂)) (cons x₄ .x₁ .(one x₂) (one x₅ .x₂))) = ⊥-elim (x₅ refl)
lemma (cons {coin} {P₂} x (cons {request-coffee} {P₄} x₁ (cons {coffee} x₂ ps))) p q (cons x₃ .x .(cons x₁ (cons x₂ ps)) (cons x₄ .x₁ .(cons x₂ ps) (cons x₅ .x₂ .ps r))) = ⊥-elim (x₅ refl)
