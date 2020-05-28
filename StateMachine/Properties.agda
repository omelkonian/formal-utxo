open import Level    using (0ℓ)
open import Function using (_∘_; case_of_; _$_)

open import Category.Monad using (RawMonad)

open import Data.Empty   using (⊥-elim)
open import Data.Unit    using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax;Σ)
  renaming (map to map₁₂)
open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_; T)
open import Data.Maybe   using (Maybe; just; nothing; fromMaybe; maybe′)
open import Data.List    using (List; null; []; _∷_; [_]; filter; map; length; and)
open import Data.Nat     using (ℕ)
  renaming (_≟_ to _≟ℕ_)
open import Data.Sum using (_⊎_)

open import Data.Maybe.Properties  using (just-injective)
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List.Membership.Propositional            using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-filter⁻)
open import Data.List.Relation.Unary.Any as Any           using (here)

open import Relation.Nullary                      using (yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; inspect; trans; sym; cong; subst)
  renaming ([_] to ≡[_])

open import Prelude.General
open import Prelude.Lists using (enumerate)

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities
open import UTxO.Validity
open import StateMachine.Base

module StateMachine.Properties
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open CEM {sm = sm}

T-propagates : ∀ {ptx}
  → propagates threadₛₘ ptx ≡ true
    ------------------------------
  → ((valueAtⁱ (thisValidator ptx) (txInfo ptx) ≥ᶜ threadₛₘ) ≡ true)
  × ((valueAtᵒ (thisValidator ptx) (txInfo ptx) ≥ᶜ threadₛₘ) ≡ true)
T-propagates {ptx} eq = map₁₂ T⇒true T⇒true (T-∧ $ true⇒T eq)

T-outputsOK : ∀ {l tx di ds s′} {txIn : TxInput} {txIn∈ : txIn ∈ inputs tx}
  → let ptx = toPendingTx l tx (Any.index txIn∈) in
    outputsOK ptx di ds s′ ≡ true
--  → finalₛₘ s′ ≡ false
    --------------------------------
  → ∃[ o ] ( (o ∈ outputs tx)
           × (getContinuingOutputs ptx ≡ [ mkOutputInfo o ])
           × (datumHash o ≡ toData s′ ♯ᵈ)
           × (value o ≡ valueAtᵒ (thisValidator ptx) (txInfo ptx))
           × (address o ≡ validator txIn ♯)
           )
T-outputsOK {l} {tx} {di} {ds} {s′} {txIn} {txIn∈} eq -- ¬fin
--   with finalₛₘ s′ | ¬fin
-- ... | true  | ()
-- ... | false | _
  with getContinuingOutputs (toPendingTx l tx (Any.index txIn∈))
     | inspect getContinuingOutputs (toPendingTx l tx (Any.index txIn∈))
... | (o ∷ []) | ≡[ out≡ ]
  rewrite ptx-‼ {l = l} {tx = tx} {i∈ = txIn∈}
  with ∈-filter⁻ (((validator txIn) ♯ ≟ℕ_) ∘ OutputInfo.validatorHash)
                  {v = o} {xs = map mkOutputInfo (outputs tx)} (singleton→∈ (_ , out≡))
... | o∈ , refl
  with ∈-map⁻ mkOutputInfo o∈
... | o′ , o′∈ , refl
  with datumHash o′ ≟ℕ toData s′ ♯ᵈ | eq
... | no ¬p    | ()
... | yes refl | _
    = o′ , o′∈ , refl , refl , sym (sum-single {v = value o′}) , refl

T-validator : ∀ {di s ptx} →
  let
    ds   = toData s
    txi  = txInfo ptx
    outs = getContinuingOutputs ptx
  in
    T (validatorₛₘ ptx di ds)
    ----------------------------------
  → ∃[ i ] ∃[ s′ ] ∃[ tx≡ ]
      ( (stepₛₘ s i ≡ pure (s′ , tx≡))
      × (outputsOK ptx di ds s′ ≡ true)
      × (verifyTxInfo txi tx≡ ≡ true)
      × (propagates threadₛₘ ptx ≡ true)
      )
T-validator {di} {s} {ptx} eq
  rewrite from∘to s
  with ⦇ stepₛₘ (pure s) (fromData di) ⦈
      | inspect (λ x → ⦇ stepₛₘ (pure s) x ⦈) (fromData di)
      | eq
... | nothing | _        | ()
... | just r  | ≡[ eq′ ] | _
  with fromData {A = I} di
... | nothing = ⊥-elim (ap-nothing {m = maybe′ (pure ∘ stepₛₘ) nothing (pure s)} eq′)
... | just i
  with stepₛₘ s i | inspect (stepₛₘ s) i | eq
... | nothing         | _          | ()
... | just (s′ , tx≡) | ≡[ step≡ ] | _
  rewrite step≡
  with outputsOK ptx di (toData s) s′ | inspect (outputsOK ptx di (toData s)) s′ | eq
... | false | _            | ()
... | true  | ≡[ outsOK≡ ] | _
  rewrite outsOK≡
  with verifyTxInfo (txInfo ptx) tx≡ | inspect (verifyTxInfo (txInfo ptx)) tx≡ | eq
... | false | _            | ()
... | true  | ≡[ verify≡ ] | _
  rewrite verify≡
  with propagates threadₛₘ ptx | eq
... | false | ()
... | true  | _
    = i , s′ , tx≡ , step≡ , outsOK≡ , verify≡ , refl


-- james

_—→[_]'_ : S → I → S → Set
s —→[ i ]' s′ =
  Σ TxConstraints λ tx≡ → stepₛₘ s i ≡ just (s′ , tx≡)

data RootedRun : S → S → Set where
  root : ∀{s} → T (initₛₘ s) → RootedRun s s
  cons : ∀{s s' i s''} → RootedRun s s' → s' —→[ i ]' s'' → RootedRun s s''

cons-lem : ∀{s s' i s''}{xs}{ xs' : RootedRun s s'}{x x' : s' —→[ i ]' s''} → cons xs x ≡ cons xs' x' → xs ≡ xs' × x ≡ x'
cons-lem refl = refl , refl

-- the predicate P holds for all states in the run
data AllS (P : S → Set) : ∀{s s'} → RootedRun s s' → Set where
  root : ∀ {s} → (p : T (initₛₘ s)) → P s → AllS P (root p)
  cons : ∀ {s s' i s''} (p : RootedRun s s')(q : s' —→[ i ]' s'')
    → P s'' → AllS P p → AllS P (cons p q)

-- the property holds in the end
end : ∀ P {s s'}{p : RootedRun s s'} → AllS P p → P s'
end P (root p q) = q
end P (cons p q r s) = r

all-lem : (P : S → Set)
        → (∀{s} → T (initₛₘ s) → P s)
        → (∀{s i s'} → s —→[ i ]' s' → P s → P s')
        → ∀ {s s'}(p : RootedRun s s') → AllS P p
all-lem P base step (root p) = root p (base p)
all-lem P base step (cons p q) =
  cons p q (step q (end P h)) h
  where h = all-lem P base step p

-- any

data AnyS (P : S → Set) : ∀{s s'} → RootedRun s s' → Set where

  root   : ∀ {s} → (p : T (initₛₘ s)) → P s → AnyS P (root p)

  here : ∀ {s s' i s''} (p : RootedRun s s')(q : s' —→[ i ]' s'')
    → P s'' → AnyS P (cons p q)
  there : ∀ {s s' i s''} (p : RootedRun s s')(q : s' —→[ i ]' s'')
    → AnyS P p → AnyS P (cons p q)
-- TODO: this isn't right, it needs two constructors for root

-- until

-- P+Q*
-- P holds and then Q holds

-- * P has to hold at least at the initial state, it can hold forever
-- and then Q doesn't need to hold at all

-- * if Q takes over then P does not need to hold anymore. There is no
-- enforced overlap

data UntilS (P Q : S → Set) : ∀{s s'} → RootedRun s s' → Set where
  prefix : ∀{s s'}(xs : RootedRun s s') → AllS P xs → UntilS P Q xs
  suffix : ∀{s s' i s''}(xs : RootedRun s s')
    → UntilS P Q xs → (x : s' —→[ i ]' s'') → Q s'' → UntilS P Q (cons xs x)

open import Bisimulation.Base {sm = sm}
-- non-empty rooted runs
data RootedRun' : S → S → Set where
  one : ∀{s s' i txc} → T (initₛₘ s) → s —→[ i ] (s' , txc) → RootedRun' s s
  cons : ∀{s s' i s'' txc} → RootedRun' s s' → s' —→[ i ] (s'' , txc) → RootedRun' s s''

-- properties of inputs (which may refer to the other stuff)
data AllI (P : S → I → TxConstraints → S → Set) : ∀ {s s'} → RootedRun' s s' → Set where
  root : ∀ {s s' i txc} → (p : T (initₛₘ s)) → (q : s —→[ i ] (s' , txc)) → P s i txc s'
    → AllI P {s = s} (one p q)
  cons : ∀ {s s' i s'' txc} (p : RootedRun' s s')(q : s' —→[ i ] (s'' , txc))
    → P s' i txc s'' → AllI P p → AllI P (cons p q)

