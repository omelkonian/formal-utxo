open import Data.List hiding (map)
open import Data.Nat
open import UTxO.Hashing.Base

module StateMachine.MultiSig (Signatories : List HashId)(Threshold : ℕ)
  where

open import Data.Empty
open import Data.Integer using (+_)
open import Data.List.Membership.DecPropositional _≟_
open import Data.Maybe
open import Data.Maybe.Properties
open import Data.Product hiding (map)
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Prelude.Default
open import UTxO.Value
open import UTxO.Types
open import StateMachine.Base

-- not sure if this is a suitable hash definition
PubKeyHash = HashId

record Payment : Set where
  constructor payment
  field
    paymentAmount    : Value
    paymentRecipient : PubKeyHash
    paymentDeadline  : Bound

data State : Set where
  Holding              :                             _
  Collecting : Payment → List PubKeyHash → _

data Input : Set where
  ProposePayment : Payment    → Input
  AddSignature   : PubKeyHash → Input
  Cancel         :              Input
  Pay            :              Input

map-just' : {A B : Set}(ma : Maybe A)(a : A)
  → (f : A → B)
  → (∀{a a'} → f a ≡ f a' → a ≡ a')
  → map f ma ≡ just (f a)
  → ma ≡ just a
map-just' (just _) a f p q = cong just (p (just-injective q))

map-nothing' : {A B : Set}(ma : Maybe A)
  → (f : A → B)
  → map f ma ≡ nothing
  → ma ≡ nothing
map-nothing' nothing f p = refl

ap-map-just : {A B C : Set}(ma : Maybe A)(a : A)(mb : Maybe B)(b : B)
  → (f : A → B → C)
  → (∀{a a'}{b b'} → f a b ≡ f a' b' → a ≡ a' × b ≡ b')
  → Data.Maybe.ap (map f ma) mb ≡ just (f a b)
  → ma ≡ just a × mb ≡ just b
ap-map-just (just _) a (just _) b f p q =
 let
   r , r' = p (just-injective q)
 in
  cong just r , cong just r'

ap-ap-map-just : {A B C D : Set}
  → (ma : Maybe A)(a : A)
  → (mb : Maybe B)(b : B)
  → (mc : Maybe C)(c : C)
  → (f : A → B → C → D)
  → (∀{a a'}{b b'}{c c'} → f a b c ≡ f a' b' c' → a ≡ a' × b ≡ b' × c ≡ c')
  → Data.Maybe.ap (Data.Maybe.ap (map f ma) mb) mc ≡ just (f a b c)
  → ma ≡ just a × mb ≡ just b × mc ≡ just c
ap-ap-map-just (just _) a (just _) b (just _) c f p q =
 let
   r , r' , r'' = p (just-injective q)
 in
  cong just r , cong just r' , cong just r''

,-injective : {A B : Set}{a a' : A}{b b' : B}
  → (a , b) ≡ (a' , b') → a ≡ a' × b ≡ b'
,-injective refl = refl , refl

t=-injective : ∀{n n'} → t= n ≡ t= n' → n ≡ n'
t=-injective refl = refl

payment-injective : ∀{v v' r r' d d'}
  → payment v r d ≡ payment v' r' d' → v ≡ v' × r ≡ r' × d ≡ d'
payment-injective refl = refl , refl , refl

Collecting-injective : ∀{p p' sigs sigs'}
  → Collecting p sigs ≡ Collecting p' sigs'
  → p ≡ p' × sigs ≡ sigs'
Collecting-injective refl = refl , refl

ProposePayment-injective : ∀{p p'}
  → ProposePayment p ≡ ProposePayment p' → p ≡ p'
ProposePayment-injective refl = refl

AddSignature-injective : ∀{sig sig'}
  → AddSignature sig ≡ AddSignature sig' → sig ≡ sig'
AddSignature-injective refl = refl

cong₃ : {A B C D : Set}(f : A → B → C → D){a a' : A}{b b' : B}{c c' : C}
  → a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

-- not making any attempt to do anything special for values
instance
  isData-ℕ : IsData ℕ
  toData ⦃ isData-ℕ ⦄ n = I (+ n)
  fromData ⦃ isData-ℕ ⦄ (I (+ n)) = just n
  fromData ⦃ isData-ℕ ⦄ _ = nothing
  from∘to ⦃ isData-ℕ ⦄ n = refl
  from-inj ⦃ isData-ℕ ⦄ (I (+ _)) _ refl = refl

instance
  isData-Bound : IsData Bound
  toData ⦃ isData-Bound ⦄ -∞      =  CONSTR 0 []
  toData ⦃ isData-Bound ⦄ (t= n)  =  CONSTR 1 [ toData n ]
  toData ⦃ isData-Bound ⦄ +∞      =  CONSTR 2 []
  fromData ⦃ isData-Bound ⦄ (CONSTR 0 [])        = just -∞
  fromData ⦃ isData-Bound ⦄ (CONSTR 1 (dt ∷ [])) =
    map t=_ (fromData dt)
  fromData ⦃ isData-Bound ⦄ (CONSTR 2 [])        = just +∞
  fromData ⦃ isData-Bound ⦄ _                    = nothing
  from∘to ⦃ isData-Bound ⦄ -∞     = refl
  from∘to ⦃ isData-Bound ⦄ (t= t) = refl
  from∘to ⦃ isData-Bound ⦄ +∞     = refl
  from-inj ⦃ isData-Bound ⦄ (CONSTR 0 [])        -∞ refl = refl
  from-inj ⦃ isData-Bound ⦄ (CONSTR 0 (_ ∷ _))   b ()
  from-inj ⦃ isData-Bound ⦄ (CONSTR 1 (dt ∷ [])) (t= t) p =
    cong (λ dt → CONSTR 1 [ dt ]) (from-inj dt t (map-just' (fromData dt) t  t=_ t=-injective p))
  from-inj ⦃ isData-Bound ⦄ (CONSTR 1 (dt ∷ [])) +∞ p with fromData {ℕ} dt
  from-inj ⦃ isData-Bound ⦄ _ _ () | nothing
  from-inj ⦃ isData-Bound ⦄ _ _ () | just x
  from-inj ⦃ isData-Bound ⦄ (CONSTR 1 (dt ∷ [])) -∞ p with fromData {ℕ} dt
  from-inj ⦃ isData-Bound ⦄ _ _ () | nothing
  from-inj ⦃ isData-Bound ⦄ _ _ () | just x
  from-inj ⦃ isData-Bound ⦄ (CONSTR 1 [])   b ()
  from-inj ⦃ isData-Bound ⦄ (CONSTR 2 [])        +∞ refl = refl
  from-inj ⦃ isData-Bound ⦄ (CONSTR 2 (_ ∷ _))   b ()
  from-inj ⦃ isData-Bound ⦄ (CONSTR (suc (suc (suc n))) xs) b ()

instance
  IsData-Pair : ∀ {A B : Set} → {{_ : IsData A}} → {{_ : IsData B}}
    → IsData (A × B)
  toData ⦃ IsData-Pair ⦄ (a , b) = LIST (toData a ∷ toData b ∷ [])
  fromData ⦃ IsData-Pair ⦄ (LIST (a ∷ b ∷ [])) =
    ap (map _,_ (fromData a)) (fromData b)
  fromData ⦃ IsData-Pair ⦄ _ = nothing
  from∘to ⦃ IsData-Pair ⦄ (a , b) rewrite from∘to a | from∘to b = refl
  from-inj ⦃ IsData-Pair ⦄ (LIST (da ∷ db ∷ [])) (a , b) p =
    let
      q , q' = ap-map-just (fromData da) a (fromData db) b _,_ ,-injective p
    in
      cong₂ (λ a b → LIST (a ∷ b ∷ [])) (from-inj da a q) (from-inj db b q')

instance
  IsData-Payment : IsData Payment
  toData   ⦃ IsData-Payment ⦄ (payment v r d) =
    LIST (toData v ∷ toData r ∷ toData d ∷ [])
  fromData ⦃ IsData-Payment ⦄ (LIST (dv ∷ dr ∷ dd ∷ [])) =
    ap (ap (map payment (fromData dv)) (fromData dr)) (fromData dd)
  fromData ⦃ IsData-Payment ⦄ _ = nothing
  from∘to ⦃ IsData-Payment ⦄ (payment v r d) rewrite from∘to v | from∘to r | from∘to d = refl
  from-inj ⦃ IsData-Payment ⦄ (LIST (dv ∷ dr ∷ dd ∷ [])) (payment v r d) p =
    let
      q , q' , q'' = ap-ap-map-just (fromData dv) v (fromData dr) r (fromData dd) d payment payment-injective p
    in
      cong₃ (λ v r d → LIST (v ∷ r ∷ d ∷ [])) (from-inj dv v q) (from-inj dr r q') (from-inj dd d q'')
instance
  IsData-MS : IsData State

  toData ⦃ IsData-MS ⦄ Holding = CONSTR 0 []
  toData ⦃ IsData-MS ⦄ (Collecting p sigs) = CONSTR 1
    (toData p ∷ toData sigs ∷ [])
  fromData ⦃ IsData-MS ⦄ (CONSTR 0 []) = just Holding
  fromData ⦃ IsData-MS ⦄ (CONSTR 1 (p ∷ sigs ∷ [])) =
    ap (map Collecting (fromData p)) (fromData sigs)
  fromData ⦃ IsData-MS ⦄ _ = nothing
  from∘to ⦃ IsData-MS ⦄ Holding = refl
  from∘to ⦃ IsData-MS ⦄ (Collecting p sigs)
    rewrite from∘to p | from∘to sigs = refl

  from-inj ⦃ IsData-MS ⦄ (CONSTR 0 []) Holding p = refl
  from-inj ⦃ IsData-MS ⦄ (CONSTR 1 (dp ∷ dsigs ∷ [])) (Collecting p sigs) q =
    let
      x , x' = ap-map-just (fromData dp) p (fromData dsigs) sigs Collecting Collecting-injective q
    in
      cong₂ (λ p sigs → CONSTR 1 (p ∷ sigs ∷ [])) (from-inj dp p x) (from-inj dsigs sigs x')

  from-inj ⦃ IsData-MS ⦄ (CONSTR (suc (suc n)) (_ ∷ _)) Holding ()
  from-inj ⦃ IsData-MS ⦄ (CONSTR 1 (dp ∷ dsigs ∷ [])) Holding q with (fromData {Payment} dp)
  from-inj IsData-MS _ _ () | nothing
  ... | just x with fromData {List ℕ} dsigs
  from-inj IsData-MS _ _ () | just _ | just _
  from-inj IsData-MS _ _ () | just _ | nothing

  from-inj ⦃ IsData-MS ⦄ (CONSTR 0 (_ ∷ _)) Holding ()
  from-inj ⦃ IsData-MS ⦄ (CONSTR 1 []) Holding ()
  from-inj ⦃ IsData-MS ⦄ (CONSTR 1 (_ ∷ [])) Holding ()
  from-inj ⦃ IsData-MS ⦄ (CONSTR (suc (suc n)) []) Holding ()

  from-inj ⦃ IsData-MS ⦄ (CONSTR 0 []) (Collecting _ _) ()
  from-inj ⦃ IsData-MS ⦄ (CONSTR 0 (_ ∷ _)) (Collecting _ _) ()
  from-inj ⦃ IsData-MS ⦄ (CONSTR 1 []) (Collecting _ _) ()
  from-inj ⦃ IsData-MS ⦄ (CONSTR 1 (_ ∷ [])) (Collecting _ _) ()
  from-inj ⦃ IsData-MS ⦄ (CONSTR (suc (suc n)) _) _ ()

  IsData-MI : IsData Input
  toData ⦃ IsData-MI ⦄ (ProposePayment p) = CONSTR 0 [ toData p ]
  toData ⦃ IsData-MI ⦄ (AddSignature sig) = CONSTR 1 [ toData sig ]
  toData ⦃ IsData-MI ⦄ Pay = CONSTR 2 []
  toData ⦃ IsData-MI ⦄ Cancel = CONSTR 3 []
  fromData ⦃ IsData-MI ⦄ (CONSTR 0 (dp ∷ [])) = map ProposePayment (fromData dp)
  fromData ⦃ IsData-MI ⦄ (CONSTR 1 (dsig ∷ [])) = map AddSignature (fromData dsig)
  fromData ⦃ IsData-MI ⦄ (CONSTR 2 []) = just Pay
  fromData ⦃ IsData-MI ⦄ (CONSTR 3 []) = just Cancel
  fromData ⦃ IsData-MI ⦄ _ = nothing
  from∘to ⦃ IsData-MI ⦄ (ProposePayment p) rewrite from∘to p = refl
  from∘to ⦃ IsData-MI ⦄ (AddSignature sig) rewrite from∘to sig = refl
  from∘to ⦃ IsData-MI ⦄ Pay = refl
  from∘to ⦃ IsData-MI ⦄ Cancel = refl
  from-inj ⦃ IsData-MI ⦄ (CONSTR 0 (dp ∷ [])) (ProposePayment p) q =
    let
      r = (map-just' (fromData dp) p ProposePayment ProposePayment-injective q)
    in
      cong (λ p → CONSTR 0 [ p ]) (from-inj dp p r)
  from-inj ⦃ IsData-MI ⦄ (CONSTR 1 []) (ProposePayment p) ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 1 (dp ∷ [])) (ProposePayment p) q with fromData {ℕ} dp
  from-inj ⦃ IsData-MI ⦄ _ _ () | just _
  from-inj ⦃ IsData-MI ⦄ _ _ () | nothing
  from-inj ⦃ IsData-MI ⦄ (CONSTR 1 (_ ∷ _ ∷ _)) (ProposePayment p) ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 2 []) (ProposePayment p) ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 2 (_ ∷ _)) (ProposePayment p) ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 3 []) (ProposePayment p) ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 3 (_ ∷ _)) (ProposePayment p) ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR (suc (suc (suc (suc _)))) _) (ProposePayment p) ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 1 (dsig ∷ [])) (AddSignature sig) q =
    let
      r = (map-just' (fromData dsig) sig AddSignature AddSignature-injective q)
    in
      cong (λ sig → CONSTR 1 [ sig ]) (from-inj dsig sig r)
  from-inj ⦃ IsData-MI ⦄ (CONSTR 0 []) (AddSignature sig) ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 0 (dp ∷ [])) (AddSignature sig) q with fromData {Payment} dp
  from-inj ⦃ IsData-MI ⦄ _ _ () | just _
  from-inj ⦃ IsData-MI ⦄ _ _ () | nothing
  from-inj ⦃ IsData-MI ⦄ (CONSTR 0 (_ ∷ _ ∷ _)) (AddSignature sig) ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 2 []) (AddSignature sig) ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 2 (_ ∷ _)) (AddSignature sig) ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 3 []) (AddSignature sig) ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 3 (_ ∷ _)) (AddSignature sig) ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR (suc (suc (suc (suc _)))) _) (AddSignature sig) ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 2 []) Pay q = refl
  from-inj ⦃ IsData-MI ⦄ (CONSTR 2 (_ ∷ _)) Pay ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 0 []) Pay ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 0 (dp ∷ [])) Pay q with fromData {Payment} dp
  from-inj ⦃ IsData-MI ⦄ _ _ () | just _
  from-inj ⦃ IsData-MI ⦄ _ _ () | nothing
  from-inj ⦃ IsData-MI ⦄ (CONSTR 0 (_ ∷ _ ∷ _)) Pay ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 1 []) Pay ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 1 (dsig ∷ [])) Pay q with fromData {ℕ} dsig
  from-inj ⦃ IsData-MI ⦄ _ _ () | just _
  from-inj ⦃ IsData-MI ⦄ _ _ () | nothing
  from-inj ⦃ IsData-MI ⦄ (CONSTR 1 (_ ∷ _ ∷ _)) Pay ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 3 []) Pay ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 3 (_ ∷ _)) Pay ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR (suc (suc (suc (suc _)))) _) Pay ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 3 []) Cancel q = refl
  from-inj ⦃ IsData-MI ⦄ (CONSTR 3 (_ ∷ _)) Cancel ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 0 []) Cancel ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 0 (dp ∷ [])) Cancel q with fromData {Payment} dp
  from-inj ⦃ IsData-MI ⦄ _ _ () | just _
  from-inj ⦃ IsData-MI ⦄ _ _ () | nothing
  from-inj ⦃ IsData-MI ⦄ (CONSTR 0 (_ ∷ _ ∷ _)) Cancel ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 1 []) Cancel ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 1 (dsig ∷ [])) Cancel q with fromData {ℕ} dsig
  from-inj ⦃ IsData-MI ⦄ _ _ () | just _
  from-inj ⦃ IsData-MI ⦄ _ _ () | nothing
  from-inj ⦃ IsData-MI ⦄ (CONSTR 1 (_ ∷ _ ∷ _)) Cancel ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 2 []) Cancel ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR 2 (_ ∷ _)) Cancel ()
  from-inj ⦃ IsData-MI ⦄ (CONSTR (suc (suc (suc (suc _)))) _) Cancel ()

MultiSigSM : StateMachine State Input
isInitial MultiSigSM Holding =  true
isInitial MultiSigSM _ = false
step MultiSigSM Holding (ProposePayment p) = just ((Collecting p []) , def)
step MultiSigSM (Collecting p sigs) (AddSignature sig) with sig ∈? Signatories | sig ∈? sigs
... | no ¬q  | _     = nothing -- not a signatory
... | yes q  | no ¬r =
  just (Collecting p (sig ∷ sigs) , def)
  -- TODO: need to add a new type of constraint to check signature
... | yes q  | yes r = nothing -- already signed
step MultiSigSM (Collecting p sigs) Cancel =
  just ( Holding
       , record { forge≡ = nothing
                ; range≡ = just (Payment.paymentDeadline p ⋯ +∞)
                           -- must be after payment deadline
                ; spent≥ = nothing })
step MultiSigSM (Collecting p sigs) Pay with length sigs ≥? Threshold
... | yes q =
  just (Holding
       , record { forge≡ = nothing
                ; range≡ = just (-∞ ⋯ Payment.paymentDeadline p)
                         -- must be before deadline
                ; spent≥ = just (Payment.paymentAmount p) })
                  -- TODO: need to add a new/modify constraint to
                  -- specify recipient
... | no ¬q = nothing
step MultiSigSM _ _ = nothing

origin MultiSigSM = nothing

open import Bisimulation.Base {sm = MultiSigSM}
open import StateMachine.Properties {sm = MultiSigSM}
open import Data.Unit

-- cancel is easy as there is no with
P : State → Input → TxConstraints → State → Set
P (Collecting p _) Cancel txc _ = range≡ txc ≡ just (Payment.paymentDeadline p ⋯ +∞)
P _ Cancel txc _ = ⊥
P _ _ _ _ = ⊤

lemma : ∀ {s s'} (xs : RootedRun' s s') → AllI P xs
lemma (root {s = Holding}{i = ProposePayment pay} p x) = root p x _
lemma (snoc {s' = Holding} {i = ProposePayment _} xs x) = snoc xs x _ (lemma xs)
lemma (snoc {s' = Collecting pay sigs} {i = AddSignature sig} xs x) = snoc xs x _ (lemma xs)
lemma (snoc {s' = Collecting pay sigs} {i = Cancel} xs refl) = snoc xs refl refl (lemma xs)
lemma (snoc {s' = Collecting pay sigs} {i = Pay} xs x) = snoc xs x _ (lemma xs)
