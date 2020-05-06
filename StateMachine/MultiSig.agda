module StateMachine.MultiSig where

open import Data.List
open import Data.Nat
open import Data.Integer using (+_)
open import Data.List.Membership.DecPropositional _≟_
open import Data.Maybe
open import Data.Maybe.Properties
open import Data.Product
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Prelude.Default

open import UTxO.Value
open import UTxO.Types
open import UTxO.Hashing.Base
open import StateMachine.Base

-- not sure if this is a suitable hash definition
PubKeyHash = HashId

Signatories : List PubKeyHash
Signatories = []

Threshold : ℕ
Threshold = 3

record Payment : Set where
  constructor payment
  field
    paymentAmount    : Value
    paymentRecipient : PubKeyHash
    paymentDeadline  : Bound

data State : Set where
  Holding              :                             _
  CollectingSignatures : Payment → List PubKeyHash → _

data Input : Set where
  ProposePayment : Payment    → Input
  AddSignatures  : PubKeyHash → Input
  Cancel         :              Input
  Pay            :              Input

map-just' : {A B : Set}(ma : Maybe A)(a : A)
  → (f : A → B)
  → (∀{a a'} → f a ≡ f a' → a ≡ a')
  → Data.Maybe.map f ma ≡ just (f a)
  → ma ≡ just a
map-just' (just _) a f p q = cong just (p (just-injective q)) 

map-nothing' : {A B : Set}(ma : Maybe A)
  → (f : A → B)
  → Data.Maybe.map f ma ≡ nothing
  → ma ≡ nothing
map-nothing' nothing f p = refl

ap-map-just : {A B C : Set}(ma : Maybe A)(a : A)(mb : Maybe B)(b : B)
  → (f : A → B → C)
  → (∀{a a'}{b b'} → f a b ≡ f a' b' → a ≡ a' × b ≡ b')
  → Data.Maybe.ap (Data.Maybe.map f ma) mb ≡ just (f a b)
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
  → Data.Maybe.ap (Data.Maybe.ap (Data.Maybe.map f ma) mb) mc ≡ just (f a b c)
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

CollectingSignatures-injective : ∀{p p' sigs sigs'}
  → CollectingSignatures p sigs ≡ CollectingSignatures p' sigs'
  → p ≡ p' × sigs ≡ sigs'
CollectingSignatures-injective refl = refl , refl

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
    Data.Maybe.map t=_ (fromData dt)
  fromData ⦃ isData-Bound ⦄ (CONSTR 2 [])        = just +∞  
  fromData ⦃ isData-Bound ⦄ _                    = nothing
  from∘to ⦃ isData-Bound ⦄ -∞     = refl
  from∘to ⦃ isData-Bound ⦄ (t= t) = refl
  from∘to ⦃ isData-Bound ⦄ +∞     = refl
  from-inj ⦃ isData-Bound ⦄ (CONSTR 0 [])        -∞ refl = refl
  from-inj ⦃ isData-Bound ⦄ (CONSTR 0 (_ ∷ _))   b ()
  from-inj ⦃ isData-Bound ⦄ (CONSTR 1 (dt ∷ [])) (t= t) p = cong (λ dt → CONSTR 1 [ dt ]) (from-inj dt t (map-just' (fromData dt) t  t=_ t=-injective p))
  from-inj ⦃ isData-Bound ⦄ (CONSTR 1 (dt ∷ [])) +∞ p with IsData.fromData isData-ℕ dt
  from-inj isData-Bound (CONSTR (suc zero) (dt ∷ [])) +∞ () | nothing
  from-inj isData-Bound (CONSTR (suc zero) (dt ∷ [])) +∞ () | just x
  from-inj ⦃ isData-Bound ⦄ (CONSTR 1 (dt ∷ [])) -∞ p with IsData.fromData isData-ℕ dt
  from-inj isData-Bound (CONSTR (suc zero) (dt ∷ [])) -∞ () | nothing
  from-inj isData-Bound (CONSTR (suc zero) (dt ∷ [])) -∞ () | just x
  from-inj ⦃ isData-Bound ⦄ (CONSTR 1 [])   b ()
  from-inj ⦃ isData-Bound ⦄ (CONSTR 2 [])        +∞ refl = refl
  from-inj ⦃ isData-Bound ⦄ (CONSTR 2 (_ ∷ _))   b ()
  from-inj ⦃ isData-Bound ⦄ (CONSTR (suc (suc (suc n))) xs) b ()

instance
  IsData-Pair : ∀ {A B : Set} → {{_ : IsData A}} → {{_ : IsData B}}
    → IsData (A × B)
  toData ⦃ IsData-Pair ⦄ (a , b) = LIST (toData a ∷ toData b ∷ [])
  fromData ⦃ IsData-Pair ⦄ (LIST (a ∷ b ∷ [])) =
    ap (Data.Maybe.map _,_ (fromData a)) (fromData b)
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
    ap (ap (Data.Maybe.map payment (fromData dv)) (fromData dr)) (fromData dd)
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
  toData ⦃ IsData-MS ⦄ (CollectingSignatures p sigs) = CONSTR 1 
    (toData p ∷ toData sigs ∷ [])
  fromData ⦃ IsData-MS ⦄ (CONSTR 0 []) = just Holding
  fromData ⦃ IsData-MS ⦄ (CONSTR 1 (p ∷ sigs ∷ [])) =
    ap (Data.Maybe.map CollectingSignatures (fromData p)) (fromData sigs)
  fromData ⦃ IsData-MS ⦄ _ = nothing
  from∘to ⦃ IsData-MS ⦄ Holding = refl
  from∘to ⦃ IsData-MS ⦄ (CollectingSignatures p sigs)
    rewrite from∘to p | from∘to sigs = refl

  from-inj ⦃ IsData-MS ⦄ (CONSTR 0 []) Holding p = refl
  from-inj ⦃ IsData-MS ⦄ (CONSTR 1 (dp ∷ dsigs ∷ [])) (CollectingSignatures p sigs) q =
    let
      x , x' = ap-map-just (fromData dp) p (fromData dsigs) sigs CollectingSignatures CollectingSignatures-injective q
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
  
  from-inj ⦃ IsData-MS ⦄ (CONSTR 0 []) (CollectingSignatures _ _) ()
  from-inj ⦃ IsData-MS ⦄ (CONSTR 0 (_ ∷ _)) (CollectingSignatures _ _) ()
  from-inj ⦃ IsData-MS ⦄ (CONSTR 1 []) (CollectingSignatures _ _) ()
  from-inj ⦃ IsData-MS ⦄ (CONSTR 1 (_ ∷ [])) (CollectingSignatures _ _) ()
  from-inj ⦃ IsData-MS ⦄ (CONSTR (suc (suc n)) _) _ ()

  IsData-MI : IsData Input
  toData ⦃ IsData-MI ⦄ i = {!!}
  fromData ⦃ IsData-MI ⦄ = {!!}
  from∘to ⦃ IsData-MI ⦄ = {!!}
  from-inj ⦃ IsData-MI ⦄ = {!!}

MultiSigSM : StateMachine State Input
isInitial MultiSigSM Holding =  true
isInitial MultiSigSM _ = false
step MultiSigSM Holding (ProposePayment p) = just ((CollectingSignatures p []) , def)
step MultiSigSM (CollectingSignatures p sigs) (AddSignatures sig)
  with sig ∈? Signatories | sig ∈? sigs
... | no ¬q  | _     = nothing -- not a signatory
... | yes q  | no ¬r =
  just (CollectingSignatures p (sig ∷ sigs) , def)
  -- TODO: need to add a new type of constraint to check signature
... | yes q  | yes r = nothing -- already signed

step MultiSigSM (CollectingSignatures p sigs) Cancel =
  just (Holding
       , record { forge≡ = nothing
                ; range≡ = just (Payment.paymentDeadline p ⋯ +∞)
                           -- must be after payment deadline
                ; spent≥ = nothing })
step MultiSigSM (CollectingSignatures p sigs) Pay with length sigs ≥? Threshold
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

