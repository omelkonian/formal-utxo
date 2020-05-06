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

,-injective : {A B : Set}{a a' : A}{b b' : B}
  → (a , b) ≡ (a' , b') → a ≡ a' × b ≡ b'
,-injective refl = refl , refl

t=-injective : ∀{n n'} → t= n ≡ t= n' → n ≡ n'
t=-injective refl = refl

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
  from-inj ⦃ isData-Bound ⦄ (CONSTR 1 (dt ∷ []))   +∞ p with IsData.fromData isData-ℕ dt
  from-inj isData-Bound (CONSTR (suc zero) (dt ∷ [])) +∞ () | nothing
  from-inj isData-Bound (CONSTR (suc zero) (dt ∷ [])) +∞ () | just x
  from-inj ⦃ isData-Bound ⦄ (CONSTR 1 (dt ∷ []))   -∞ p with IsData.fromData isData-ℕ dt
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
  IsData-MS : IsData State
  
  toData ⦃ IsData-MS ⦄ Holding = CONSTR 0 []
  toData ⦃ IsData-MS ⦄ (CollectingSignatures p sigs) = CONSTR 1
    (LIST (toData (Payment.paymentAmount p) ∷ toData (Payment.paymentRecipient p) ∷ toData (Payment.paymentDeadline p) ∷ [])
    ∷
    toData (Payment.paymentDeadline p)
    ∷ [])
  fromData ⦃ IsData-MS ⦄ = {!!}
  from∘to ⦃ IsData-MS ⦄ = {!!}
  from-inj ⦃ IsData-MS ⦄ = {!pay!}

  IsData-MI : IsData Input
  toData ⦃ IsData-MI ⦄ = {!!}
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

