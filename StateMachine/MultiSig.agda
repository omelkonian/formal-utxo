module StateMachine.MultiSig where

open import Data.List
open import Data.Nat
open import Data.List.Membership.DecPropositional _≟_
open import Data.Maybe
open import Data.Product
open import Data.Bool
open import Relation.Nullary

open import Prelude.Default

open import UTxO.Value
open import UTxO.Types
open import UTxO.Hashing.Base
open import StateMachine.Base

-- not sure if this is a suitable hash definition
PubKeyHash = HashId

Slot = ℕ

Signatories : List PubKeyHash
Signatories = []

Threshold : ℕ
Threshold = 3

record Payment : Set where
  field
    paymentAmount    : Value
    paymentRecipient : PubKeyHash
    paymentDeadline  : Slot

data State : Set where
  Holding              :                             _
  CollectingSignatures : Payment → List PubKeyHash → _

data Input : Set where
  ProposePayment : Payment    → Input
  AddSignatures  : PubKeyHash → Input
  Cancel         :              Input
  Pay            :              Input

instance
  IsData-MS : IsData State
  toData ⦃ IsData-MS ⦄ = {!!}
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
  just (CollectingSignatures p (sig ∷ sigs) , {!!})
... | yes q  | yes r = nothing -- already signed

step MultiSigSM (CollectingSignatures p sigs) Cancel =
  just (Holding , {!!})
step MultiSigSM (CollectingSignatures p sigs) Pay with length sigs ≥? Threshold
... | yes q = just (Holding , {!!})
... | no ¬q = nothing
step MultiSigSM _ _ = nothing

origin MultiSigSM = nothing

