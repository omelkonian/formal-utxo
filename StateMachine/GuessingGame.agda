{-# OPTIONS --allow-unsolved-metas #-}
module StateMachine.GuessingGame where

open import Function using (_∘_; const; case_of_)

open import Data.Empty   using (⊥-elim)
open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe   using (Maybe; just; nothing; _>>=_; ap)
  renaming (map to mapₘ)
open import Data.Nat     using ()
  renaming (_≟_ to _≟ℕ_)
open import Data.Integer using (+_; ∣_∣)
open import Data.Char    using (Char; toℕ; fromℕ)
open import Data.String  using (String; toList; fromList)
  renaming (_≟_ to _≟ₛ_)
open import Data.List    using (List; []; _∷_; [_]; foldr; map)

open import Relation.Nullary            using (yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (refl; inspect)
  renaming ([_] to ≡[_])

open import UTxO.Hashing.Base
open import UTxO.Value
open import UTxO.Types
open import StateMachine.Base

HashedString = HashId
ClearString  = String

data GameState : Set where
  Initialised : CurrencySymbol → TokenName → HashedString → GameState
  Locked      : CurrencySymbol → TokenName → HashedString → GameState

data GameInput : Set where
  ForgeToken : GameInput
  Guess      : ClearString → HashedString → GameInput

open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

instance
  IsDataᵍˢ : IsData GameState
  toData   {{IsDataᵍˢ}} (Initialised c tn hs) = CONSTR 0 (H c ∷ H tn ∷ H hs ∷ [])
  toData   {{IsDataᵍˢ}} (Locked      c tn hs) = CONSTR 1 (H c ∷ H tn ∷ H hs ∷ [])

  fromData {{IsDataᵍˢ}} (CONSTR 0 (H c ∷ H tn ∷ H hs ∷ [])) = just (Initialised c tn hs)
  fromData {{IsDataᵍˢ}} (CONSTR 1 (H c ∷ H tn ∷ H hs ∷ [])) = just (Locked      c tn hs)
  fromData {{IsDataᵍˢ}} _                                   = nothing

  from∘to  {{IsDataᵍˢ}} (Initialised _ _ _) = refl
  from∘to  {{IsDataᵍˢ}} (Locked      _ _ _) = refl

  from-inj {{IsDataᵍˢ}} (CONSTR 0 (H c ∷ H tn ∷ H hs ∷ [])) .(Initialised c tn hs) refl = refl
  from-inj {{IsDataᵍˢ}} (CONSTR 1 (H c ∷ H tn ∷ H hs ∷ [])) .(Locked      c tn hs) refl = refl
  from-inj {{IsDataᵍˢ}} (CONSTR _ _) _ p = {!!}
  from-inj {{IsDataᵍˢ}} (LIST _) _ ()
  from-inj {{IsDataᵍˢ}} (H _) _ ()
  from-inj {{IsDataᵍˢ}} (I _) _ ()
  from-inj {{IsDataᵍˢ}} (MAP _) _ ()

  IsDataᵍⁱ : IsData GameInput
  toData   {{IsDataᵍⁱ}} ForgeToken    = CONSTR 0 []
  toData   {{IsDataᵍⁱ}} (Guess cs hs) = CONSTR 1 (toData cs ∷ H hs ∷ [])

  fromData {{IsDataᵍⁱ}} (CONSTR 0 [])              = just ForgeToken
  fromData {{IsDataᵍⁱ}} (CONSTR 1 (d ∷ H hs ∷ [])) = mapₘ (λ cs → Guess cs hs) (fromData d)
  fromData {{IsDataᵍⁱ}} _                          = nothing

  from∘to  {{IsDataᵍⁱ}} ForgeToken = refl
  from∘to  {{IsDataᵍⁱ}} (Guess cs hs) rewrite from∘to cs = refl

  from-inj {{IsDataᵍⁱ}} (CONSTR 0 [])  .ForgeToken refl = refl
  from-inj {{IsDataᵍⁱ}} (CONSTR 1 (d ∷ H hs ∷ [])) g p = {!!}
  from-inj {{IsDataᵍⁱ}} (CONSTR _ _) _ p = {!!}
  from-inj {{IsDataᵍⁱ}} (LIST _) _ ()
  from-inj {{IsDataᵍⁱ}} (H _) _ ()
  from-inj {{IsDataᵍⁱ}} (I _) _ ()
  from-inj {{IsDataᵍⁱ}} (MAP _) _ ()

GameStateMachine : StateMachine GameState GameInput
isInitial GameStateMachine (Initialised _ _ _) = true
isInitial GameStateMachine (Locked      _ _ _) = false

isFinal GameStateMachine = const false

step GameStateMachine (Initialised c tn hs) ForgeToken =
  just ( Locked c tn hs
       , record defConstraints { forge≡ = just ((c , (tn , 1) ∷ []) ∷ []) })
step GameStateMachine (Locked c tn currentSecret) (Guess theGuess nextSecret) =
  if ⌊ (theGuess ♯ₛₜᵣ) ≟ℕ currentSecret ⌋ then
    just ( Locked c tn nextSecret
         , record defConstraints { forge≡ = just ((c , (tn , 0) ∷ []) ∷ [])
                                 ; spent≥ = just ((c , (tn , 1) ∷ []) ∷ []) })
  else
    nothing
step GameStateMachine _ _ =
  nothing

gameValidator : Validator
gameValidator = mkValidator GameStateMachine
