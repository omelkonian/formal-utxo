{-# OPTIONS --allow-unsolved-metas #-}
module StateMachine.GuessingGame where

open import Level          using (0ℓ)
open import Function       using (_∘_; const; case_of_; flip; _$_)
open import Category.Monad using (RawMonad)

open import Data.Empty   using (⊥-elim)
open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using ()
  renaming (_≟_ to _≟ℕ_)
open import Data.Integer using (+_; ∣_∣)
open import Data.Char    using (Char; toℕ; fromℕ)
open import Data.String  using (String; toList; fromList)
  renaming (_≟_ to _≟ₛ_)
open import Data.List    using (List; []; _∷_; [_]; foldr; map)

import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Relation.Nullary            using (yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (refl)

open import UTxO.Hashing.Base
open import UTxO.Value
open import UTxO.Types
open import StateMachine.Base

open import Prelude.Default
open import UTxO.Defaults

HashedString = HashId
ClearString  = String

data GameState : Set where
  Locked : HashedString → GameState

data GameInput : Set where
  Guess : ClearString → HashedString → GameInput

instance
  IsDataᵍˢ : IsData GameState
  toData   {{IsDataᵍˢ}} (Locked hs) = H hs

  fromData {{IsDataᵍˢ}} (H hs) = just (Locked hs)
  fromData {{IsDataᵍˢ}} _      = nothing

  from∘to  {{IsDataᵍˢ}} (Locked _) = refl

  from-inj {{IsDataᵍˢ}} (H hs) .(Locked hs) refl = refl
  from-inj {{IsDataᵍˢ}} (CONSTR _ _) _ ()
  from-inj {{IsDataᵍˢ}} (LIST _) _ ()
  from-inj {{IsDataᵍˢ}} (I _) _ ()
  from-inj {{IsDataᵍˢ}} (MAP _) _ ()

  IsDataᵍⁱ : IsData GameInput
  toData   {{IsDataᵍⁱ}} (Guess cs hs) = LIST (toData cs ∷ H hs ∷ [])

  fromData {{IsDataᵍⁱ}} (LIST (d ∷ H hs ∷ [])) = flip Guess hs <$> fromData d
  fromData {{IsDataᵍⁱ}} _                      = nothing

  from∘to  {{IsDataᵍⁱ}} (Guess cs hs) rewrite from∘to cs = refl

  from-inj {{IsDataᵍⁱ}} (LIST xs) (Guess cs hs) p = {!!}
  from-inj {{IsDataᵍⁱ}} (CONSTR _ _) _ ()
  from-inj {{IsDataᵍⁱ}} (H _) _ ()
  from-inj {{IsDataᵍⁱ}} (I _) _ ()
  from-inj {{IsDataᵍⁱ}} (MAP _) _ ()

GameStateMachine : StateMachine GameState GameInput
isInitial GameStateMachine = const true
isFinal   GameStateMachine = const false
step      GameStateMachine (Locked currentSecret) (Guess theGuess nextSecret) =
  if ⌊ (theGuess ♯ₛₜᵣ) ≟ℕ currentSecret ⌋ then
    just (Locked nextSecret , def)
  else
    nothing
