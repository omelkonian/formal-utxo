module StateMachine.GuessingGame where

open import Function using (_∘_; const; case_of_)

open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe   using (Maybe; just; nothing; _>>=_; ap)
  renaming (map to mapₘ)
open import Data.Nat     using ()
  renaming (_≟_ to _≟ℕ_)
open import Data.Integer using (+_; ∣_∣)
open import Data.Char    using (Char; toℕ; fromℕ)
open import Data.String  using (String; toList; fromList)
open import Data.List    using (List; []; _∷_; [_]; foldr; map)

open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (refl)

open import UTxO.Hashing.Base using (_♯ₛₜᵣ)
open import UTxO.Types
open import StateMachine.Base

HashedString = HashId
ClearString  = String

data GameState : Set where
  Initialised : GameState
  Locked      : HashedString → GameState

data GameInput : Set where
  StartGame : HashedString → GameInput
  Guess     : ClearString → HashedString → GameInput

instance
  IsDataᵍˢ : IsData GameState
  toData   {{IsDataᵍˢ}} Initialised = LIST []
  toData   {{IsDataᵍˢ}} (Locked hs) = H hs
  fromData {{IsDataᵍˢ}} (LIST [])   = just Initialised
  fromData {{IsDataᵍˢ}} (H hs)      = just (Locked hs)
  fromData {{IsDataᵍˢ}} _           = nothing

  from∘to  {{IsDataᵍˢ}} Initialised = refl
  from∘to  {{IsDataᵍˢ}} (Locked _)  = refl

  IsDataᵍⁱ : IsData GameInput
  toData   {{IsDataᵍⁱ}} (StartGame hs)         = H hs
  toData   {{IsDataᵍⁱ}} (Guess cs hs)          = LIST (toData cs ∷ H hs ∷ [])
  fromData {{IsDataᵍⁱ}} (H hs)                 = just (StartGame hs)
  fromData {{IsDataᵍⁱ}} (LIST (d ∷ H hs ∷ [])) = mapₘ (λ cs → Guess cs hs) (fromData d)
  fromData {{IsDataᵍⁱ}} _                      = nothing

  from∘to  {{IsDataᵍⁱ}} (StartGame _) = refl
  from∘to  {{IsDataᵍⁱ}} (Guess cs _)  rewrite from∘to cs = refl

GameStateMachine : StateMachine GameState GameInput
isInitial GameStateMachine Initialised = true
isInitial GameStateMachine (Locked _)  = false

isFinal GameStateMachine = const false

step GameStateMachine Initialised (StartGame hs) = just (Locked hs , record{ forge≡ = just 1; range≡ = nothing })
step GameStateMachine (Locked hs) (Guess cs hs′) = if ⌊ (cs ♯ₛₜᵣ) ≟ℕ hs ⌋ then
                                                     just (Locked hs′ , record{ forge≡ = just 0; range≡ = nothing })
                                                   else
                                                     nothing
step GameStateMachine _           _              = nothing

gameValidator : Validator
gameValidator = mkValidator GameStateMachine
