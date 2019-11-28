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

open import Relation.Nullary.Decidable using (⌊_⌋)

open import UTxO.Hashing.Base using (_♯ₛₜᵣ)
open import UTxO.Types
open import StateMachine.Base renaming (mkValidator to mkValidator₀)

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

  IsDataᵍⁱ : IsData GameInput
  toData   {{IsDataᵍⁱ}} (StartGame hs)         = H hs
  toData   {{IsDataᵍⁱ}} (Guess cs hs)          = LIST (toData cs ∷ H hs ∷ [])
  fromData {{IsDataᵍⁱ}} (H hs)                 = just (StartGame hs)
  fromData {{IsDataᵍⁱ}} (LIST (d ∷ H hs ∷ [])) = mapₘ (λ cs → Guess cs hs) (fromData d)
  fromData {{IsDataᵍⁱ}} _                      = nothing


init : GameState → Bool
init Initialised = true
init (Locked _)  = false

final : GameState → Bool
final = const false

step : GameState → GameInput → Maybe (GameState × TxConstraints)
step Initialised (StartGame hs) = just (Locked hs  , forge≡ 1)
step (Locked hs) (Guess cs hs′) = if ⌊ (cs ♯ₛₜᵣ) ≟ℕ hs ⌋
                                    then just (Locked hs′ , forge≡ 0 && thisValueSpent≡ 1 && valueToOwnHash≡ 1)
                                    else nothing
step _           _              = nothing


GameStateMachine : StateMachine GameState GameInput
GameStateMachine = SM[ init , final , step ]

mkValidator : Validator
mkValidator = mkValidator₀ GameStateMachine
