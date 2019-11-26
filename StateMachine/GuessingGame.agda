module StateMachine.GuessingGame where

open import Function using (_∘_; const; case_of_)

open import Data.Bool    using (Bool; true; false; _∧_)
open import Data.Product using (_,_)
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
open import UTxO.Types using ( HashId; Value; _≟ᶜ_; _≥ᶜ_; $0
                             ; DATA; I; H; LIST
                             ; IsData; toData; fromData; IsDataˢ
                             ; PendingTx; PendingTxOutput
                             ; findData; getContinuingOutputs; ownCurrencySymbol; valueSpent )

open import StateMachine.Base as SM using (Validator; StateMachine; SM[_,_,_])

HashedString = HashId
TokenName    = HashId
ClearString  = String

data GameState : Set where
  Initialised : HashedString → GameState
  Locked      : TokenName → HashedString → GameState

data GameInput : Set where
  ForgeToken : TokenName → GameInput
  Guess      : ClearString → HashedString → GameInput

instance
  IsDataᵍˢ : IsData GameState
  toData   {{IsDataᵍˢ}} (Initialised hs)          = H hs
  toData   {{IsDataᵍˢ}} (Locked tn hs)            = LIST (H tn ∷ H hs ∷ [])
  fromData {{IsDataᵍˢ}} (H hs)                    = just (Initialised hs)
  fromData {{IsDataᵍˢ}} (LIST (H tn ∷ H hs ∷ [])) = just (Locked tn hs)
  fromData {{IsDataᵍˢ}} _                         = nothing

  IsDataᵍⁱ : IsData GameInput
  toData   {{IsDataᵍⁱ}} (ForgeToken tn)        = H tn
  toData   {{IsDataᵍⁱ}} (Guess cs hs)          = LIST (toData cs ∷ H hs ∷ [])
  fromData {{IsDataᵍⁱ}} (H tn)                 = just (ForgeToken tn)
  fromData {{IsDataᵍⁱ}} (LIST (d ∷ H hs ∷ [])) = mapₘ (λ cs → Guess cs hs) (fromData d)
  fromData {{IsDataᵍⁱ}} _                      = nothing

step : GameState → GameInput → Maybe GameState
step (Initialised s) (ForgeToken tn)      = just (Locked tn s)
step (Locked tn _)   (Guess _ nextSecret) = just (Locked tn nextSecret)
step _               _                    = nothing

checkGuess : HashedString → ClearString → Bool
checkGuess hashed clear = ⌊ (clear ♯ₛₜᵣ) ≟ℕ hashed ⌋

check : GameState → GameInput → PendingTx → Bool
check state input ptx = case (state , input) of λ
  { (Initialised _ , ForgeToken tn)    → checkForge (tokenVal tn)
  ; (Locked tn cur , Guess theGuess _) → checkGuess cur theGuess ∧ tokenPresent tn ∧ checkForge $0
  ; _                                  → false }
  where
    tokenVal : TokenName → Value
    tokenVal tn = [ ownCurrencySymbol ptx , [ tn , 1 ] ]

    tokenPresent : TokenName → Bool
    tokenPresent tn = valueSpent ptx ≥ᶜ tokenVal tn

    checkForge : Value → Bool
    checkForge v = ⌊ v ≟ᶜ PendingTx.forge ptx ⌋

GameStateMachine : StateMachine GameState GameInput
GameStateMachine = SM[ step , check , const false ]

mkValidator : Validator
mkValidator = SM.mkValidator GameStateMachine
