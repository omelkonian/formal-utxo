module StateMachine.TeaCoffee where

open import StateMachine.Base
open import UTxO.Types

open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Data.Nat

data State : Set where
  P₁ P₂ P₃ P₄ : _

data Input : Set where
  coin request-tea request-coffee coffee tea : _

instance
  IsData-CS : IsData State
  toData   ⦃ IsData-CS ⦄ P₁ = CONSTR 1 []
  toData   ⦃ IsData-CS ⦄ P₂ = CONSTR 2 []
  toData   ⦃ IsData-CS ⦄ P₃ = CONSTR 3 []
  toData   ⦃ IsData-CS ⦄ P₄ = CONSTR 4 []
  
  fromData ⦃ IsData-CS ⦄ (CONSTR 1 []) = just P₁
  fromData ⦃ IsData-CS ⦄ (CONSTR 2 []) = just P₂
  fromData ⦃ IsData-CS ⦄ (CONSTR 3 []) = just P₃
  fromData ⦃ IsData-CS ⦄ (CONSTR 4 []) = just P₄  
  fromData ⦃ IsData-CS ⦄ _ = nothing
  
  from∘to  ⦃ IsData-CS ⦄ P₁ = refl
  from∘to  ⦃ IsData-CS ⦄ P₂ = refl
  from∘to  ⦃ IsData-CS ⦄ P₃ = refl
  from∘to  ⦃ IsData-CS ⦄ P₄ = refl

  from-inj ⦃ IsData-CS ⦄ (CONSTR 1 []) P₁ p = refl
  from-inj ⦃ IsData-CS ⦄ (CONSTR 2 []) P₂ p = refl
  from-inj ⦃ IsData-CS ⦄ (CONSTR 3 []) P₃ p = refl
  from-inj ⦃ IsData-CS ⦄ (CONSTR 4 []) P₄ p = refl
  from-inj ⦃ IsData-CS ⦄ (CONSTR 0 []) s ()
  from-inj ⦃ IsData-CS ⦄ (CONSTR (suc (suc (suc (suc (suc 0))))) []) s ()
  from-inj ⦃ IsData-CS ⦄ (I i) s ()
  from-inj ⦃ IsData-CS ⦄ (H n) s ()
  from-inj ⦃ IsData-CS ⦄ (LIST xs) s ()
  from-inj ⦃ IsData-CS ⦄ (MAP xs) s ()
  
  IsData-CI : IsData Input
  toData   ⦃ IsData-CI ⦄ coin = CONSTR 0 []
  toData   ⦃ IsData-CI ⦄ request-tea = CONSTR 1 []
  toData   ⦃ IsData-CI ⦄ request-coffee = CONSTR 2 []
  toData   ⦃ IsData-CI ⦄ tea = CONSTR 3 []
  toData   ⦃ IsData-CI ⦄ coffee = CONSTR 4 []
  
  fromData ⦃ IsData-CI ⦄ (CONSTR 0 []) = just coin
  fromData ⦃ IsData-CI ⦄ (CONSTR 1 []) = just request-tea
  fromData ⦃ IsData-CI ⦄ (CONSTR 2 []) = just request-coffee
  fromData ⦃ IsData-CI ⦄ (CONSTR 3 []) = just tea
  fromData ⦃ IsData-CI ⦄ (CONSTR 4 []) = just coffee
  fromData ⦃ IsData-CI ⦄ _ = nothing

  from∘to  ⦃ IsData-CI ⦄ coin = refl
  from∘to  ⦃ IsData-CI ⦄ request-tea = refl
  from∘to  ⦃ IsData-CI ⦄ request-coffee = refl
  from∘to  ⦃ IsData-CI ⦄ tea = refl
  from∘to  ⦃ IsData-CI ⦄ coffee = refl

  from-inj ⦃ IsData-CI ⦄ (CONSTR 0 []) coin p = refl
  from-inj ⦃ IsData-CI ⦄ (CONSTR 1 []) request-tea p = refl
  from-inj ⦃ IsData-CI ⦄ (CONSTR 2 []) request-coffee p = refl
  from-inj ⦃ IsData-CI ⦄ (CONSTR 3 []) tea p = refl
  from-inj ⦃ IsData-CI ⦄ (CONSTR 4 []) coffee p = refl
  from-inj ⦃ IsData-CI ⦄ (CONSTR (suc (suc (suc (suc (suc 0))))) []) s ()
  from-inj ⦃ IsData-CI ⦄ (I i) s ()
  from-inj ⦃ IsData-CI ⦄ (H n) s ()
  from-inj ⦃ IsData-CI ⦄ (LIST xs) s ()
  from-inj ⦃ IsData-CI ⦄ (MAP xs) s ()
