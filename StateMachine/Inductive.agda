open import UTxO.Types
open import StateMachine.Base

module StateMachine.Inductive
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open import StateMachine.Inductive.Core {sm = sm} public
open import StateMachine.Inductive.Combinators {sm = sm} public
