open import

module StateMachine.RecallProtection
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

open CEM {sm = sm}


#threads : ∀ {}


#threads [] = 0

replay-protection : ∀ {}
  → Is-just originₛₘ
    ------------------
  → #threads l ≤ 1
replay-protection = ?
