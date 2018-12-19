module Basic where

open import Data.Nat using (ℕ)

Address : Set
Address = ℕ

Id : Set
Id = ℕ

Value : Set
Value = ℕ

$ : ℕ → Value
$ v = v

record State : Set where
  field
    height : ℕ
open State
