module UTxO.Defaults where

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types
open import UTxO.Validity

open import Data.Nat using (ℕ)
open import Prelude.Default

instance
  Default-Value : Default Value
  Default-Value = ⌞ $0 ⌟

  Default-DATA : Default DATA
  Default-DATA = ⌞ I def ⌟

  Default-SlotRange : Default SlotRange
  Default-SlotRange = ⌞ -∞ ⋯ +∞ ⌟

  Default-TxOutputRef : Default TxOutputRef
  Default-TxOutputRef =  ⌞ def indexed-at def ⌟

  Default-TxOutput : Default TxOutput
  Default-TxOutput = ⌞ record
    { address   = def
    ; value     = def } ⌟

  Default-TxInput : Default TxInput
  Default-TxInput = ⌞ record
    { outputRef = def
    ; validator = def } ⌟

  Default-Tx : Default Tx
  Default-Tx = ⌞ record
    { inputs         = def
    ; outputs        = def
    ; forge          = def
    ; policies       = def
    ; range          = def } ⌟
