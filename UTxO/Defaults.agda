module UTxO.Defaults where

open import Prelude.Init
open import Prelude.Default

open import UTxO.Hashing
open import UTxO.Value
open import UTxO.Types
open import UTxO.Validity

instance
  Default-Value : Default Value
  Default-Value = ⌞ $0 ⌟

  Default-DATA : Default DATA
  Default-DATA = ⌞ I def ⌟

  Default-SlotRange : Default SlotRange
  Default-SlotRange = ⌞ -∞ ⋯ +∞ ⌟

  Default-TxOutputRef : Default TxOutputRef
  Default-TxOutputRef =  ⌞ def indexed-at def ⌟

  Default-InputInfo : Default InputInfo
  Default-InputInfo = ⌞ record
    { outputRef     = def
    ; validatorHash = def
    ; datumHash     = def
    ; redeemerHash  = def
    ; value         = def } ⌟

  Default-TxOutput : Default TxOutput
  Default-TxOutput = ⌞ record
    { address   = def
    ; value     = def
    ; datumHash = def } ⌟

  Default-TxInfo : Default TxInfo
  Default-TxInfo = ⌞ record
    { inputInfo      = def
    ; outputInfo     = def
    ; forge          = def
    ; policies       = def
    ; range          = def
    ; datumWitnesses = def } ⌟

  Default-TxInput : Default TxInput
  Default-TxInput = ⌞ record
    { outputRef = def
    ; validator = def
    ; redeemer  = def
    ; datum     = def } ⌟

  Default-Tx : Default Tx
  Default-Tx = ⌞ record
    { inputs         = def
    ; outputs        = def
    ; forge          = def
    ; policies       = def
    ; range          = def
    ; datumWitnesses = def } ⌟
