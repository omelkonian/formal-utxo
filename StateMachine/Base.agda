{-
A State Machine library for smart contracts, based on very similar
library for Plutus Smart contracts

Specification of a state machine, consisting of a transition
function that determines the next state from the current state and
an input, and a checking function that checks the validity of the
transition in the context of the current transaction.
-}
module StateMachine.Base where

open import Level    using (0ℓ)
open import Function using (_∘_; case_of_; _$_)

open import Category.Monad using (RawMonad)

open import Data.Empty   using (⊥-elim)
open import Data.Unit    using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_; T)
open import Data.Maybe   using (Maybe; just; nothing; fromMaybe; maybe′)
open import Data.List    using (List; null; []; _∷_; [_]; filter; map; length; and)
open import Data.Nat     using (ℕ)
  renaming (_≟_ to _≟ℕ_)

open import Data.Maybe.Properties  using (just-injective)
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List.Membership.Propositional using (_∈_)

open import Relation.Nullary                      using (yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; inspect; trans; sym; cong)
  renaming ([_] to ≡[_])

open import Prelude.General
open import Prelude.Lists using (enumerate)

open import UTxO.Hashing.Base
open import UTxO.Hashing.Types
open import UTxO.Value
open import UTxO.Types hiding (I)
open import UTxO.TxUtilities
open import UTxO.Validity

open import Prelude.Default
open import UTxO.Defaults

--------------------------
-- Transaction constraints

record TxConstraints : Set where
  field
    forge≡ : Maybe ValueS
    range≡ : Maybe SlotRange
    spent≥ : Maybe Value

open TxConstraints public

instance
  Default-TxConstraints : Default TxConstraints
  Default-TxConstraints = ⌞ record
    { forge≡ = def
    ; range≡ = def
    ; spent≥ = def } ⌟

_>>=ₜ_ : ∀ {a : Set} → Maybe a → (a → Bool) → Bool
ma >>=ₜ f = fromMaybe true (ma >>= pure ∘ f)

verifyTxInfo : TxInfo → TxConstraints → Bool
verifyTxInfo tx tx≡ =
  (forge≡ tx≡ >>=ₜ λ v → ⌊ TxInfo.forge tx ≟ᶜ toValue v ⌋) ∧
  (range≡ tx≡ >>=ₜ λ r → ⌊ TxInfo.range tx ≟ˢ r ⌋) ∧
  (spent≥ tx≡ >>=ₜ λ v → valueSpent tx ≥ᶜ v)

verifyTx : Ledger → Tx → TxConstraints → Bool
verifyTx l tx = verifyTxInfo (mkTxInfo l tx)


-------------------------------------
-- Constraint Emitting Machines (CEM)

record StateMachine (S I : Set) {{_ : IsData S}} {{_ : IsData I}} : Set where
  constructor SM[_,_,_]
  field
    isInitial : S → Bool
--    isFinal   : S → Bool
    step      : S → I → Maybe (S × TxConstraints)
    origin    : Maybe TxOutputRef

open StateMachine public

module CEM
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

  initₛₘ   = isInitial sm
--  finalₛₘ  = isFinal sm
  stepₛₘ   = step sm
  originₛₘ = origin sm

  spentsOrigin : TxInfo → Bool
  spentsOrigin txi =
    originₛₘ >>=ₜ λ o → ⌊ o SETₒ.∈? map InputInfo.outputRef (TxInfo.inputInfo txi) ⌋

  𝕍 : HashId

  policyₛₘ : MonetaryPolicy
  policyₛₘ pti@(record {this = c; txInfo = txi})
    = ⌊ lookupQuantity (c , 𝕋) (TxInfo.forge txi) ≟ℕ 1 ⌋
    ∧ spentsOrigin txi
    ∧ (case outputsOf (c , 𝕋) pti of λ
        { (record {validatorHash = v♯; datumHash = d♯} ∷ [])
          → ⌊ v♯ ≟ℕ 𝕍 ⌋
          ∧ (fromMaybe false $ lookupDatumPtx d♯ pti >>= fromData >>= pure ∘ initₛₘ)
        ; _ → false })
    where
      𝕋 = fromMaybe c ⦇ originₛₘ ♯ₒᵣ ⦈

  ℂ : CurrencySymbol
  ℂ = policyₛₘ ♯

  𝕋 : TokenName
  𝕋 = fromMaybe ℂ ⦇ originₛₘ ♯ₒᵣ ⦈

  threadₛₘ : Value
  threadₛₘ = [ ℂ , [ 𝕋 , 1 ] ]

  validatorₛₘ : Validator
  validatorₛₘ ptx di ds
    = fromMaybe false do (s′ , tx≡) ← join ⦇ stepₛₘ (fromData ds) (fromData di) ⦈
                         pure $ outputsOK s′
                              ∧ verifyTxInfo (txInfo ptx) tx≡
                              ∧ propagates threadₛₘ ptx
    module _ where
      outs : List OutputInfo
      outs = getContinuingOutputs ptx

      outputsOK : S → Bool
      outputsOK st =
 --       if finalₛₘ st then
 --         null outs
 --       else
          case outs of λ{ (o ∷ []) → ⌊ OutputInfo.datumHash o ≟ℕ toData st ♯ᵈ ⌋
                        ; _        → false }

  𝕍 = validatorₛₘ ♯

  -- Create a transaction input.
  infix 5 _←—_
  _←—_ : TxOutputRef → I × S → TxInput
  outputRef (r ←— _      ) = r
  redeemer  (_ ←— (i , _)) = toData i
  validator (_ ←— _      ) = validatorₛₘ
  datum     (_ ←— (_ , d)) = toData d

  -- Create a transaction output.
  infix 5 _—→_
  _—→_ : S → Value → TxOutput
  value     (_ —→ v) = v
  address   (_ —→ _) = 𝕍
  datumHash (d —→ _) = toData d ♯ᵈ

  withOutputs : List S → Tx
  withOutputs ss = record def
    { outputs        = map (_—→ threadₛₘ) ss
    ; datumWitnesses = map (λ s → toData s ♯ᵈ , toData s) ss }
