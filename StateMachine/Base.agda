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
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax)
open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_; T)

open import Data.Nat
  renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties

open import Data.Maybe   using (Maybe; just; nothing; fromMaybe; maybe′; Is-just)
open import Data.Maybe.Properties  using (just-injective)
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List    using (List; []; _∷_; [_]; filter; map; length; and)
open import Data.List.NonEmpty using (List⁺; _∷_; toList; _⁺++_; _++⁺_; _∷⁺_; _∷ʳ_; last)
  renaming ([_] to [_]⁺; map to map⁺; head to head⁺)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (here; there)
open import Data.List.Relation.Binary.Pointwise using (≡⇒Pointwise-≡)

open import Relation.Nullary                      using (¬_; yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋; toWitness)
open import Relation.Unary                        using (Pred)
open import Relation.Binary                       using (Rel)
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
    step      : S → I → Maybe (S × TxConstraints)
    origin    : Maybe TxOutputRef

open StateMachine public

module CEM
  {S I : Set} {{_ : IsData S}} {{_ : IsData I}} {sm : StateMachine S I}
  where

  initₛₘ   = isInitial sm
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
        { (record {value = v; address = v♯; datumHash = d♯} ∷ [])
          → ⌊ v♯ ≟ℕ 𝕍 ⌋
          ∧ (fromMaybe false $ lookupDatumPtx d♯ pti >>= fromData >>= pure ∘ initₛₘ)
        ; _ → false })
    where
      𝕋 = fromMaybe c ⦇ originₛₘ ♯ₒᵣ ⦈

  ℂ : CurrencySymbol
  ℂ = policyₛₘ ♯

  𝕋 : TokenName
  𝕋 = fromMaybe ℂ ⦇ originₛₘ ♯ₒᵣ ⦈

  nftₛₘ : TokenClass
  nftₛₘ = ℂ , 𝕋

  threadₛₘ : Value
  threadₛₘ = [ ℂ , [ 𝕋 , 1 ] ]

  validatorₛₘ : Validator
  validatorₛₘ ptx di ds
    = fromMaybe false do (s′ , tx≡) ← join ⦇ stepₛₘ (fromData ds) (fromData di) ⦈
                         pure $ outputsOK s′
                              ∧ verifyTxInfo (txInfo ptx) tx≡
                              ∧ propagates threadₛₘ ptx
    module _ where
      outputsOK : S → Bool
      outputsOK st = case getContinuingOutputs ptx of λ
        { (o ∷ []) → ⌊ datumHash o ≟ℕ toData st ♯ᵈ ⌋
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


  -- Well-rooted sequences
  _↝_ : Rel S 0ℓ
  s ↝ s′ = ∃ λ i → ∃ λ tx≡ → stepₛₘ s i ≡ just (s′ , tx≡)

  Init : Pred S 0ℓ
  Init = T ∘ initₛₘ

  data R : S → S → Set where
    root : ∀ {s} → Init s → R s s
    cons : ∀{s s′ s″} → R s s′ → s′ ↝ s″ → R s s″

  -- Lemmas
  open FocusTokenClass nftₛₘ

  fromMaybe≡ : {A B : Set} {mx : Maybe A} {f : A → Maybe B} {g : B → Bool}
    → fromMaybe false (mx >>= f >>= pure ∘ g) ≡ true
    → ∃ λ y →
          ((mx >>= f) ≡ just y)
        × T (g y)
  fromMaybe≡ {mx = just x}{f}{g} p
    with f x | inspect f x
  ... | just y | ≡[ f≡ ]
    with g y | inspect g y
  ... | true | ≡[ g≡ ]
       = y , refl , true⇒T g≡

  postulate
    lookupDatum-helper : ∀ {pti : PendingMPS} {d♯ : HashId} {s : S}
      → (lookupDatumPtx d♯ pti >>= fromData) ≡ just s
        ---------------------------------------------
      → d♯ ≡ toData s ♯ᵈ

  Tpolicy⇒ : ∀ {tx l pti}
    → this pti ≡ ℂ
    → txInfo pti ≡ mkTxInfo l tx
    → T (policyₛₘ pti)
    → ∃ λ v → ∃ λ s →
          (forge tx ◆ ≡ 1)
        × outputsOf nftₛₘ pti ≡ [ record {value = v; address = 𝕍; datumHash = toData s ♯ᵈ} ]
        × Init s
  Tpolicy⇒ {tx = tx}{l}{pti@(record {this = .ℂ; txInfo = txi})} refl refl h₀
    with forge tx ◆ ≟ℕ 1 | h₀
  ... | no  _    | ()
  ... | yes frg≡ | h₁
    with spentsOrigin txi | h₁
  ... | false | ()
  ... | true  | h₂
    with outputsOf nftₛₘ pti | h₂
  ... | [] | ()
  ... | _ ∷ _ ∷ _ | ()
  ... | record {value = v; address = v♯; datumHash = d♯} ∷ [] | h₃
    with v♯ ≟ℕ 𝕍 | h₃
  ... | no  _    | ()
  ... | yes refl | h₄
    with fromMaybe false (lookupDatumPtx d♯ pti >>= fromData >>= pure ∘ initₛₘ)
       | inspect (fromMaybe false) (lookupDatumPtx d♯ pti >>= fromData >>= pure ∘ initₛₘ)
       | h₄
  ... | false | _        | ()
  ... | true  | ≡[ fm≡ ] | _
    with s , fm≡′ , Tinit ← fromMaybe≡ {mx = lookupDatumPtx d♯ pti}{fromData}{initₛₘ} fm≡
      = v , s , frg≡
      , cong (λ x → [ record {value = v; address = v♯; datumHash = x} ])
             (lookupDatum-helper {pti = pti}{d♯}{s} fm≡′)
      , Tinit

  ◆∈⇒Tpolicy : ∀ {tx l}
    → IsValidTx tx l
    → ◆∈ forge tx
    → T (policyₛₘ $ toPendingMPS l tx ℂ)
  ◆∈⇒Tpolicy {tx} {l} vtx ◆∈ = policy≡
    where
      policy≡ : T (policyₛₘ $ toPendingMPS l tx ℂ)
      policy≡ = All.lookup (allPoliciesValidate vtx) $ ∈♯ $ All.lookup (forging vtx) $ ◆-currencies∈ ◆∈

  module JustOrigin (just-origin : Is-just originₛₘ) where

    𝕆 : TxOutputRef
    𝕆 = proj₁ $ destruct-Is-just just-origin

    o∈ : ∀ {txi} → T (spentsOrigin txi) → 𝕆 ∈ map InputInfo.outputRef (TxInfo.inputInfo txi)
    o∈ p with originₛₘ
    ... | nothing = ⊥-elim $ Is-just⇒≢nothing just-origin refl
    ... | just _  = toWitness p

    frg◆≤1 : ∀ {tx} {l} → IsValidTx tx l → forge tx ◆ ≤ 1
    frg◆≤1 {tx} {l} vtx = ¬>⇒≤ ¬frg◆>1
      where
        ¬frg◆>1 : ¬ (forge tx ◆ > 1)
        ¬frg◆>1 frg◆>1 = <⇒≢ frg◆>1 (sym frg≡1)
          where
            ◆∈frg : ◆∈ forge tx
            ◆∈frg = ≤⇒pred≤ frg◆>1

            Tpolicy : T (policyₛₘ $ toPendingMPS l tx ℂ)
            Tpolicy = ◆∈⇒Tpolicy vtx ◆∈frg

            frg≡1 : forge tx ◆ ≡ 1
            frg≡1 = toWitness {Q = lookupQuantity (ℂ , 𝕋) (forge tx) ≟ℕ 1} (proj₁ $ T-∧ Tpolicy)

    ∃forging : ∀ {l}
      → ValidLedger l
      → ∑ l forge ◆ > 0
      → ∃ λ tx → ∃ λ l′ →
          ValidLedger (tx ∷ l′)
        × tx ∷ l′ ≼ l
        × (◆∈ forge tx)
    ∃forging {tx ∷ l} vl₀@(vl ⊕ .tx ∶- vtx) ∑>0
      rewrite +ᶜ-◆ {x = forge tx} {y = ∑ l forge}
      with ◆∈? forge tx
    ... | no  ◆∉ rewrite ¬x>0⇒x≡0 ◆∉ | +-identityˡ (∑ l forge ◆)
                 with tx , l′ , vl′ , l′≺ , ◆∈ ← ∃forging vl ∑>0
                    = tx , l′ , vl′ , there l′≺ , ◆∈
    ... | yes ◆∈ = tx , l , vl₀ , here (≡⇒Pointwise-≡ refl) , ◆∈

    ∃forging² : ∀ {l}
      → ValidLedger l
      → ∑ l forge ◆ > 1
      → ∃ λ tx₁ → ∃ λ l₁ → ∃ λ tx₂ → ∃ λ l₂
          → ValidLedger (tx₁ ∷ l₁)
          × ValidLedger (tx₂ ∷ l₂)
          × tx₁ ∷ l₁ ≼ l₂
          × (◆∈ forge tx₁)
          × (◆∈ forge tx₂)
    ∃forging² {tx ∷ l} vl₀@(vl ⊕ .tx ∶- vtx) ∑>1
      rewrite +ᶜ-◆ {x = forge tx} {y = ∑ l forge}
      with ◆∈? forge tx
    ... | no  ◆∉
      rewrite ¬x>0⇒x≡0 ◆∉ | +-identityˡ (∑ l forge ◆) = ∃forging² vl ∑>1
    ... | yes ◆∈
      rewrite x>0,x≤1⇒x≡1 ◆∈ (frg◆≤1 vtx)
      with ∑>0 ← x+y>x⇒y>0 {x = 1} {y = ∑ l forge ◆} ∑>1
      with tx′ , l′ , vl′ , l′≺l , ◆∈′ ← ∃forging vl ∑>0
         = tx′ , l′ , tx , l , vl′ , vl₀ , l′≺l , ◆∈′ , ◆∈

    ◆∈⇒𝕆∈ : ∀ {tx l}
      → IsValidTx tx l
      → ◆∈ forge tx
      → 𝕆 ∈ outputRefs tx
    ◆∈⇒𝕆∈ {tx} {l} vtx ◆∈frg = outRef∈txi {tx}{l}{𝕆} $ o∈ {txi} Tspents
      where
        txi = mkTxInfo l tx

        Tpolicy : T (policyₛₘ $ toPendingMPS l tx ℂ)
        Tpolicy = ◆∈⇒Tpolicy vtx ◆∈frg

        Tspents : T (spentsOrigin txi)
        Tspents = proj₁ $ T-∧ {l = spentsOrigin txi} $ proj₂ $ T-∧ {l = ⌊ forge tx ◆ ≟ℕ 1 ⌋} Tpolicy

    nf : ∀ L → NonFungible L nftₛₘ
    nf L@(l , vl) = ¬>⇒≤ nf′
      where
        nf′ : ¬ (∑ l forge ◆ > 1)
        nf′ ∑>1
          with tx₁ , l₁ , tx₂ , l₂
             , vl₁ ⊕ .tx₁ ∶- vtx₁ , vl₂ ⊕ .tx₂ ∶- vtx₂
             , l₁≺l₂ , ◆∈₁ , ◆∈₂
             ← ∃forging² vl ∑>1
          = o∉utxo₂ o∈utxo₂
         where
          o∈₁ : 𝕆 ∈ outputRefs tx₁
          o∈₁ = ◆∈⇒𝕆∈ vtx₁ ◆∈₁

          o∈utxo₁ : 𝕆 ∈ map outRef (utxo l₁)
          o∈utxo₁ = validOutputRefs vtx₁ o∈₁

          o∉utxo₂ : 𝕆 ∉ map outRef (utxo l₂)
          o∉utxo₂ = suf-utxo vl₂ l₁≺l₂ o∈utxo₁ o∈₁

          o∈₂ : 𝕆 ∈ outputRefs tx₂
          o∈₂ = ◆∈⇒𝕆∈ vtx₂ ◆∈₂

          o∈utxo₂ : 𝕆 ∈ map outRef (utxo l₂)
          o∈utxo₂ = validOutputRefs vtx₂ o∈₂
