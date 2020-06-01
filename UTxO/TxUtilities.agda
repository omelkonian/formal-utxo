module UTxO.TxUtilities where

open import Level          using (0ℓ)
open import Function       using (_∘_; _∋_; flip; _$_)
open import Category.Monad using (RawMonad)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax; Σ-syntax; map₁)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Fin     using (Fin; toℕ; fromℕ<)
open import Data.Nat     using (ℕ; zero; suc; _+_; _<_; _≡ᵇ_)
  renaming (_≟_ to _≟ℕ_)

open import Data.Integer using (+_)
open import Data.Integer.Properties using () renaming (_≟_ to _≟ℤ_)

open import Data.Bool using (Bool; T; _∧_; _∨_; not)
open import Data.Bool.Properties using (T?)

open import Data.Maybe using (Maybe; just; nothing; maybe; Is-just; fromMaybe)
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List using (List; []; _∷_; [_]; length; map; _++_; filter; lookup)
open import Data.List.Properties
open import Data.List.Membership.Propositional             using (_∈_; mapWith∈; find)
open import Data.List.Membership.Propositional.Properties  using (∈-map⁻; ∈-++⁻; ∈-filter⁻)
open import Data.List.Relation.Unary.Any as Any            using (any)
open import Data.List.Relation.Unary.All                   using (all)

open import Relation.Nullary           using (yes; no)
open import Relation.Nullary.Product   using (_×-dec_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary            using (Decidable)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Prelude.Lists

open import UTxO.Crypto
open import UTxO.Value
open import UTxO.Types

record UTXO : Set where
  field
    outRef   : TxOutputRef
    out      : TxOutput
    prevTx   : Tx

open UTXO public

mkUtxo : ∀ {out} tx → out ∈ outputs tx → UTXO
outRef (mkUtxo tx out∈)   = (tx ♯) indexed-at toℕ (Any.index out∈)
out    (mkUtxo {out} _ _) = out
prevTx (mkUtxo tx _ )     = tx

utxo : Ledger → List UTXO
utxo []       = []
utxo (tx ∷ l) = filter ((SETₒ._∉? outputRefs tx) ∘ outRef) (utxo l)
             ++ mapWith∈ (outputs tx) (mkUtxo tx)

balance : List TxOutput → Value
balance = flip ∑ value

------------------------------------------------------------------------
-- Script evaluation.

⟦_⟧ : Script → (HashId × Tx × List TxOutput → Bool)
⟦ s ⟧ ρ@(h , tx , us)
  with s
... | l && r = (⟦ l ⟧ ρ) ∧ (⟦ r ⟧ ρ)
... | l || r = (⟦ l ⟧ ρ) ∨ (⟦ r ⟧ ρ)
... | Not s′ = not (⟦ s′ ⟧ ρ)
... | TickAfter⟨ t ⟩ = t ≤ˢ minˢ (range tx)
... | SpendsOutput⟨ or ⟩      = ⌊ or SETₒ.∈? outputRefs tx ⌋
... | JustMSig⟨ msig ⟩        = checkMultiSigTx msig tx
... | Forges⟨ tks ⟩           = (forge tx ≥ᶜ [ h , tks ]) ∧ ([ h , tks ] ≥ᶜ $0)
... | Burns⟨ tks ⟩            = (forge tx ≥ᶜ [ h , tks ]) ∧ ([ h , tks ] ≤ᶜ $0)
... | FreshTokens             = ⌊ all (λ{ (i , (t , q)) → (any (λ o → t ≟ℕ (toℕ i , o) ♯) us) ×-dec (q ≟ℤ (+ 1)) })
                                      (enumerate $ lookupᶜ h (forge tx)) ⌋
... | AssetToAddress⟨ addr ⟩  = ⌊ all ((fromMaybe h addr ≟ℕ_ ) ∘ address)
                                      (filter (T? ∘ (h ∈ᶜ_) ∘ value) us) ⌋
... | DoForge                 = h ∈ᶜ forge tx
... | SignedByPIDToken⟨ pid ⟩ = ⌊ all (λ s → any (T? ∘ isSignedBy tx s)
                                                 (supp $ lookupᶜ (fromMaybe h pid) (balance us)))
                                      (sigs tx)⌋
... | SpendsCur⟨ pid ⟩        = fromMaybe h pid ∈ᶜ (balance us)

--------------------------------------------------------------------------------------
-- Pending transactions (i.e. parts of the transaction being passed to a validator).

_⟨_⟩ : Ledger → TxOutputRef → Maybe Tx
[] ⟨ txo ⟩ = nothing
(tx ∷ l) ⟨ txo ⟩
  with id txo ≟ℕ tx ♯
... | yes _ = just tx
... | no  _ = l ⟨ txo ⟩

_⟦_⟧ : {X : Set} → List X → ℕ → Maybe X
_⟦_⟧ = _⁉_

getSpentOutputRef : Ledger → TxOutputRef → Maybe TxOutput
getSpentOutputRef l oRef =
  outputs <$> (l ⟨ oRef ⟩) >>= _⟦ index oRef ⟧

getSpentOutput : Ledger → TxInput → Maybe TxOutput
getSpentOutput l i = getSpentOutputRef l (outputRef i)
