{- Section 5 of the UTXOₘₐ paper -}
{-# OPTIONS --allow-unsolved-metas #-}
module UTxO.Applications where

open import Data.Product
open import Data.Integer
open import Data.List

open import UTxO.Crypto
open import UTxO.Value
open import UTxO.Types

-- 5.1 Simple single token issuance
simple_policy : TxOutputRef × SubValue → Script
simple_policy (o , v) = SpendsOutput⟨ o ⟩ && Forges⟨ v ⟩

-- 5.2 Relfelction of off-ledger assets
trusted_issuer : MultiSignature → Script
trusted_issuer msig = JustMSig⟨ msig ⟩

-- 5.3 Vesting
Tranche = Asset

postulate
  trBundle₁ trBundle₂ : SubValue

vesting : TxOutputRef × (Tranche × Bound) × (Tranche × Bound) → Script
vesting (o , (tr₁ , t₁) , (tr₂ , t₂))
  = SpendsOutput⟨ o ⟩ && Forges⟨ (tr₁ , + 1) ∷ (tr₂ , + 1) ∷ [] ⟩
 || TickAfter⟨ t₁ ⟩ && Forges⟨ trBundle₁ ⟩ && Burns⟨ [ tr₁ , + 1 ] ⟩
 || TickAfter⟨ t₂ ⟩ && Forges⟨ trBundle₂ ⟩ && Burns⟨ [ tr₂ , + 1 ] ⟩

-- 5.4 Inventrory tracker: tokens as state
inventory_tracker : MultiSignature → Script
inventory_tracker msig = JustMSig⟨ msig ⟩ && AssetToAddress⟨⟩

-- 5.6 Revocable permission
credential_token : MultiSignature → Script
credential_token msig = JustMSig⟨ msig ⟩ && DoForge
                     || AssetToAddress⟨⟩ && Not (DoForge) && SignedByPIDToken⟨⟩

must_be_on_list : MultiSignature → Script
must_be_on_list msig = SpendsCur⟨ {!!} ⟩ -- ??? credential_token(msig) cannot be filled in here??
