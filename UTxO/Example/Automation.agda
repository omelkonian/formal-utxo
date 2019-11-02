{-# OPTIONS --rewriting #-}
module Example.Automation where

open import Example.Setup public

open import Function using (case_of_) public
open import Level using () renaming (zero to lzero)  public

open import Data.String using (String) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; setoid) public
open import Relation.Nullary using (Dec) public
open import Data.List.Relation.Unary.Any using (any) public

-- open import Agda.Builtin.Reflection public
open import Reflection renaming (_≟_ to _`≟_) public

l₀ : Ledger
l₀ = c₁ ∷ []

-- infixl 1 _>>=_
-- _>>=_ = bindTC

pattern vArg x   = arg (arg-info visible relevant) x
pattern hArg x   = arg (arg-info hidden relevant) x

pattern `λ_⇒_ s y = lam visible (abs s y)
pattern `λ_∶_⇒_ s x y = pi (vArg x) (abs s y)
pattern # x      = var x []
pattern `_ = hArg unknown

pattern `0ℓ = hArg (def (quote lzero) [])
pattern `ℕ = def (quote ℕ) []
pattern _`≡_ x y = def (quote _≡_) (`0ℓ ∷ hArg `ℕ ∷ vArg x ∷ vArg y ∷ [])

pattern `TxInput = def (quote TxInput) []
pattern `≡ₜ_ x = def (quote _≡_) (`0ℓ ∷ hArg `TxInput ∷ vArg x ∷ [])

import UTxO.Ledger as UX
pattern `addresses = def (quote addresses) []
pattern `Tx = def (quote UX.Tx) (vArg `addresses ∷ [])
pattern `inputs x = def (quote UX.inputs) (`_ ∷ vArg x ∷ [])

pattern `id x = def (quote id) (vArg x ∷ [])
pattern `outputRef x = def (quote outputRef) (vArg x ∷ [])
pattern `♯ x = def (quote _♯) (`0ℓ ∷ hArg `Tx ∷ vArg x ∷ [])

pattern `Any f xs = def (quote Any) (`0ℓ ∷ hArg `Tx ∷ `0ℓ ∷ vArg f ∷ vArg xs ∷ [])
pattern `Any≡ x xs = def (quote Any) (`0ℓ ∷ hArg `TxInput ∷ `0ℓ ∷ vArg (`≡ₜ_ x) ∷ vArg xs ∷ [])

pattern `setoid = def (quote setoid) (`0ℓ ∷ vArg `TxInput ∷ [])
pattern _`∈_ x y = def (quote _∈_) (`0ℓ ∷ `0ℓ ∷ vArg `setoid ∷ vArg x ∷ vArg y ∷ [])

open import Relation.Binary using (Setoid) public

setoid′ : Setoid _ _
setoid′ = setoid {lzero} TxInput

import Data.List.Membership.Setoid as S

_∈′_ : TxInput → List TxInput → Set
x ∈′ xs = S._∈_ {lzero} {lzero} setoid′ x xs


pattern _`∈′_ x y = def (quote _∈′_) (vArg x ∷ vArg y ∷ [])

pattern vtx i i∈ tx t l =
  `λ i ∶ `TxInput ⇒
    `λ i∈ ∶ (# 0) `∈′ (`inputs t) ⇒
      `Any (`λ tx ⇒ ((`♯ (# 0)) `≡ (`id (`outputRef (# 2))))) l

getData : Term → TC (String × String × String × Term × Term)
getData (vtx i i∈ tx t l) = returnTC (i , i∈ , tx , t , l)
getData t = typeError ( strErr "expecting" ∷ termErr (vtx "i" "i∈" "tx" unknown unknown)
                      ∷ strErr ", but was given" ∷ termErr t ∷ [] )

macro
  by-magic : Term → TC ⊤
  by-magic hole = do
    goal ← inferType hole
    (i , i∈ , tx , t , l) ← getData goal
    case goal `≟ (vtx i i∈ tx t l) of λ
      { (no  _) → typeError [ strErr "no¹" ]
      ; (yes refl) → do
          t′ ← unquoteTC t
          l′ ← unquoteTC l
          case validTxRefs? t′ l′ of λ
            { (no _) → typeError [ strErr "no²" ]
            ; (yes p) → quoteTC p >>= unify hole }}

v₀₀ : ∀ (i : TxInput) → (i∈ : i ∈′ (inputs t₁)) → Any (λ tx → tx ♯ ≡ id (outputRef i)) l₀
v₀₀ = toWitness {Q = validTxRefs? t₁ l₀} tt
  -- by-magic

--------------------------------------------------------------------------------

v₀ : ∀ i → i ∈ inputs t₂ → Any (λ tx → tx ♯ ≡ id (outputRef i)) l₁
v₀ = toWitness {Q = validTxRefs? t₂ l₁} tt

macro
  by-magic2 : ∀ {tx : Tx} {l : Ledger} {v : ∀ i → i ∈ inputs tx → Any (λ t → t ♯ ≡ id (outputRef i)) l}
            → Term → TC ⊤
  by-magic2 {t} {l} {v} hole with validOutputIndices? t l v
  ... | no ¬p = do goal ← inferType hole
                   ¬p′ ← quoteTC ¬p
                   typeError (termErr goal ∷ strErr " does not hold, as evidenced by: " ∷ termErr ¬p′ ∷ [])
  ... | yes p = quoteTC p >>= unify hole


v₁ : ∀ i → (i∈ : i ∈ inputs t₂) →
       index (outputRef i) < length (outputs (lookupTx l₁ (outputRef i) (v₀ i i∈)))
v₁ = toWitness {Q = validOutputIndices? t₂ l₁ v₀} tt
 -- by-magic2 {t₂} {l₁} {v₀}

--------------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Agda.Builtin.Reflection using (reduce; withNormalisation; debugPrint)
open import Reflection renaming (_≟_ to _≞_)

---------------------------------------------------------------------------------------

infixl 1 _>>=_
_>>=_ = bindTC

_>>_ : ∀ {a} {b} {A : Set a} {B : Set b}
     → TC A → TC B → TC B
x >> y = x >>= λ _ → y

pattern vArg x = arg (arg-info visible relevant) x
pattern hArg x = arg (arg-info hidden relevant) x

---------------------------------------------------------------------------------------

record DD : Set where
  field
    l : List ℕ
    ll : List ℕ
open DD public

d₀ : DD
d₀ = record {l = []; ll = []}

_≟s_ : Decidable {A = List ℕ} _≡_
[]       ≟s []       = yes refl
[]       ≟s (_ ∷ _)  = no λ ()
(_ ∷ _)  ≟s []       = no λ ()
(x ∷ xs) ≟s (y ∷ ys) with x ≟ y
... | no ¬p          = no λ { refl → ¬p refl }
... | yes refl       with xs ≟s ys
... | no ¬p          = no λ { refl → ¬p refl }
... | yes refl       = yes refl

pattern vtx d =
  def (quote _≡_)
    ( hArg (def (quote lzero) [])
    ∷ hArg (def (quote List) ( hArg (def (quote lzero) [])
                             ∷ vArg (def (quote ℕ) [])
                             ∷ []
                             ))
    ∷ vArg (def (quote l) (vArg d ∷ []))
    ∷ vArg (con (quote List.[]) ( hArg unknown
                                ∷ hArg unknown
                                ∷ []
                                ))
    ∷ []
    )

getData : Term → Term
getData (vtx d) = d
getData _       = unknown

macro
  get : Term → TC ⊤
  get hole = do
    goal ← inferType hole
    let d = getData goal
    d′ ← unquoteTC d
    case goal ≞ vtx d of λ
      { (no  _) → typeError [ strErr "no¹" ]
      ; (yes _) →
          case l d′ ≟s [] of λ
            { (no _) → typeError [ strErr "no²" ]
            ; (yes p) → quoteTC p >>= unify hole
            }
      }

test : l d₀ ≡ []
test = get

---------------------------------------------------------------------------------------

-- abstract
_∈∈_ : ℕ → List ℕ → Set
x ∈∈ xs = x ∈ xs

pattern `λ_∶_⇒_ s x y = pi (vArg x) (abs s y)
pattern # x      = var x []
pattern `1 = lit (nat 1)
pattern `_ = hArg unknown
pattern `0ℓ = hArg (def (quote lzero) [])
pattern `ℕ = def (quote ℕ) []
pattern `[] = con (quote List.[]) (`_ ∷ `_ ∷ [])
pattern _`∷_ x y = con (quote _∷_) (`_ ∷ `_ ∷ vArg x ∷ vArg y ∷ [])
pattern _`≡_ x y = def (quote _≡_) (`0ℓ ∷ hArg `ℕ ∷ vArg x ∷ vArg y ∷ [])
pattern `setoid = def (quote Relation.Binary.PropositionalEquality.setoid) (`0ℓ ∷ vArg `ℕ ∷ [])
pattern _`∈_ x y = def (quote _∈_) (`0ℓ ∷ `0ℓ ∷ vArg `setoid ∷ vArg x ∷ vArg y ∷ [])
pattern _`∈∈_ x y = def (quote _∈∈_) (vArg x ∷ vArg y ∷ [])

pattern vtx2 i i∈ xs =
  `λ i ∶ `ℕ ⇒
    `λ i∈ ∶ (# 0 `∈∈ xs) ⇒
      (# 1 `≡ `1)

getData2 : Term → (String × String × Term)
getData2 (vtx2 x x∈ xs) = x , x∈ , xs
getData2 _              = "?" , "?" , unknown

dec? : ∀ {xs : List ℕ} → Dec (∀ x → x ∈ xs → x ≡ 1)
dec? {[]}     = yes λ _ ()
dec? {x ∷ xs} with x ≟ 1
... | no ¬p = no λ p → ¬p (p x (here refl))
... | yes refl with dec? {xs}
... | no ¬p = no λ p → ¬p (λ y y∈ → p y (there y∈))
... | yes p = yes λ { .1 (here refl) → refl ; y (there y∈) → p y y∈ }

macro
  get2 : Term → TC ⊤
  get2 hole = do
    goal ← inferType hole
    let (x , x∈ , xs) = getData2 goal
    case goal ≞ vtx2 x x∈ xs of λ
      { (no  _) → typeError [ strErr "no¹" ]
      ; (yes _) → do
          xs′ ← unquoteTC xs
          case dec? {xs′} of λ
            { (no _) → typeError [ strErr "no²" ]
            ; (yes p) → quoteTC p >>= unify hole }}

test2 : ∀ i → i ∈∈ (1 ∷ []) → i ≡ 1
test2 = {!!} -- get2

---------------------------------------------------------------------------------------

pattern `Any x xs =
  def (quote Any) (`0ℓ ∷ hArg `ℕ ∷ `0ℓ ∷ vArg (def (quote _≡_) (`0ℓ ∷ hArg `ℕ ∷ vArg x ∷ [])) ∷ vArg xs ∷ [])

pattern vtx3 x xs = `Any x xs

getData3 : Term → TC (Term × Term)
getData3 (vtx3 x xs) = returnTC (x , xs)
getData3 t           = typeError ( strErr "expecting"
                                 ∷ termErr (vtx3 unknown unknown)
                                 ∷ strErr ", but was given"
                                 ∷ termErr t
                                 ∷ []
                                 )

printContext : TC ⊤
printContext = do
  ctx ← getContext
  typeError (strErr "CTX:" ∷ (map (λ { (arg _ x) → termErr x}) ctx))

macro
  get3 : Term → TC ⊤
  get3 hole = do
    -- printContext
    goal ← inferType hole
    (x , xs) ← getData3 goal
    case goal ≞ (vtx3 x xs) of λ
      { (no  _) → typeError [ strErr "no¹" ]
      ; (yes _) → do
          x′ ← unquoteTC x
          xs′ ← unquoteTC xs
          case x′ ∈? xs′ of λ
            { (no _) → typeError [ strErr "no²" ]
            ; (yes p) → quoteTC p >>= unify hole }}

test3 : Any (1 ≡_) (1 ∷ []) -- 1 ∈ (1 ∷ []) does not work
test3 = get3 -- get2
