-- Terms in de Bruijn representation, but not well-scoped

module RawTerms where

open import Data.List
open import Library

data Term : Set where
  var  : (x : ℕ) → Term
  abs  : (t : Term) → Term
  app  : (t u : Term) → Term
  ▹_   : (t : Term) → Term
  _∗_  : (t u : Term) → Term
  pair : (t u : Term) → Term
  fst  : (t : Term) → Term
  snd  : (t : Term) → Term

-- Renaming

Ren = ℕ → ℕ

liftr : Ren → Ren
liftr ρ 0       = 0
liftr ρ (suc x) = suc (ρ x)

rename : Ren → Term → Term
rename ρ (var x)    = var (ρ x)
rename ρ (abs t)    = abs (rename (liftr ρ) t)
rename ρ (app t u)  = app (rename ρ t) (rename ρ u)
rename ρ (▹ t)      = ▹ (rename ρ t)
rename ρ (t ∗ u)    = (rename ρ t) ∗ (rename ρ u)
rename ρ (pair t u) = pair (rename ρ t) (rename ρ u)
rename ρ (fst t)    = fst (rename ρ t)
rename ρ (snd t)    = snd (rename ρ t)

-- Parallel substitution

Subst = ℕ → Term

-- Identity substitution

ids : Subst
ids = var

-- Substitution for 0th variable

sgs : Term → Subst
sgs t 0       = t
sgs t (suc x) = var x

 -- Weakening

weaks : Subst → Subst
weaks σ x = rename suc (σ x)

-- Lifiting a substitution

lifts : Subst → Subst
lifts σ 0       = var 0
lifts σ (suc x) = rename suc (σ x)

-- Performing a substitution

subst : Subst → Term → Term
subst σ (var x)   = σ x
subst σ (abs t)   = abs (subst (lifts σ) t)
subst σ (app t u) = app (subst σ t) (subst σ u)
subst σ (▹ t)     = ▹ (subst σ t)
subst σ (t ∗ u)   = (subst σ t) ∗ (subst σ u)
subst σ (pair t u) = pair (subst σ t) (subst σ u)
subst σ (fst t)    = fst (subst σ t)
subst σ (snd t)    = snd (subst σ t)

-- Substituting for the 0th variable [u/0]t

subst0 : Term → Term → Term
subst0 u = subst (sgs u)

--

-- Shallow one-hole full reduction contexts

data Shole : (Term → Term) → Set where
  abs   : Shole abs
  appl  : ∀ u  → Shole (λ t → app t u)
  appr  : ∀ t  → Shole (app t)
  pairl : ∀ u  → Shole (λ t → pair t u)
  pairr : ∀ t  → Shole (pair t)
  fst   : Shole fst
  snd   : Shole snd
  _∗l   : ∀ u  → Shole (λ t → t ∗ u)
  ∗r_   : ∀ t  → Shole (λ u → t ∗ u)

-- Depth-indexed reduction

data _-⟨_⟩→_ : Term → ℕ → Term → Set where
  β     : ∀{n t u}                 → app (abs t) u -⟨ n ⟩→ subst0 u t
  β▹    : ∀{n t u}                 → ((▹ t) ∗ (▹ u)) -⟨ n ⟩→ ▹ (app t u)
  βfst  : ∀{n t u}                 → fst (pair t u) -⟨ n ⟩→ t
  βsnd  : ∀{n t u}                 → snd (pair t u) -⟨ n ⟩→ u
  ▹_    : ∀{n t t'} → t -⟨ n ⟩→ t' → ▹ t -⟨ suc n ⟩→ ▹ t'
  cong  : ∀{C}(sh : Shole C) →
          ∀{n t t'} → t -⟨ n ⟩→ t' → C t -⟨ n ⟩→ C t'

{- Compatibility rules
  abs   : ∀{n t t'}   → t -⟨ n ⟩→ t' → abs t -⟨ n ⟩→ abs t'
  appl  : ∀{n t t' u} → t -⟨ n ⟩→ t' → app t u -⟨ n ⟩→ app t' u
  appr  : ∀{n t u u'} → u -⟨ n ⟩→ u' → app t u -⟨ n ⟩→ app t u'
  _∗l   : ∀{n t t' u} → t -⟨ n ⟩→ t' → (t ∗ u) -⟨ n ⟩→ (t' ∗ u)
  ∗r_   : ∀{n t u u'} → u -⟨ n ⟩→ u' → (t ∗ u) -⟨ n ⟩→ (t ∗ u')
  pairl : ∀{n t t' u} → t -⟨ n ⟩→ t' → pair t u -⟨ n ⟩→ pair t' u
  pairr : ∀{n t u u'} → u -⟨ n ⟩→ u' → pair t u -⟨ n ⟩→ pair t u'
  fst   : ∀{n t t'}   → t -⟨ n ⟩→ t' → fst t -⟨ n ⟩→ fst t'
  snd   : ∀{n t t'}   → t -⟨ n ⟩→ t' → snd t -⟨ n ⟩→ snd t'
-}

-- Predicate semantic

UU = Term → Set

-- Strong normalization

-- sn : ℕ → UU
-- sn n = Acc (λ t' t → t -⟨ n ⟩→ t')

data sn (n : ℕ) (t : Term) : Set where
  acc : (∀ {t'} → t -⟨ n ⟩→ t' → sn n t') → sn n t

-- Closure properties of sn

-- A direct sub term of a sn term is sn.

subsn : ∀{C} (sh : Shole C) {n t} → sn n (C t) → sn n t
subsn sh (acc ih) = acc (λ red → subsn sh (ih (cong sh red)))

-- Strongly normalizing contexts

snHole : ∀ n {C} (sh : Shole C) → Set
snHole n abs       = ⊤
snHole n (appl u)  = sn n u
snHole n (appr t)  = sn n t
snHole n (pairl u) = sn n u
snHole n (pairr t) = sn n t
snHole n fst       = ⊤
snHole n snd       = ⊤
snHole n (t ∗l)    = sn n t
snHole n (∗r u)    = sn n u

-- Evaluation contexts

data Ehole : (Term → Term) → Set where
  appl  : ∀ u  → Ehole (λ t → app t u)
  fst   : Ehole fst
  snd   : Ehole snd
  _∗l   : ∀ u  → Ehole (λ t → t ∗ u)
  ∗r_   : ∀ t  → Ehole (λ u → (▹ t) ∗ u)

-- Inductive SN

mutual

-- Strongly normalizing evaluation contexts

  data SNhole (n : ℕ) : (Term → Term) → Set where
    appl  : ∀{u} → SN n u     → SNhole n (λ t → app t u)
    fst   : SNhole n fst
    snd   : SNhole n snd
    _∗l   : ∀{u} → SN n u     → SNhole n (λ t → t ∗ u)
    ∗r_   : ∀{t} → SN n (▹ t) → SNhole n (λ u → (▹ t) ∗ u)

{-
  record SNHole (n : ℕ) : Set where
    constructor snhole
    field
      shole  : Term → Term
      isSN   : SNhole n shole

  -- Stacking evaluation context, innermost first

  SNHole* : (n : ℕ) → Set
  SNHole* n = List (SNHole n)

  -- Plugging a hole

  _•_ : ∀{n} (t : Term) (E* : SNHole* n) → Term
  t • [] = t
  t • (snhole E _ ∷ E*) = E t • E*

  -- Strongly neutral

  record SNe' (n : ℕ) (t : Term) : Set where
    constructor ne
    field
      head : ℕ
      elim : SNHole* n
      plug : (var head • elim) ≡ t

-}

  data SNe (n : ℕ) : Term → Set where
    var  : ∀ x                            → SNe n (var x)
    elim : ∀ {t E} → SNe n t → SNhole n E → SNe n (E t)

  -- Strongly normalizing

  data SN : ℕ → Term → Set where
    ne   : ∀{n t}   → SNe n t         → SN n t
    abs  : ∀{n t}   → SN n t          → SN n (abs t)
    pair : ∀{n t u} → SN n t → SN n u → SN n (pair t u)
    ▹0_  : ∀{t}                       → SN 0 (▹ t)
    ▹_   : ∀{n t}   → SN n t          → SN (suc n) (▹ t)
    exp  : ∀{n t t'} → t ⟨ n ⟩⇒ t' → SN n t' → SN n t

  -- Strong head reduction

  data _⟨_⟩⇒_ : Term → ℕ → Term → Set where
    β     : ∀{n t u} → SN n u       → app (abs t) u   ⟨ n ⟩⇒ subst (sgs u) t
    β▹    : ∀{n t u}                → ((▹ t) ∗ (▹ u)) ⟨ n ⟩⇒ ▹ (app t u)
    βfst  : ∀{n t u} → SN n u       → fst (pair t u)  ⟨ n ⟩⇒ t
    βsnd  : ∀{n t u} → SN n t       → snd (pair t u)  ⟨ n ⟩⇒ u
--    ▹_    : ∀{n t t'} → t ⟨ n ⟩⇒ t' → ▹ t ⟨ suc n ⟩⇒ ▹ t'
    cong  : ∀{n}{E} → Ehole E → -- NOT NEEDED: (sh : SNhole n E) →
            ∀{t t'} → t ⟨ n ⟩⇒ t' → E t             ⟨ n ⟩⇒ E t'


  -- data SNe (n : ℕ) : Term → Set where
  --   var  : ∀ x                           → SNe n (var x)
  --   app  : ∀{t u} → SNe n t    → SN n u  → SNe n (app t u)
  --   fst  : ∀{t}   → SNe n t              → SNe n (fst t)
  --   snd  : ∀{t}   → SNe n t              → SNe n (snd t)
  --   _*l_ : ∀{t u} → SNe n t    → SN  n u → SNe n (t ∗ u)
  --   _*r_ : ∀{t u} → SN n (▹ t) → SNe n u → SNe n ((▹ t) ∗ u)

-- Variables are SN

varSN : ∀{n x} → var x ∈ SN n
varSN = ne (var _)

-- Closure of SN by application to variable

appVarSN : ∀{n t x} → t ∈ SN n → app t (var x) ∈ SN n
appVarSN (ne sne) = ne (elim sne (appl varSN))
appVarSN (abs snt) = exp (β varSN) {!!}
appVarSN (exp shr snt) = exp (cong (appl (var _)) shr) (appVarSN snt)
-- Ill-typed cases:
appVarSN (pair snt snt₁) = {!!}
appVarSN ▹0_ = {!!}
appVarSN (▹ snt) = {!!}

-- Closure by strong head expansion

Closed : (n : ℕ) (AA : UU) → Set
Closed n AA = ∀{ t t'} → t ⟨ n ⟩⇒ t' → t' ∈ AA → t ∈ AA

data Cl (n : ℕ) (AA : UU) (t : Term) : Set where
  emb : AA t                             → Cl n AA t
  exp : ∀{t'} → t ⟨ n ⟩⇒ t' → Cl n AA t' → Cl n AA t

-- Semantic types

_⟦→⟧_ : UU → UU → UU
(AA ⟦→⟧ BB) t = ∀{u} → AA u → BB (app t u)

_⟦×⟧_ : UU → UU → UU
(AA ⟦×⟧ BB) t = AA (fst t) × BB (snd t)

data _⟦▸⟧_ (n : ℕ) (AA : UU) : UU where
  emb : ∀{t}  → AA t                       → (n ⟦▸⟧ AA) (▹ t)
  exp : ∀{t t'} → t ⟨ n ⟩⇒ t' → (n ⟦▸⟧ AA) t' → (n ⟦▸⟧ AA) t

-- Saturated sets

record SAT (n : ℕ) (AA : UU) : Set where
  field
    satne   : SNe n ⊆ AA
    satsn   : AA ⊆ SN n
    satexp  : Closed n AA

-- Closure properties of semantic types

sat→ : ∀{n AA BB} → AA ⊆ SN n → BB ∈ SAT n → (AA ⟦→⟧ BB) ∈ SAT n
sat→ snA satB = record
  { satne  = λ sne aa → SAT.satne satB (elim sne (appl (snA aa)))
  ; satsn  = λ ff → {!!}
  ; satexp = {!!}
  }

-- Function space is closed under expansion

cl→ : ∀ {AA BB} n {t t'} → t ⟨ n ⟩⇒ t' → t' ∈ (AA ⟦→⟧ BB) → t ∈ (AA ⟦→⟧ BB)
cl→ n red ff aa = {!!}


semAbs : ∀{AA BB t} n → (∀{u} → u ∈ AA → subst0 u t ∈ BB) → abs t ∈ (AA ⟦→⟧ BB)
semAbs n h aa = {!cl→ n (β ?) {!(h aa)!}!}

{-
-- One-step Reduction

data _⟶_ : Term → Term → Set where
  β    : ∀{t u}             → app (abs t) u ⟶ subst (sgs u) t
  abs  : ∀{t t'}   → t ⟶ t' → abs t ⟶ abs t'
  appl : ∀{t t' u} → t ⟶ t' → app t u ⟶ app t' u
  appr : ∀{t u u'} → u ⟶ u' → app t u ⟶ app t u'

free : Term → List ℕ
free (var x)   = x ∷ []
free (abs t)   = gfilter {!!} (free t)
free (app t u) = free t ++ free u

-}
