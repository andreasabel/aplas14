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
  β     : ∀{n t u}                 → app (abs t) u -⟨ n ⟩→ subst (sgs u) t
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

-- SN : ℕ → UU
-- SN n = Acc (λ t' t → t -⟨ n ⟩→ t')

data SN (n : ℕ) (t : Term) : Set where
  acc : (∀ {t'} → t -⟨ n ⟩→ t' → SN n t') → SN n t

-- Closure properties of SN

-- A direct sub term of a SN term is SN.

subSN : ∀{C} (sh : Shole C) {n t} → SN n (C t) → SN n t
subSN sh (acc ih) = acc (λ red → subSN sh (ih (cong sh red)))

-- Strongly normalizing contexts

SNHole : ∀ n {C} (sh : Shole C) → Set
SNHole n abs       = ⊤
SNHole n (appl u)  = SN n u
SNHole n (appr t)  = SN n t
SNHole n (pairl u) = SN n u
SNHole n (pairr t) = SN n t
SNHole n fst       = ⊤
SNHole n snd       = ⊤
SNHole n (t ∗l)    = SN n t
SNHole n (∗r u)    = SN n u

-- Evaluation contexts

data Ehole : (Term → Term) → Set where
  appl  : ∀ u  → Ehole (λ t → app t u)
  fst   : Ehole fst
  snd   : Ehole snd
  _∗l   : ∀ u  → Ehole (λ t → t ∗ u)
  ∗r_   : ∀ t  → Ehole (λ u → (▹ t) ∗ u)

data _⟨_⟩⇒_ : Term → ℕ → Term → Set where
  β     : ∀{n t u}                 → app (abs t) u ⟨ n ⟩⇒ subst (sgs u) t
  β▹    : ∀{n t u}                 → ((▹ t) ∗ (▹ u)) ⟨ n ⟩⇒ ▹ (app t u)
  βfst  : ∀{n t u}                 → fst (pair t u) ⟨ n ⟩⇒ t
  βsnd  : ∀{n t u}                 → snd (pair t u) ⟨ n ⟩⇒ u
  ▹_    : ∀{n t t'} → t ⟨ n ⟩⇒ t' → ▹ t ⟨ suc n ⟩⇒ ▹ t'
  cong  : ∀{C}(sh : Shole C) →
          ∀{n t t'} → t ⟨ n ⟩⇒ t' → C t ⟨ n ⟩⇒ C t'

-- Strong head reduction

_⟦→⟧_ : UU → UU → UU
(AA ⟦→⟧ BB) t = ∀{u} → AA u → BB (app t u)

_⟦×⟧_ : UU → UU → UU
(AA ⟦×⟧ BB) t = AA (fst t) × BB (snd t)


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
