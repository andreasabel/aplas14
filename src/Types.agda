module Types where

open import Library

-- The kind of a type is its guardedness level.

Kind = ℕ

-- Subsumption for kinds is decreasing guardedness level.

_≤K_ : (g g' : Kind) → Set
g ≤K g' = g ≤ℕ g'

module ≤K = DecTotalOrderℕ

-- A type context is a list of type variables with their guardedness level.
-- We use de Bruijn representation.

TyCxt = List Kind

-- Order-preserving embedding for contexts

data _≼_ : (Γ Δ : TyCxt) → Set where
  id   : ∀ {Γ} → Γ ≼ Γ
  weak : ∀ {Γ Δ g}                     (η : Γ ≼ Δ) → (g ∷ Γ) ≼ Δ
  lift : ∀ {Γ Δ g g'} (g≤g' : g ≤K g') (η : Γ ≼ Δ) → (g ∷ Γ) ≼ (g' ∷ Δ)

-- Type variables.

data TyVar : TyCxt → Kind → Set where
  zero : ∀ {Δ g g'} (g≤g' : g ≤K g') → TyVar (g ∷ Δ) g'
  suc  : ∀ {Δ g g'} (x : TyVar Δ g') → TyVar (g ∷ Δ) g'

-- Monotonicity / map for variables

tyVar≤K : ∀ {Δ g g'} (g≤g' : g ≤K g') (x : TyVar Δ g) → TyVar Δ g'
tyVar≤K g'≤g'' (zero g≤g') = zero (≤K.trans g≤g' g'≤g'')
tyVar≤K g≤g' (suc x)       = suc (tyVar≤K g≤g' x)

tyVar≼ : ∀ {Γ Δ g} (η : Γ ≼ Δ) (x : TyVar Δ g) → TyVar Γ g
tyVar≼ id            x             = x
tyVar≼ (weak η)      x             = suc (tyVar≼ η x)
tyVar≼ (lift g≤g' η) (zero g'≤g'') = zero (≤K.trans g≤g' g'≤g'')
tyVar≼ (lift _    η) (suc x)       = suc (tyVar≼ η x)

-- Well-kinded types.

mutual

  data Ty (Δ : TyCxt) : (g : Kind) → Set where
    var : ∀ {g} (x : TyVar Δ g)    → Ty Δ g
    ▸̂_  : ∀ {g} (a : Ty Δ (suc g)) → Ty Δ g
    1̂   : ∀ {g}                    → Ty Δ g
    _×̂_ : ∀ {g} (a b : Ty Δ g)     → Ty Δ g
    _+̂_ : ∀ {g} (a b : Ty Δ g)     → Ty Δ g
    _→̂_ : ∀ {g} (a b : Ty Δ g)     → Ty Δ g
    μ̂_  : ∀ {g} (f  : TyF Δ g)     → Ty Δ (suc g)

  TyF : (Δ : TyCxt) (g : Kind) → Set
  TyF Δ g = ∀{g'} (g≤g' : g ≤K g') → Ty (suc g' ∷ Δ) g'

vzero : ∀{Δ g} → Ty (g ∷ Δ) g
vzero = var (zero ≤K.refl)

-- Weakening types

module Both where
  ty≼ : ∀{Γ Δ g g'} (g≤g' : g ≤K g') (η : Γ ≼ Δ) (a : Ty Δ g) → Ty Γ g'
  ty≼ g≤g' η (var x) = var (tyVar≤K g≤g' (tyVar≼ η x))
  ty≼ g≤g' η (▸̂ a) = ▸̂ ty≼ (s≤s g≤g') η a
  ty≼ g≤g' η 1̂     = 1̂
  ty≼ g≤g' η (a ×̂ b) = ty≼ g≤g' η a ×̂ ty≼ g≤g' η b
  ty≼ g≤g' η (a +̂ b) = ty≼ g≤g' η a +̂ ty≼ g≤g' η b
  ty≼ g≤g' η (a →̂ b) = ty≼ g≤g' η a →̂ ty≼ g≤g' η b
--  ty≼ (s≤s {g} {g'} g≤g') η (μ̂ f) = μ̂ λ {g''} g'≤g'' → ty≼ g≤g' (lift ≤K.refl η) (f g'≤g'')
  ty≼ (s≤s {g} {g'} g≤g') η (μ̂ f) = μ̂ λ {g''} g'≤g'' → ty≼ ≤K.refl (lift ≤K.refl η) (f (≤K.trans g≤g' g'≤g''))


ty≼ : ∀{Γ Δ g} (η : Γ ≼ Δ) (a : Ty Δ g) → Ty Γ g
ty≼ η (var x) = var (tyVar≼ η x)
ty≼ η (▸̂ a) = ▸̂ ty≼ η a
ty≼ η 1̂     = 1̂
ty≼ η (a ×̂ b) = ty≼ η a ×̂ ty≼ η b
ty≼ η (a +̂ b) = ty≼ η a +̂ ty≼ η b
ty≼ η (a →̂ b) = ty≼ η a →̂ ty≼ η b
ty≼ η (μ̂ f) = μ̂ λ g≤g' → ty≼ (lift ≤K.refl η) (f g≤g')

weakTy : ∀{g' Δ g} (a : Ty Δ g) → Ty (g' ∷ Δ) g
weakTy = ty≼ (weak id)

ty≤K : ∀{Δ g g'} (g≤g' : g ≤K g') (a : Ty Δ g) → Ty Δ g'
ty≤K g≤g'       (var x) = var (tyVar≤K g≤g' x)
ty≤K g≤g'       (▸̂ a)   = ▸̂ ty≤K (s≤s g≤g') a
ty≤K g≤g'       1̂       = 1̂
ty≤K g≤g'       (a ×̂ b) = ty≤K g≤g' a ×̂ ty≤K g≤g' b
ty≤K g≤g'       (a +̂ b) = ty≤K g≤g' a +̂ ty≤K g≤g' b
ty≤K g≤g'       (a →̂ b) = ty≤K g≤g' a →̂ ty≤K g≤g' b
ty≤K (s≤s g≤g') (μ̂ f)   = μ̂ λ g'≤g'' → f (≤K.trans g≤g' g'≤g'')

tyMaxL : ∀ g' {g Δ} (a : Ty Δ g) → Ty Δ (max g g')
tyMaxL g' a = caseMax (Ty _) (λ g≤g' → ty≤K g≤g' a) (λ g'≤g → a)

tyMaxR : ∀ g {g' Δ} (a : Ty Δ g') → Ty Δ (max g g')
tyMaxR g a = caseMax {g} (Ty _) (λ g≤g' → a) (λ g'≤g → ty≤K g'≤g a)

-- Well-kinded type substitutions

data TySubst (Γ : TyCxt) : (Δ : TyCxt) → Set where
  []  : TySubst Γ []
  _∷_ : ∀{Δ g} (a : Ty Γ g) (τ : TySubst Γ Δ) → TySubst Γ (g ∷ Δ)

-- Looking up an entry in a type substitution

tyVarSubst : ∀{Γ Δ g} → TyVar Δ g → TySubst Γ Δ → Ty Γ g
tyVarSubst (zero g≤g') (a ∷ τ) = ty≤K g≤g' a
tyVarSubst (suc x)     (a ∷ τ) = tyVarSubst x τ

-- Weakening an lifting type substitutions

weakTySubst : ∀{Γ Δ g} (τ : TySubst Γ Δ) → TySubst (g ∷ Γ) Δ
weakTySubst [] = []
weakTySubst (a ∷ τ) = weakTy a ∷ weakTySubst τ

liftTySubst : ∀{Γ Δ g} (τ : TySubst Γ Δ) → TySubst (g ∷ Γ) (g ∷ Δ)
liftTySubst τ = var (zero ≤K.refl) ∷ weakTySubst τ

idTySubst : ∀ Δ → TySubst Δ Δ
idTySubst []      = []
idTySubst (_ ∷ Δ) = liftTySubst (idTySubst Δ)

sgTySubst : ∀{Δ g} (a : Ty Δ g) → TySubst Δ (g ∷ Δ)
sgTySubst a = a ∷ idTySubst _

-- Applying a parallel substitution

tySubst : ∀{Γ Δ g} (τ : TySubst Γ Δ) (a : Ty Δ g) → Ty Γ g
tySubst τ (var x) = tyVarSubst x τ
tySubst τ (▸̂ a) = ▸̂ tySubst τ a
tySubst τ 1̂ = 1̂
tySubst τ (a ×̂ b) = tySubst τ a ×̂ tySubst τ b
tySubst τ (a +̂ b) = tySubst τ a +̂  tySubst τ b
tySubst τ (a →̂ b) = tySubst τ a →̂  tySubst τ b
tySubst τ (μ̂ f) = μ̂ λ g≤g' → tySubst (liftTySubst τ) (f g≤g')

_·′_ : ∀{Δ g g'} → Ty (g' ∷ Δ) g → Ty Δ g' → Ty Δ g
f ·′ a = tySubst (sgTySubst a) f

_·_ : ∀{Δ g} → TyF Δ g → Ty Δ (suc g) → Ty Δ g
f · a = f ≤K.refl ·′ a

-- Closed types

Ty⁰ = Ty []

record Type : Set where
  constructor type_
  field
    {guardedness} : Kind
    theType       : Ty [] guardedness

unit : Type
unit = type_ {0} 1̂

_⇒_ : Type → Type → Type
type_ {g} a ⇒ type b = type (tyMaxL _ a →̂ tyMaxR g b)

_⊗_ : Type → Type → Type
type_ {g} a ⊗ type b = type (tyMaxL _ a ×̂ tyMaxR g b)

_⊕_ : Type → Type → Type
type_ {g} a ⊕ type b = type (tyMaxL _ a +̂ tyMaxR g b)

▸_ : ∀{g} (a : Ty⁰ (suc g)) → Type
▸ a = type ▸̂ a

μ : ∀{g} (f : TyF [] g) → Type
μ f = type μ̂ f

-- Impossible to define!
-- ▸_ : Type → Type
-- ▸ type {g} a = type {{!!}} (▸̂ {!!})
