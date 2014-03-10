{-# OPTIONS --copatterns --sized-types #-}

module Substitution where

open import Library
open import SizedInfiniteTypes
open import Terms

-- * Renaming (weakening and lifting)
------------------------------------------------------------------------

-- Order-preserving embedding for contexts

data _≤_  : (Γ Δ : Cxt) → Set where
  id   : ∀ {Γ} → Γ ≤ Γ
  weak : ∀ {Γ Δ a} → Γ ≤ Δ → (a ∷ Γ) ≤ Δ
  lift : ∀ {Γ Δ a} → Γ ≤ Δ → (a ∷ Γ) ≤ (a ∷ Δ)

-- Smart lift, preserves id.

lift' : ∀{Γ Δ : Cxt}{a : Ty} (η : Γ ≤ Δ) → (a ∷ Γ) ≤ (a ∷ Δ)
lift' id = id
lift' η  = lift η

-- Composition

_•_ : ∀{Γ Δ Δ' : Cxt} (η : Γ ≤ Δ) (η' : Δ ≤ Δ') → Γ ≤ Δ'
id     • η'      = η'
weak η • η'      = weak (η • η')
lift η • id      = lift η
lift η • weak η' = weak (η • η')
lift η • lift η' = lift (η • η')

η•id : ∀{Γ Δ : Cxt} (η : Γ ≤ Δ) → η • id ≡ η
η•id id       = ≡.refl
η•id (weak η) = ≡.cong weak (η•id η)
η•id (lift η) = ≡.refl

lift'-• : ∀{Γ Δ Δ' : Cxt}{a : Ty} (η : Γ ≤ Δ) (η' : Δ ≤ Δ') →
  lift' {a = a} η • lift' η' ≡ lift' (η • η')
lift'-• id       η'        = ≡.refl
lift'-• (weak η) id        = ≡.cong lift (≡.cong weak (≡.sym (η•id η)))
lift'-• (weak η) (weak η') = ≡.refl
lift'-• (weak η) (lift η') = ≡.refl
lift'-• (lift η) id        = ≡.refl
lift'-• (lift η) (weak η') = ≡.refl
lift'-• (lift η) (lift η') = ≡.refl

-- Monotonicity / map for variables

var≤ : ∀{Γ Δ : Cxt}{a : Ty} (η : Γ ≤ Δ) (x : Var Δ a) → Var Γ a
var≤ id        x      = x
var≤ (weak η)  x      = suc (var≤ η x)
var≤ (lift η)  zero   = zero
var≤ (lift η) (suc x) = suc (var≤ η x)

-- First functor law.

var≤-id : ∀{Γ : Cxt}{a : Ty} (x : Var Γ a) → var≤ id x ≡ x
var≤-id x = ≡.refl

-- Second functor law.

var≤-• : ∀{Γ₁ Γ₂ Γ₃ : Cxt}{a : Ty} (η : Γ₁ ≤ Γ₂) (η' : Γ₂ ≤ Γ₃) (x : Var Γ₃ a) →
  var≤ η (var≤ η' x) ≡ var≤ (η • η') x
var≤-• id       η'        x       = ≡.refl
var≤-• (weak η) η'        x       = ≡.cong suc (var≤-• η η' x)
var≤-• (lift η) id        x       = ≡.refl
var≤-• (lift η) (weak η') x       = ≡.cong suc (var≤-• η η' x)
var≤-• (lift η) (lift η') zero    = ≡.refl
var≤-• (lift η) (lift η') (suc x) = ≡.cong suc (var≤-• η η' x)


-- Renaming

rename : ∀ {Γ Δ : Cxt} {a : Ty} (η : Γ ≤ Δ) (x : Tm Δ a) → Tm Γ a
rename η (var x)      = var (var≤ η x)
rename η (abs t)      = abs (rename (lift η) t)
rename η (app t₁ t₂)  = app (rename η t₁) (rename η t₂)
rename η (pair t₁ t₂) = pair (rename η t₁) (rename η t₂)
rename η (fst t)      = fst (rename η t)
rename η (snd t)      = snd (rename η t)
rename η (▹ t)        = ▹ rename η t
rename η (t₁ ∗ t₂)    = rename η t₁ ∗ rename η t₂
rename η (cast eq t)  = cast eq (rename η t)


-- Parallel substitution
Subst : Cxt → Cxt → Set
Subst Γ Δ = ∀ {a : Ty} → Var Γ a → Tm Δ a

-- Identity substitution

ids : ∀ {Γ} → Subst Γ Γ
ids = var

-- Substitution for 0th variable

sgs : ∀ {Γ a} → Tm Γ a → Subst (a ∷ Γ) Γ
sgs t zero    = t
sgs t (suc x) = var x

-- Lifiting a substitution

lifts : ∀ {Γ Δ a} → Subst Γ Δ → Subst (a ∷ Γ) (a ∷ Δ)
lifts σ zero    = var zero
lifts σ (suc x) = rename (weak id) (σ x)

-- Performing a substitution

subst : ∀ {Γ Δ τ} → Subst Γ Δ → Tm Γ τ → Tm Δ τ
subst σ (var x)     = σ x
subst σ (abs t)     = abs (subst (lifts σ) t)
subst σ (app t u)   = app (subst σ t) (subst σ u)
subst σ (▹ t)       = ▹ (subst σ t)
subst σ (t ∗ u)     = (subst σ t) ∗ (subst σ u)
subst σ (pair t u)  = pair (subst σ t) (subst σ u)
subst σ (fst t)     = fst (subst σ t)
subst σ (snd t)     = snd (subst σ t)
subst σ (cast eq t) = cast eq (subst σ t)

-- Substituting for the 0th variable [u/0]t

subst0 : ∀ {Γ a b} → Tm Γ a → Tm (a ∷ Γ) b → Tm Γ b
subst0 u = subst (sgs u)

-- Composition

_•s_ : ∀ {Γ₀ Γ₁ Γ₂} → Subst Γ₁ Γ₂ → Subst Γ₀ Γ₁ → Subst Γ₀ Γ₂
σ •s ρ = λ x → subst σ (ρ x)
