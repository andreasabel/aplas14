{-# OPTIONS --copatterns --sized-types #-}
module InfiniteTypes where

open import Library

-- Infinite type expression

mutual
  data Ty : Set where
    -- 1̂   : Ty
    -- _×̂_ : ∀ (a b : Ty) → Ty
    -- _+̂_ : ∀ (a b : Ty) → Ty
    _→̂_ : ∀ (a b : Ty) → Ty
    ▸̂_  : ∀ (a∞ : ∞Ty) → Ty

  record ∞Ty : Set where
    coinductive
    constructor delay_
    field       force_ : Ty
open ∞Ty public

▸_ : Ty → Ty
▸ A = ▸̂ delay A

_⇒_ : ∀ (a∞ b∞ : ∞Ty) → ∞Ty
force (a∞ ⇒ b∞) = force a∞ →̂ force b∞

-- Guarded fixpoint types (needs sized types)

{-# NO_TERMINATION_CHECK #-}
μ̂ : (∞Ty → Ty) → ∞Ty
force (μ̂ F) = F (μ̂ F)

-- Type equality

mutual
  data _≅_ : (a b : Ty) → Set where
    _→̂_ : ∀{a a' b b'} (a≅ : a ≅ a') (b≅ : b ≅ b') → (a →̂ b) ≅ (a' →̂ b')
    ▸̂_  : ∀{a∞ b∞}     (a≅ : a∞ ∞≅ b∞)             → ▸̂ a∞    ≅ ▸̂ b∞

  record _∞≅_ (a∞ b∞ : ∞Ty) : Set where
    coinductive
    constructor ≅delay
    field       ≅force : force a∞ ≅ force b∞
open _∞≅_

mutual
  ≅refl  : ∀{a} → a ≅ a
  ≅refl {a →̂ b} = (≅refl {a}) →̂ (≅refl {b})
  ≅refl {▸̂ a∞ } = ▸̂ (≅refl∞ {a∞})

  ≅refl∞ : ∀{a∞} → a∞ ∞≅ a∞
  ≅force ≅refl∞ = ≅refl


-- Typing contexts

Cxt = List Ty

-- Variables

data Var : (Γ : Cxt) (a : Ty) → Set where
  zero : ∀{Γ a}             → Var (a ∷ Γ) a
  suc  : ∀{Γ a b} → Var Γ a → Var (b ∷ Γ) a

-- Well-typed terms

data Tm (Γ : Cxt) : (a : Ty) → Set where
  var  : ∀{a}        (x : Var Γ a)                       → Tm Γ a
  abs  : ∀{a b}      (t : Tm (a ∷ Γ) b)                  → Tm Γ (a →̂ b)
  app  : ∀{a b}      (t : Tm Γ (a →̂ b)) (u : Tm Γ a)     → Tm Γ b
  ▹_   : ∀{a∞}       (t : Tm Γ (force a∞))               → Tm Γ (▸̂ a∞)

  _∗_  : ∀{a b∞}     (t : Tm Γ (▸̂ (delay a ⇒ b∞)))
                     (u : Tm Γ (▸ a))                    → Tm Γ (▸̂ b∞)

  cast : ∀{a b}      (eq : a ≅ b)  (t : Tm Γ a)          → Tm Γ b

-- A more flexible version of _∗_

▹app : ∀{Γ c∞ a b∞} (eq : c∞ ∞≅ (delay a ⇒ b∞))
                    (t : Tm Γ (▸̂ c∞)) (u : Tm Γ (▸ a))  → Tm Γ (▸̂ b∞)
▹app eq t u = cast (▸̂ eq) t ∗ u

-- Example: fixed-point combinator

Fix_ : Ty → ∞Ty
force Fix A = ▸̂ Fix A →̂ A

omega : ∀{Γ A} → Tm Γ (▸̂ Fix A) → Tm Γ (▸ A)
omega x = ▹app (≅delay ≅refl) x (▹ x)

Y : ∀{Γ A} → Tm Γ ((▸ A →̂ A) →̂ A)
Y = abs (app L (▹ L))
  where L = abs (app (var (suc zero)) (omega (var zero)))

-- Alternative definition of omega

Fix∞_ : ∞Ty → ∞Ty
force Fix∞ A = ▸̂ Fix∞ A →̂ force A

omega' : ∀{Γ a∞} → Tm Γ (▸̂ Fix∞ a∞) → Tm Γ (▸̂ a∞)
omega' x = ▹app (≅delay ≅refl) x (▹ x)

