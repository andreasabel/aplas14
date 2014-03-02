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

_⇒_ :  ∀ (a∞ b∞ : ∞Ty) → ∞Ty
force (a∞ ⇒ b∞) = force a∞ →̂ force b∞

-- Guarded fixpoint types (needs sized types)

{-# NO_TERMINATION_CHECK #-}
μ̂ : (∞Ty → Ty) → ∞Ty
force (μ̂ F) = F (μ̂ F)

-- Example

Fix_ : Ty → ∞Ty
force Fix A = ▸̂ Fix A →̂ A

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
  var  : ∀{a}        (x : Var Γ a)                           → Tm Γ a
  abs  : ∀{a b}      (t : Tm (a ∷ Γ) b)                      → Tm Γ (a →̂ b)
  app  : ∀{a b}      (t : Tm Γ (a →̂ b)) (u : Tm Γ a)         → Tm Γ b
  ▹_   : ∀{a∞}       (t : Tm Γ (force a∞))                   → Tm Γ (▸̂ a∞)
  ▹app : ∀{c∞ a∞ b∞} (eq : c∞ ∞≅ (a∞ ⇒ b∞))
                     (t : Tm Γ (▸̂ c∞)) (u : Tm Γ (▸̂ a∞))     → Tm Γ (▸̂ b∞)
  ▹ap  : ∀{c∞ a∞ b∞} (eq : force c∞ ≡ (force a∞ →̂ force b∞))
                     (t : Tm Γ (▸̂ c∞)) (u : Tm Γ (▸̂ a∞))     → Tm Γ (▸̂ b∞)
  _∗_  : ∀{a∞ b∞}    (t : Tm Γ (▸̂ (a∞ ⇒ b∞))) (u : Tm Γ (▸̂ a∞)) → Tm Γ (▸̂ b∞)
  cast : ∀{a b}      (eq : a ≅ b)  (t : Tm Γ a)              → Tm Γ b

module FixDelay where

  -- Example: fixed-point combinator

  omega'' : ∀{Γ A} → Tm Γ (▸̂ Fix A) → Tm Γ (▸̂ delay A)
  omega'' x = ▹ap {a∞ = delay _} ≡.refl x (▹ x)

  omega' : ∀{Γ A} → Tm Γ (▸̂ Fix A) → Tm Γ (▸̂ delay A)
  omega' x = ▹app {a∞ = delay _} (≅delay ≅refl) x (▹ x)

  omega : ∀{Γ A} → Tm Γ (▸̂ Fix A) → Tm Γ (▸̂ delay A)
  omega {A = A} x = _∗_ {a∞ = delay _} (cast (▸̂ (≅delay ≅refl)) x) (▹ x)

  -- omega {A = A} x = _∗_ {a∞ = delay (▸̂ (Fix A))}{b∞ = delay A} (cast (▸̂ (≅delay (≅refl {force (Fix A)}))) x) (▹ x)
  -- omega {A = A} x = (cast (▸̂ (≅delay (≅refl {force (Fix A)}))) x) ∗ (▹ x)
  -- omega x = (cast (▸̂ (≅delay (≅refl {force (Fix _)}))) x) ∗ (▹ x)


  -- Y : ∀{Γ A} → Tm Γ (▸̂ delay A →̂ A) → Tm Γ A
  -- Y f = {!app L!}
  --   where L = abs (app f (omega (var 0)))

  Y : ∀{Γ A} → Tm Γ ((▸̂ delay A →̂ A) →̂ A)
  Y = abs (app L (▹ L))
    where L = abs (app (var (suc zero)) (omega (var zero)))

module FixForce where

  -- Example: fixed-point combinator

  omega'' : ∀{Γ a∞} → Tm Γ (▸̂ Fix force a∞) → Tm Γ (▸̂ a∞)
  omega'' x = ▹ap {a∞ = delay _} ≡.refl x (▹ x)

  omega' : ∀{Γ a∞} → Tm Γ (▸̂ Fix force a∞) → Tm Γ (▸̂ a∞)
  omega' x = ▹app {a∞ = delay _} (≅delay ≅refl) x (▹ x)

  omega : ∀{Γ a∞} → Tm Γ (▸̂ Fix force a∞) → Tm Γ (▸̂ a∞)
  omega {a∞ = a∞} x = _∗_ {a∞ = delay _} (cast (▸̂ (≅delay ≅refl)) x) (▹ x)

  Y : ∀{Γ a∞} → Tm Γ ((▸̂ a∞ →̂ force a∞) →̂ force a∞)
  Y = abs (app L (▹ L))
    where L = abs (app (var (suc zero)) (omega (var zero)))
