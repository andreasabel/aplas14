{-# OPTIONS --copatterns --sized-types #-}

module SizedInfiniteTypes where

open import Library

-- * Types
------------------------------------------------------------------------

-- Infinite type expressions

mutual
  data Ty {i : Size} : Set where
    -- 1̂   : Ty {i}
    -- _+̂_ : ∀ (a b : Ty {i}) → Ty {i}
    _×̂_ : ∀ (a b : Ty {i}) → Ty {i}
    _→̂_ : ∀ (a b : Ty {i}) → Ty {i}
    ▸̂_  : ∀ (a∞ : ∞Ty {i}) → Ty {i}

  record ∞Ty {i : Size} : Set where
    coinductive
    constructor delay_
    field       force_ : ∀{j : Size< i} → Ty {j}
open ∞Ty public

▸_ : ∀{i} → Ty {i} → Ty {↑ i}
▸ A = ▸̂ delay A

_⇒_ : ∀{i} (a∞ b∞ : ∞Ty {i}) → ∞Ty {i}
force (a∞ ⇒ b∞) = force a∞ →̂ force b∞

-- Guarded fixpoint types (needs sized types)

μ̂ : ∀{i} → (∀{j : Size< i} → ∞Ty {j} → Ty {j}) → ∞Ty {i}
force (μ̂ F) = F (μ̂ F)

-- Type equality

mutual
  data _≅_ : (a b : Ty) → Set where
    _×̂_ : ∀{a a' b b'} (a≅ : a ≅ a') (b≅ : b ≅ b') → (a ×̂ b) ≅ (a' ×̂ b')
    _→̂_ : ∀{a a' b b'} (a≅ : a ≅ a') (b≅ : b ≅ b') → (a →̂ b) ≅ (a' →̂ b')
    ▸̂_  : ∀{a∞ b∞}     (a≅ : a∞ ∞≅ b∞)             → ▸̂ a∞    ≅ ▸̂ b∞

  record _∞≅_ (a∞ b∞ : ∞Ty) : Set where
    coinductive
    constructor ≅delay
    field       ≅force : force a∞ ≅ force b∞
open _∞≅_ public

mutual
  ≅refl  : ∀{a} → a ≅ a
  ≅refl {a ×̂ b} = (≅refl {a}) ×̂ (≅refl {b})
  ≅refl {a →̂ b} = (≅refl {a}) →̂ (≅refl {b})
  ≅refl {▸̂ a∞ } = ▸̂ (≅refl∞ {a∞})

  ≅refl∞ : ∀{a∞} → a∞ ∞≅ a∞
  ≅force ≅refl∞ = ≅refl

mutual
  ≅sym : ∀ {a b} → a ≅ b → b ≅ a
  ≅sym (eq ×̂ eq₁) = (≅sym eq) ×̂ (≅sym eq₁)
  ≅sym (eq →̂ eq₁) = (≅sym eq) →̂ (≅sym eq₁)
  ≅sym (▸̂ a≅) = ▸̂  (≅sym∞ a≅)

  ≅sym∞ : ∀{a∞ b∞} → a∞ ∞≅ b∞ → b∞ ∞≅ a∞
  ≅force (≅sym∞ eq) = ≅sym (≅force eq)
