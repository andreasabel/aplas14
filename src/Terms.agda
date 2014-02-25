-- Well-typed terms

module Terms where

open import Library
open import Types

-- Terms inhabit closed types of any guardedness level

Cxt = List Type

-- Variables

data Var : (Γ : Cxt) (a : Type) → Set where
  zero : ∀{Γ a}             → Var (a ∷ Γ) a
  suc  : ∀{Γ a b} → Var Γ a → Var (b ∷ Γ) a

-- Well-typed terms

data Tm (Γ : Cxt) : (a : Type) → Set where
  var : ∀{a}   (x : Var Γ a)                      → Tm Γ a
  abs : ∀{a b} (t : Tm (a ∷ Γ) b)                 → Tm Γ (a ⇒ b)
  app : ∀{a b} (t : Tm Γ (a ⇒ b)) (u : Tm Γ a)    → Tm Γ b
  ▹_  : ∀{g}{a : Ty⁰ (suc g)} (t : Tm Γ (type a)) → Tm Γ (▸ a)
  _∗_ : ∀{g}{a b : Ty⁰ (suc g)} (t : Tm Γ (▸ (a →̂ b))) (u : Tm Γ (▸ a)) → Tm Γ (▸ b)
  fold   : ∀{g}{f : TyF [] g} (t : Tm Γ (type (f · μ̂ f))) → Tm Γ (μ f)
  unfold : ∀{g}{f : TyF [] g} (t : Tm Γ (μ f))       → Tm Γ (type (f · μ̂ f))

-- * Renaming (weakening and lifting)
------------------------------------------------------------------------

-- Order-preserving embedding for contexts

data _≤_ : (Γ Δ : Cxt) → Set where
  id   : ∀ {Γ} → Γ ≤ Γ
  weak : ∀ {Γ Δ a} → Γ ≤ Δ → (a ∷ Γ) ≤ Δ
  lift : ∀ {Γ Δ a} → Γ ≤ Δ → (a ∷ Γ) ≤ (a ∷ Δ)

-- Smart lift, preserves id.

lift' : ∀ {Γ Δ a} (η : Γ ≤ Δ) → (a ∷ Γ) ≤ (a ∷ Δ)
lift' id = id
lift' η  = lift η

-- Composition

_•_ : ∀ {Γ Δ Δ'} (η : Γ ≤ Δ) (η' : Δ ≤ Δ') → Γ ≤ Δ'
id     • η'      = η'
weak η • η'      = weak (η • η')
lift η • id      = lift η
lift η • weak η' = weak (η • η')
lift η • lift η' = lift (η • η')

η•id :  ∀ {Γ Δ} (η : Γ ≤ Δ) → η • id ≡ η
η•id id       = refl
η•id (weak η) = cong weak (η•id η)
η•id (lift η) = refl

lift'-• : ∀ {Γ Δ Δ' a} (η : Γ ≤ Δ) (η' : Δ ≤ Δ') →
  lift' {a = a} η • lift' η' ≡ lift' (η • η')
lift'-• id       η'        = refl
lift'-• (weak η) id        = cong lift (cong weak (sym (η•id η)))
lift'-• (weak η) (weak η') = refl
lift'-• (weak η) (lift η') = refl
lift'-• (lift η) id        = refl
lift'-• (lift η) (weak η') = refl
lift'-• (lift η) (lift η') = refl

-- Monotonicity / map for variables

var≤ : ∀ {Γ Δ a} (η : Γ ≤ Δ) (x : Var Δ a) → Var Γ a
var≤ id        x      = x
var≤ (weak η)  x      = suc (var≤ η x)
var≤ (lift η)  zero   = zero
var≤ (lift η) (suc x) = suc (var≤ η x)

-- First functor law.

var≤-id : ∀ {Γ a} (x : Var Γ a) → var≤ id x ≡ x
var≤-id x = refl

-- Second functor law.

var≤-• : ∀ {Γ₁ Γ₂ Γ₃ a} (η : Γ₁ ≤ Γ₂) (η' : Γ₂ ≤ Γ₃) (x : Var Γ₃ a) →
  var≤ η (var≤ η' x) ≡ var≤ (η • η') x
var≤-• id       η'        x       = refl
var≤-• (weak η) η'        x       = cong suc (var≤-• η η' x)
var≤-• (lift η) id        x       = refl
var≤-• (lift η) (weak η') x       = cong suc (var≤-• η η' x)
var≤-• (lift η) (lift η') zero    = refl
var≤-• (lift η) (lift η') (suc x) = cong suc (var≤-• η η' x)

