-- Well-typed terms

module Terms where

open import Library
open import Types
open import TypeEquality

-- Terms inhabit closed types of a fixed guardedness level

Cxt : Kind → Set
Cxt g = List (Ty⁰ g)

cxt↑ : ∀{g} → Cxt g → Cxt (suc g)
cxt↑ = map ty↑

-- Variables

data Var {g} : (Γ : Cxt g) (a : Ty⁰ g) → Set where
  zero : ∀{Γ : Cxt g}{a}             → Var (a ∷ Γ) a
  suc  : ∀{Γ : Cxt g}{a b} → Var Γ a → Var (b ∷ Γ) a

-- Well-typed terms

data Tm : ∀{g} (Γ : Cxt g) (a : Ty⁰ g) → Set where
  var    : ∀{g}{Γ : Cxt g}{a}                 (x : Var Γ a)                           → Tm Γ a
  abs    : ∀{g}{Γ : Cxt g}{a b}               (t : Tm (a ∷ Γ) b)                      → Tm Γ (a →̂ b)
  app    : ∀{g}{Γ : Cxt g}{a b}               (t : Tm Γ (a →̂ b)) (u : Tm Γ a)         → Tm Γ b
  ▹_     : ∀{g}{Γ : Cxt g}{a   : Ty⁰ (suc g)} (t : Tm (cxt↑ Γ) a)                     → Tm Γ (▸̂ a)
  _∗_    : ∀{g}{Γ : Cxt g}{a b : Ty⁰ (suc g)} (t : Tm Γ (▸̂ (a →̂ b))) (u : Tm Γ (▸̂ a)) → Tm Γ (▸̂ b)
  cast   : ∀{g}{Γ : Cxt g}{a b} (eq : a ≅ b)  (t : Tm Γ a)                            → Tm Γ b
  fold   : ∀{g}{Γ : Cxt g}{f : TyF [] g}      (t : Tm Γ (f · μ̂ f))                    → Tm (cxt↑ Γ) (μ̂ f)
  unfold : ∀{g}{Γ : Cxt g}{f : TyF [] g}      (t : Tm (cxt↑ Γ) (μ̂ f))                 → Tm Γ (f · μ̂ f)

-- * Renaming (weakening and lifting)
------------------------------------------------------------------------

-- Order-preserving embedding for contexts

data _≤_ {g} : (Γ Δ : Cxt g) → Set where
  id   : ∀ {Γ} → Γ ≤ Γ
  weak : ∀ {Γ Δ a} → Γ ≤ Δ → (a ∷ Γ) ≤ Δ
  lift : ∀ {Γ Δ a} → Γ ≤ Δ → (a ∷ Γ) ≤ (a ∷ Δ)

-- Smart lift, preserves id.

lift' : ∀{g}{Γ Δ : Cxt g}{a : Ty⁰ g} (η : Γ ≤ Δ) → (a ∷ Γ) ≤ (a ∷ Δ)
lift' id = id
lift' η  = lift η

-- Composition

_•_ : ∀{g}{Γ Δ Δ' : Cxt g} (η : Γ ≤ Δ) (η' : Δ ≤ Δ') → Γ ≤ Δ'
id     • η'      = η'
weak η • η'      = weak (η • η')
lift η • id      = lift η
lift η • weak η' = weak (η • η')
lift η • lift η' = lift (η • η')

η•id : ∀{g}{Γ Δ : Cxt g} (η : Γ ≤ Δ) → η • id ≡ η
η•id id       = ≡.refl
η•id (weak η) = ≡.cong weak (η•id η)
η•id (lift η) = ≡.refl

lift'-• : ∀{g}{Γ Δ Δ' : Cxt g}{a : Ty⁰ g} (η : Γ ≤ Δ) (η' : Δ ≤ Δ') →
  lift' {a = a} η • lift' η' ≡ lift' (η • η')
lift'-• id       η'        = ≡.refl
lift'-• (weak η) id        = ≡.cong lift (≡.cong weak (≡.sym (η•id η)))
lift'-• (weak η) (weak η') = ≡.refl
lift'-• (weak η) (lift η') = ≡.refl
lift'-• (lift η) id        = ≡.refl
lift'-• (lift η) (weak η') = ≡.refl
lift'-• (lift η) (lift η') = ≡.refl

-- Monotonicity / map for variables

var≤ : ∀{g}{Γ Δ : Cxt g}{a : Ty⁰ g} (η : Γ ≤ Δ) (x : Var Δ a) → Var Γ a
var≤ id        x      = x
var≤ (weak η)  x      = suc (var≤ η x)
var≤ (lift η)  zero   = zero
var≤ (lift η) (suc x) = suc (var≤ η x)

-- First functor law.

var≤-id : ∀{g}{Γ : Cxt g}{a : Ty⁰ g} (x : Var Γ a) → var≤ id x ≡ x
var≤-id x = ≡.refl

-- Second functor law.

var≤-• : ∀{g}{Γ₁ Γ₂ Γ₃ : Cxt g}{a : Ty⁰ g} (η : Γ₁ ≤ Γ₂) (η' : Γ₂ ≤ Γ₃) (x : Var Γ₃ a) →
  var≤ η (var≤ η' x) ≡ var≤ (η • η') x
var≤-• id       η'        x       = ≡.refl
var≤-• (weak η) η'        x       = ≡.cong suc (var≤-• η η' x)
var≤-• (lift η) id        x       = ≡.refl
var≤-• (lift η) (weak η') x       = ≡.cong suc (var≤-• η η' x)
var≤-• (lift η) (lift η') zero    = ≡.refl
var≤-• (lift η) (lift η') (suc x) = ≡.cong suc (var≤-• η η' x)

