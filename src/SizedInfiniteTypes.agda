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
open _∞≅_

mutual
  ≅refl  : ∀{a} → a ≅ a
  ≅refl {a ×̂ b} = (≅refl {a}) ×̂ (≅refl {b})
  ≅refl {a →̂ b} = (≅refl {a}) →̂ (≅refl {b})
  ≅refl {▸̂ a∞ } = ▸̂ (≅refl∞ {a∞})

  ≅refl∞ : ∀{a∞} → a∞ ∞≅ a∞
  ≅force ≅refl∞ = ≅refl


-- * Terms
------------------------------------------------------------------------

-- Typing contexts

Cxt = List Ty

-- Variables

data Var : (Γ : Cxt) (a : Ty) → Set where
  zero : ∀{Γ a}             → Var (a ∷ Γ) a
  suc  : ∀{Γ a b} → Var Γ a → Var (b ∷ Γ) a


-- Well-typed terms

data Tm (Γ : Cxt) : (a : Ty) → Set where
  var  : ∀{a}          (x : Var Γ a)                   → Tm Γ a
  abs  : ∀{a b}        (t : Tm (a ∷ Γ) b)              → Tm Γ (a →̂ b)
  app  : ∀{a b}        (t : Tm Γ (a →̂ b)) (u : Tm Γ a) → Tm Γ b
  pair : ∀{a b}        (t : Tm Γ a) (u : Tm Γ b)       → Tm Γ (a ×̂ b)
  fst  : ∀{a b}        (t : Tm Γ (a ×̂ b))              → Tm Γ a
  snd  : ∀{a b}        (t : Tm Γ (a ×̂ b))              → Tm Γ b
  ▹_   : ∀{a∞}         (t : Tm Γ (force a∞))           → Tm Γ (▸̂ a∞)

  _∗_  : ∀{a : Ty}{b∞} (t : Tm Γ (▸̂ (delay a ⇒ b∞)))
                       (u : Tm Γ (▸ a))                → Tm Γ (▸̂ b∞)

  cast : ∀{a b}        (eq : a ≅ b)  (t : Tm Γ a)      → Tm Γ b

-- A more flexible version of _∗_

▹app : ∀{Γ c∞ b∞}{a : Ty} (eq : c∞ ∞≅ (delay a ⇒ b∞))
                          (t : Tm Γ (▸̂ c∞)) (u : Tm Γ (▸ a)) → Tm Γ (▸̂ b∞)
▹app eq t u = cast (▸̂ eq) t ∗ u

-- * Examples
------------------------------------------------------------------------

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

-- Y' : ∀{Γ}{a∞ : ∞Ty {∞}} → Tm Γ ((▸̂ a∞ →̂ force a∞) →̂ force a∞)
-- Y' = abs {!(app L {!(▹ L)!})!}
--   where L = abs (app (var (suc zero)) (omega (var zero)))

-- Example: Streams

mutual
  Stream : Ty → Ty
  Stream A = A ×̂ ▸̂ Stream∞ A

  Stream∞ : Ty → ∞Ty
  force (Stream∞ A) = Stream A

-- Stream constructor

cons : ∀{Γ A} → Tm Γ A → Tm Γ (▸ Stream A) → Tm Γ (Stream A)
cons a s = pair a (cast (▸̂ (≅delay ≅refl)) s)
-- cons a s = cast (≅refl ×̂ (▸̂ (≅delay ≅refl))) (pair a s)

head : ∀{Γ A} → Tm Γ (Stream A) → Tm Γ A
head s = fst s

tail : ∀{Γ A} → Tm Γ (Stream A) → Tm Γ (▸ Stream A)
tail s = cast (▸̂ (≅delay ≅refl)) (snd s)

-- repeat a = (a , ▹ repeat a)
-- repeat = λ a → Y λ f → cons a f

repeat : ∀{Γ A} → Tm Γ (A →̂ Stream A)
repeat = abs (app Y (abs (cons (var (suc zero)) (var zero))))

-- smap f s = cons (f (head s)) (smap f (tail s))
-- smap = λ f → Y λ map → λ s → (f (head s), map <*> tail s)

smap : ∀{Γ A B} → Tm Γ ((A →̂ B) →̂ (Stream A →̂ Stream B))
smap = abs (app Y (abs (abs
  (let f   = var (suc (suc zero))
       map = var (suc zero)
       s   = var zero
   in pair (app f (head s)) (▹app (≅delay ≅refl) map (tail s))))))

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

