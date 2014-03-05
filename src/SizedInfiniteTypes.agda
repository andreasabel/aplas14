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

  -- `applicative'
  _∗_  : ∀{a : Ty}{b∞} (t : Tm Γ (▸̂ (delay a ⇒ b∞)))
                       (u : Tm Γ (▸ a))                → Tm Γ (▸̂ b∞)

  cast : ∀{a b}        (eq : a ≅ b)  (t : Tm Γ a)      → Tm Γ b

-- A more flexible version of _∗_

▹app : ∀{Γ c∞ b∞}{a : Ty} (eq : c∞ ∞≅ (delay a ⇒ b∞))
                          (t : Tm Γ (▸̂ c∞)) (u : Tm Γ (▸ a)) → Tm Γ (▸̂ b∞)
▹app eq t u = cast (▸̂ eq) t ∗ u

_∗'_  : ∀{Γ a∞ b∞} (t : Tm Γ (▸̂ (a∞ ⇒ b∞))) (u : Tm Γ (▸̂ a∞)) → Tm Γ (▸̂ b∞)
_∗'_ {a∞ = a∞} t u = _∗_ {a = force a∞} (cast (▸̂ (≅delay ≅refl)) t) (cast ((▸̂ (≅delay ≅refl))) u)

_<$>_ : ∀{Γ}{a : Ty}{b∞} (t : Tm Γ (a →̂ force b∞)) (u : Tm Γ (▸ a)) → Tm Γ (▸̂ b∞)
t <$> u = ▹ t ∗ u

_∶_ : ∀ {Γ} a -> Tm Γ a -> Tm Γ a
a ∶ t = t

-- * Examples
------------------------------------------------------------------------

-- Example: fixed-point combinator

Fix_ : Ty → ∞Ty
force Fix A = ▸̂ Fix A →̂ A

omega : ∀{Γ A} → Tm Γ (▸̂ Fix A) → Tm Γ (▸ A)
omega x = ▹app (≅delay ≅refl) x (▹ x)

Y : ∀{Γ A} → Tm Γ ((▸ A →̂ A) →̂ A)
Y = abs (app L (▹ L))
  where
    f = var (suc zero)
    x = var zero
    L = abs (app f (omega x))

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

-- zipWith f s t = cons (f (head s) (head t)) (zipWith f (tail s) (tail t))
-- zipWith = λ f → Y λ zipWith → λ s t →
--   (f (head s) (head t) , zipWith <*> tail s <*> tail t)

zipWith : ∀{Γ A B C} → Tm Γ ((A →̂ (B →̂ C)) →̂ (Stream A →̂ (Stream B →̂ Stream C)))
zipWith = abs (app Y (abs (abs (abs
  (let f   = var (suc (suc (suc zero)))
       zw  = var (suc (suc zero))
       s   = var (suc zero)
       t   = var zero
   in pair (app (app f (head s)) (head t))
           (▹app {c∞ = Stream∞ _ ⇒ Stream∞ _} (≅delay ≅refl)
                 (▹app (≅delay ≅refl) zw (tail s))
                 (tail t)))))))

-- Fibonacci stream

module Fib (N : Ty) (n0 n1 : ∀{Γ} → Tm Γ N) (plus : ∀{Γ} → Tm Γ (N →̂ (N →̂  N))) where

  -- fib = Y λ fib → cons n0 (▹ (cons n1
  --   (zipWith plus <$> fib <*> (tail <$> fib)))) -- Ill-typed!
  --
  -- fib = Y λ fib → cons n0 (cons n1 <$>
  --   ((λ s → (zipWith plus <$> fib) <*> s) <$> (tail <$> fib)))

  fib : ∀{Γ} → Tm Γ (Stream N)
  fib {Γ} = app Y (abs
    (let fib  : Tm (_ ∷ Γ) (▸ Stream N)
         fib  = var zero
         fib₁  : Tm (_ ∷ _ ∷ Γ) (▸ Stream N)
         fib₁  = var (suc zero)
         adds : Tm (_ ∷ _ ∷ Γ) (Stream N →̂ (Stream N →̂ Stream N))
         adds = app zipWith plus
         addf :  Tm (_ ∷ _ ∷ Γ) (▸ (Stream N →̂ Stream N))
         addf = adds <$> fib₁
         tf   : Tm (_ ∷ Γ) (▸ ▸ Stream N)
         tf   = abs (tail (var zero)) <$> fib
         aftf : Tm (_ ∷ Γ) (▸ ▸ Stream N)
         aftf = abs (▹app (≅delay ≅refl) addf (var zero)) <$> tf
     in  cons n0 (abs (cons n1 (var zero)) <$> aftf)))

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



-- Evaluation Contexts

data Ehole {Γ : Cxt} : {a b : Ty} → (Tm Γ a → Tm Γ b) → Set where
  appl  : ∀ {a b} (u : Tm Γ a)  → Ehole (λ (t : Tm Γ (a →̂ b)) → app t u)
  fst   : ∀ {a b} → Ehole {a = a ×̂ b} fst
  snd   : ∀ {a b} → Ehole {a = a ×̂ b} snd
  _∗l   : ∀ {a b∞} (u : Tm Γ (▸ a)) → Ehole {a = (▸̂ (delay a ⇒ b∞))} (λ t → t ∗ u)
  ∗r_   : ∀ {a : Ty}{b∞} (t : Tm Γ (a →̂ force b∞)) → Ehole (λ u → ▸̂ b∞ ∶ ((▹ t) ∗ (▸ a ∶ u)))


mutual

-- Strongly normalizing evaluation contexts

  data SNhole (n : ℕ) {Γ : Cxt} : {a b : Ty} → (Tm Γ a → Tm Γ b) → Set where
    appl  : ∀ {a b u} → SN n u     → SNhole n (λ t → b ∶ app t (a ∶ u))
    fst   : ∀ {a b}                → SNhole n (fst {a = a} {b = b})
    snd   : ∀ {a b}                → SNhole n (snd {a = a} {b = b})
    _∗l   : ∀ {a b∞ u} → SN n u    → SNhole n (λ t → _∗_ {a = a} {b∞} t u)
    ∗r_   : ∀ {a : Ty}{b∞ t} → SN n (▹_ {a∞ = delay (a →̂ force b∞)} t) 
                                   → SNhole n (λ u → _<$>_ {a = a} {b∞} t u)

  data SNe (n : ℕ) {Γ} {b} : Tm Γ b → Set where
    var  : ∀ x                    → SNe n (var x)
    elim : ∀ {a} {t : Tm Γ a} {E} 
           → SNe n t → SNhole n E → SNe n (E t)

  -- Strongly normalizing

  data SN {Γ} : ℕ → ∀ {a} → Tm Γ a → Set where
    ne   : ∀{a n t}     → SNe n t            → SN n {a} t
    abs  : ∀{a b n t}   → SN {a ∷ Γ} n {b} t → SN n (abs t)
    pair : ∀{a b n t u} → SN n t → SN n u    → SN n {a ×̂ b} (pair t u)
    ▹0_  : ∀{a}   {t : Tm Γ (force a)}          → SN 0       {▸̂ a} (▹ t)
    ▹_   : ∀{a n} {t : Tm Γ (force a)} → SN n t → SN (suc n) {▸̂ a} (▹ t)
    exp  : ∀{a n t t'} → t ⟨ n ⟩⇒ t'  → SN n t' → SN n {a} t

  -- Strong head reduction

  data _⟨_⟩⇒_ {Γ} : ∀ {a} → Tm Γ a → ℕ → Tm Γ a → Set where
    β     : ∀{n a b t u} → SN n (a ∶ u)  →   (b ∶ app (abs t) u)     ⟨ n ⟩⇒ subst0 u t
    β▹    : ∀{n a b t}{u : Tm _ (force a)} → ((▸̂ b) ∶ (t <$> (▹ u))) ⟨ n ⟩⇒ ▹ (app t u)
    βfst  : ∀{n a b t u} → SN n u       → fst (pair (a ∶ t) (b ∶ u)) ⟨ n ⟩⇒ t
    βsnd  : ∀{n a b t u} → SN n t       → snd (pair (a ∶ t) (b ∶ u)) ⟨ n ⟩⇒ u
    cong  : ∀{n a b}{E} → Ehole {Γ} {a} {b} E → 
            ∀{t t'} → t ⟨ n ⟩⇒ t' →                              E t ⟨ n ⟩⇒ E t'

mutual
  mapSNe : ∀ {m n} → m ≤ℕ n → ∀ {Γ a}{t : Tm Γ a} → SNe n t -> SNe m t
  mapSNe m≤n (var x) = var x
  mapSNe m≤n (elim t∈Ne E∈SNh) = elim (mapSNe m≤n t∈Ne) (mapSNh m≤n E∈SNh)
  
  mapSN : ∀ {m n} → m ≤ℕ n → ∀ {Γ a}{t : Tm Γ a} → SN n t -> SN m t
  mapSN m≤n (ne u∈SNe) = ne (mapSNe m≤n u∈SNe)
  mapSN m≤n (abs t∈SN) = abs (mapSN m≤n t∈SN)
  mapSN m≤n (pair t∈SN u∈SN) = pair (mapSN m≤n t∈SN) (mapSN m≤n u∈SN)
  mapSN z≤n ▹0_ = ▹0_
  mapSN z≤n (▹ t∈SN) = ▹0_
  mapSN (s≤s m≤n) (▹ t∈SN) = ▹ mapSN m≤n t∈SN
  mapSN m≤n (exp t→t' t∈SN) = exp (map⇒ m≤n t→t') (mapSN m≤n t∈SN)

  map⇒ : ∀ {m n} → m ≤ℕ n → ∀ {Γ a}{t t' : Tm Γ a} → t ⟨ n ⟩⇒ t' → t ⟨ m ⟩⇒ t'
  map⇒ m≤n (β t∈SN) = β (mapSN m≤n t∈SN)
  map⇒ m≤n (β▹ {a = a}) = β▹ {a = a}
  map⇒ m≤n (βfst t∈SN) = βfst (mapSN m≤n t∈SN)
  map⇒ m≤n (βsnd t∈SN) = βsnd (mapSN m≤n t∈SN)
  map⇒ m≤n (cong Eh t→t') = cong Eh (map⇒ m≤n t→t')

  mapSNh : ∀ {m n} → m ≤ℕ n → ∀ {Γ a b}{E : Tm Γ a → Tm Γ b} → SNhole n E -> SNhole m E
  mapSNh m≤n (appl u∈SN) = appl (mapSN m≤n u∈SN)
  mapSNh m≤n fst = fst
  mapSNh m≤n snd = snd
  mapSNh m≤n (u∈SN ∗l) = mapSN m≤n u∈SN ∗l
  mapSNh m≤n (∗r t∈SN) = ∗r mapSN m≤n t∈SN

 
mutual
  substEh' : ∀ {Γ Δ a b} → (σ : Subst Γ Δ) → ∀ {E : Tm Γ a → Tm Γ b} → Ehole E → Tm Δ a → Tm Δ b
  substEh' σ (appl u) t = _
  substEh' σ fst t      = _
  substEh' σ snd t      = _
  substEh' σ (u ∗l) t   = _
  substEh' σ (∗r t) u   = _

  substEh : ∀ {Γ Δ a b} → (σ : Subst Γ Δ) → ∀ {E : Tm Γ a → Tm Γ b} → (Eh : Ehole E) → Ehole (substEh' σ Eh)
  substEh σ (appl u) = appl (subst σ u)
  substEh σ fst      = fst
  substEh σ snd      = snd
  substEh σ (u ∗l)   = subst σ u ∗l
  substEh σ (∗r t)   = ∗r subst σ t


SubstSNe : ℕ → Cxt → Cxt → Set
SubstSNe n Γ Δ = Σ (Subst Γ Δ) λ σ → ∀ {a} (x : Var Γ a) -> SNe n (σ x)

mapSubSNe : ∀ {Γ Δ m n} → m ≤ℕ n → SubstSNe n Γ Δ → SubstSNe m Γ Δ
mapSubSNe m≤n (σ , σ∈SNe) = σ , (λ x → mapSNe m≤n (σ∈SNe x))

sgs-varSNe : ∀ {n Γ a} → Var Γ a → SubstSNe n (a ∷ Γ) Γ 
proj₁ (sgs-varSNe x) = sgs (var x)
proj₂ (sgs-varSNe x) zero    = var x
proj₂ (sgs-varSNe x) (suc y) = var y  

liftsSNe : ∀ {n Γ Δ a} → SubstSNe n Γ Δ → SubstSNe n (a ∷ Γ) (a ∷ Δ) 
proj₁ (liftsSNe σ) = lifts (proj₁ σ)
proj₂ (liftsSNe (σ , σ∈SNe)) zero    = var zero
proj₂ (liftsSNe (σ , σ∈SNe)) (suc y) = {!!}
 

mutual
  substSNh' : ∀ {Γ Δ a b n} → (σ : SubstSNe n Γ Δ) → ∀ {E : Tm Γ a → Tm Γ b} → SNhole n E → Tm Δ a → Tm Δ b
  substSNh' σ (appl u) t = _
  substSNh' σ fst t      = _
  substSNh' σ snd t      = _
  substSNh' σ (u ∗l) t   = _
  substSNh' σ (∗r t) u   = _

  substSNh : ∀ {Γ Δ a b n} → (σ : SubstSNe n Γ Δ) → ∀ {E : Tm Γ a → Tm Γ b} → (SNh : SNhole n E) → SNhole n (substSNh' σ SNh)
  substSNh σ (appl u) = appl (substSN σ u)
  substSNh σ fst      = fst
  substSNh σ snd      = snd
  substSNh σ (u ∗l)   = substSN σ u ∗l
  substSNh σ (∗r t)   = ∗r substSN σ t

  substSNh'-subst : ∀ {Γ Δ a b n} → (σ : SubstSNe n Γ Δ) → ∀ {E : Tm Γ a → Tm Γ b} → (SNh : SNhole n E) → (t : Tm Γ a) 
                    → substSNh' σ SNh (subst (proj₁ σ) t) ≡ subst (proj₁ σ) (E t)
  substSNh'-subst σ (appl u) t = ≡.refl
  substSNh'-subst σ fst      t = ≡.refl
  substSNh'-subst σ snd      t = ≡.refl
  substSNh'-subst σ (u ∗l)   t = ≡.refl
  substSNh'-subst σ (∗r t)   u = ≡.refl

  subst⇒ : ∀ {Γ Δ a n} (σ : SubstSNe n Γ Δ) {t t' : Tm Γ a} → t ⟨ n ⟩⇒ t' → subst (proj₁ σ) t ⟨ n ⟩⇒ subst (proj₁ σ) t'
  subst⇒ {n = n} (σ , σ∈Ne) (β {t = t} {u = u} x) = ≡.subst (λ t' → app (abs (subst (lifts σ) t)) (subst σ u) ⟨ n ⟩⇒ t') 
                                                   {!!} 
                                                   (β {t = subst (lifts σ) t} (substSN (σ , σ∈Ne) x))
  subst⇒         σ (β▹ {a = a})          = β▹ {a = a}
  subst⇒         σ (βfst t∈SN)           = βfst (substSN σ t∈SN)
  subst⇒         σ (βsnd u∈SN)           = βsnd (substSN σ u∈SN)
  subst⇒ {n = n} σ (cong E∈Eh t→t')      = ≡.subst₂ (λ t t' → t ⟨ n ⟩⇒ t') {!!} {!!} (cong (substEh (proj₁ σ) E∈Eh) (subst⇒ σ t→t'))
  
  substSNe : ∀ {Γ Δ τ n} → (σ : SubstSNe n Γ Δ) → ∀ {t : Tm Γ τ} → SNe n t → SNe n (subst (proj₁ σ) t)
  substSNe σ (var x)            = proj₂ σ x
  substSNe σ (elim t∈SNe E∈SNh) = ≡.subst (SNe _) (substSNh'-subst σ E∈SNh _) (elim (substSNe σ t∈SNe) (substSNh σ E∈SNh))

  substSN : ∀ {Γ Δ τ n} → (σ : SubstSNe n Γ Δ) → ∀ {t : Tm Γ τ} → SN n t → SN n (subst (proj₁ σ) t)
  substSN σ (ne t∈SNe)         = ne (substSNe σ t∈SNe)
  substSN σ (abs t∈SN)         = abs (substSN (liftsSNe σ) t∈SN)
  substSN σ (pair t₁∈SN t₂∈SN) = pair (substSN σ t₁∈SN) (substSN σ t₂∈SN)
  substSN σ ▹0_                = ▹0_
  substSN σ (▹ t∈SN)           = ▹ substSN (mapSubSNe n≤sn σ) t∈SN
  substSN σ (exp t→t' t'∈SN)   = exp (subst⇒ σ t→t') (substSN σ t'∈SN)


varSN : ∀{Γ a n x} → var x ∈ SN {Γ} n {a}
varSN = ne (var _)

appVarSN : ∀{Γ a b n}{t : Tm Γ (a →̂ b)}{x} → t ∈ SN n → app t (var x) ∈ SN n
appVarSN (ne t∈SNe)       = ne (elim t∈SNe (appl varSN))
appVarSN (abs t∈SN)       = exp (β varSN) (substSN (sgs-varSNe _) t∈SN)
appVarSN (exp t→t' t'∈SN) = exp (cong (appl (var _)) t→t') (appVarSN t'∈SN)
