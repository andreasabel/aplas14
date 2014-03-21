{-# OPTIONS --copatterns --sized-types #-}

module Terms where

open import Library
open import SizedInfiniteTypes

-- * Terms
------------------------------------------------------------------------

-- Typing contexts

Cxt = List Ty

-- Variables

data Var : (Γ : Cxt) (a : Ty) → Set where
  zero : ∀{Γ a b}  (eq : a ≅ b) → Var (a ∷ Γ) b
  suc  : ∀{Γ a b} (x : Var Γ a) → Var (b ∷ Γ) a

data _≅V_ : {Γ : Cxt} {Γ' : Cxt} {a : Ty} {a' : Ty} → Var Γ a → Var Γ' a' → Set where
  zero : ∀ {Γ}{a b} {eq : a ≅ b} {Γ' a' b'} {eq' : a' ≅ b'} → (zero {Γ = Γ} eq) ≅V (zero {Γ = Γ'} eq')
  suc  : ∀ {Γ a b} {x : Var Γ a} {Γ' a' b'} {x' : Var Γ' a'} → x ≅V x' → suc {b = b} x ≅V suc {b = b'} x'

v₀ : ∀ {a Γ} → Var (a ∷ Γ) a
v₀ = zero ≅refl

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


data _≅T_ {Γ Γ' : Cxt} : {a a' : Ty} → Tm Γ a → Tm Γ' a' → Set where
  var  : ∀{a a'} {x : Var Γ a}{x' : Var Γ' a'} → ([x] : x ≅V x') → var x ≅T var x'
  abs  : ∀{a b a' b'} {t : Tm (a ∷ Γ) b}{t' : Tm (a' ∷ Γ') b'} → ([t] : t ≅T t') → abs t ≅T abs t'
  app  : ∀{a b a' b'} {t : Tm Γ (a →̂ b)}{t' : Tm Γ' (a' →̂ b')} → t ≅T t' → {u : Tm Γ a} {u' : Tm Γ' a'} → u ≅T u' → app t u ≅T app t' u'
  pair : ∀{a b a' b'} {t : Tm Γ a} {t' : Tm Γ' a'} → t ≅T t' → {u : Tm Γ b}{u' : Tm Γ' b'} → u ≅T u' → pair t u ≅T pair t' u'
  fst  : ∀{a b a' b'} {t : Tm Γ (a ×̂ b)} {t' : Tm Γ' (a' ×̂ b')} → t ≅T t' → fst t ≅T fst t'
  snd  : ∀{a b a' b'} {t : Tm Γ (a ×̂ b)} {t' : Tm Γ' (a' ×̂ b')} → t ≅T t' → snd t ≅T snd t'
  ▹_   : ∀{a∞ a∞'} {t : Tm Γ (force a∞)} {t' : Tm Γ' (force a∞')} → t ≅T t' → ▹_ {a∞ = a∞} t ≅T ▹_ {a∞ = a∞'} t'

  -- `applicative'
  _∗_  : ∀{a : Ty}{b∞}{a' : Ty}{b∞'} {t : Tm Γ (▸̂ (delay a ⇒ b∞))}{t' : Tm Γ' (▸̂ (delay a' ⇒ b∞'))}
         → t ≅T t' → {u : Tm Γ (▸ a)} {u' : Tm Γ' (▸ a')}  → u ≅T u' → (t ∗ u) ≅T (t' ∗ u')

Vsym : ∀ {Γ Γ' : Cxt} {a a' : Ty} → {t : Var Γ a} → {t' : Var Γ' a'} → t ≅V t' → t' ≅V t
Vsym zero = zero
Vsym (suc v) = suc (Vsym v)

Tsym : ∀ {Γ Γ' : Cxt} {a a' : Ty} → {t : Tm Γ a} → {t' : Tm Γ' a'} → t ≅T t' → t' ≅T t
Tsym (var [x]) = var (Vsym [x])
Tsym (abs t)     = abs (Tsym t)
Tsym (app t u)   = app (Tsym t) (Tsym u)
Tsym (▹ t)       = ▹ (Tsym t)
Tsym (t ∗ u)     = (Tsym t) ∗ (Tsym u)
Tsym (pair t u)  = pair (Tsym t) (Tsym u)
Tsym (fst t)     = fst (Tsym t)
Tsym (snd t)     = snd (Tsym t)

_≅C_ : Cxt → Cxt → Set
_≅C_ = ≅L _≅_

castVar : ∀{Γ Δ a b} → (eqC : Γ ≅C Δ) (eq : a ≅ b)  (t : Var Γ a) → Var Δ b
castVar (x∼y ∷ eqC) eq (zero eq₁) = zero TODO
castVar (x∼y ∷ eqC) eq (suc x₁) = suc (castVar eqC eq x₁)

castC : ∀{Γ Δ a b} (eqC : Γ ≅C Δ) (eq : a ≅ b)  (t : Tm Γ a)      → Tm Δ b
castC eqC eq         (var x)     = var (castVar eqC eq x)
castC eqC (eq →̂ eq₁) (abs t)     = abs (castC (eq ∷ eqC) eq₁ t)
castC eqC eq         (app t t₁)  = app (castC eqC (≅refl →̂ eq) t) (castC eqC ≅refl t₁)
castC eqC (eq ×̂ eq₁) (pair t t₁) = pair (castC eqC eq t) (castC eqC eq₁ t₁)
castC eqC eq         (fst t)     = fst (castC eqC (eq ×̂ ≅refl) t)
castC eqC eq         (snd t)     = snd (castC eqC (≅refl ×̂ eq) t)
castC eqC (▸̂ a≅)     (▹ t)       = ▹ (castC eqC (≅force a≅) t)
castC eqC (▸̂ a≅)     (t ∗ t₁)    = (castC eqC (▸̂ (≅delay (≅refl →̂ (≅force a≅)))) t) ∗ (castC eqC ≅refl t₁)

cast : ∀{Γ a b} (eq : a ≅ b) (t : Tm Γ a) → Tm Γ b
cast = castC (≅L.refl ≅refl)

coehV : ∀{Γ Δ a b} (eqC : Γ ≅C Δ) (eq : a ≅ b) (x : Var Γ a) → castVar eqC eq x ≅V x
coehV (x∼y ∷ eqC) eq (zero eq₁) = zero
coehV (x∼y ∷ eqC) eq (suc x₁)   = suc (coehV eqC eq x₁)
 
coeh : ∀{Γ Δ a b} (eqC : Γ ≅C Δ) (eq : a ≅ b) (t : Tm Γ a) → castC eqC eq t ≅T t
coeh eqC eq         (var x)     = var (coehV eqC eq x)
coeh eqC (eq →̂ eq₁) (abs t)     = abs (coeh (eq ∷ eqC) eq₁ t)
coeh eqC eq         (app t t₁)  = app (coeh eqC (≅refl →̂ eq) t) (coeh eqC ≅refl t₁)
coeh eqC (eq ×̂ eq₁) (pair t t₁) = pair (coeh eqC eq t) (coeh eqC eq₁ t₁)
coeh eqC eq         (fst t)     = fst (coeh eqC (eq ×̂ ≅refl) t)
coeh eqC eq         (snd t)     = snd (coeh eqC (≅refl ×̂ eq) t)
coeh eqC (▸̂ a≅)     (▹ t)       = ▹_ (coeh eqC (≅force a≅) t)
coeh eqC (▸̂ a≅)     (t ∗ t₁)    = coeh eqC (▸̂ ≅delay (≅refl →̂ ≅force a≅)) t ∗ coeh eqC ≅refl t₁


-- A more flexible version of _∗_
▹app : ∀{Γ c∞ b∞}{a : Ty} (eq : c∞ ∞≅ (delay a ⇒ b∞))
                          (t : Tm Γ (▸̂ c∞)) (u : Tm Γ (▸ a)) → Tm Γ (▸̂ b∞)
▹app eq t u = cast (▸̂ eq) t ∗ u

_∗'_  : ∀{Γ a∞ b∞} (t : Tm Γ (▸̂ (a∞ ⇒ b∞))) (u : Tm Γ (▸̂ a∞)) → Tm Γ (▸̂ b∞)
_∗'_ {a∞ = a∞} t u = _∗_ {a = force a∞} (cast (▸̂ (≅delay ≅refl)) t) (cast ((▸̂ (≅delay ≅refl))) u)

_<$>_ : ∀{Γ}{a : Ty}{b∞} (t : Tm Γ (a →̂ force b∞)) (u : Tm Γ (▸ a)) → Tm Γ (▸̂ b∞)
t <$> u = ▹ t ∗ u

tmId : ∀ {Γ} a → Tm Γ a → Tm Γ a
tmId a t = t

syntax tmId a t = t ∶ a

-- Equality of subterms

≡app₁ : ∀ {Γ a a' b}{t : Tm Γ (a →̂ b)}{t' : Tm Γ (a' →̂ b)}{u u'}
         → Tm.app t u ≡ app t' u'
         → (P : {a : Ty} → Tm Γ a → Set) → P t → P t'
≡app₁ ≡.refl P x = x

≡appTy : ∀{Γ a a' b}{t : Tm Γ (a →̂ b)}{t' : Tm Γ (a' →̂ b)}{u u'} → Tm.app t u ≡ app t' u' → a ≡ a'
≡appTy ≡.refl = ≡.refl

≡app₁' : ∀{Γ a b}{t t' : Tm Γ (a →̂ b)}{u u'} → Tm.app t u ≡ app t' u' → t ≡ t'
≡app₁' ≡.refl = ≡.refl
