{-# OPTIONS --copatterns --sized-types #-}

module Terms where

open import Library
open import SizedInfiniteTypes

-- * Variables
------------------------------------------------------------------------

-- Typing contexts.

Cxt = List Ty

-- Type equality lifted to contexts.

_≅C_ : Cxt → Cxt → Set
_≅C_ = ≅L _≅_

-- Variables.

data Var : (Γ : Cxt) (a : Ty) → Set where
  zero : ∀{Γ a b}  (eq : a ≅ b) → Var (a ∷ Γ) b
  suc  : ∀{Γ a b} (x : Var Γ a) → Var (b ∷ Γ) a

-- De Bruijn index 0.

v₀ : ∀ {a Γ} → Var (a ∷ Γ) a
v₀ = zero ≅refl

-- A congruence on variables.  Ignores the equality proofs embedded in zero.
-- Two variables are equal if they have the same de Bruijn index.

data _≅V_ : ∀ {Γ Γ' a a'} → Var Γ a → Var Γ' a' → Set where

  zero : ∀ {Γ a b} {eq : a ≅ b} {Γ' a' b'} {eq' : a' ≅ b'}

         → zero {Γ = Γ} eq ≅V zero {Γ = Γ'} eq'

  suc  : ∀ {Γ a b} {x : Var Γ a} {Γ' a' b'} {x' : Var Γ' a'}

         → x ≅V x'
         → suc {b = b} x ≅V suc {b = b'} x'

-- We are indeed an equivalence relation.

Vrefl : ∀ {Γ : Cxt} {a : Ty} {x : Var Γ a} → x ≅V x
Vrefl {x = zero eq} = zero
Vrefl {x = suc t}   = suc Vrefl

Vsym : ∀ {Γ Γ' a a'} {x : Var Γ a} {x' : Var Γ' a'} → x ≅V x' → x' ≅V x
Vsym zero      = zero
Vsym (suc [x]) = suc (Vsym [x])

Vtrans : ∀ {Γ Γ' Γ'' a a' a''} {x : Var Γ a} {x' : Var Γ' a'} {x'' : Var Γ'' a''}
       → x ≅V x' → x' ≅V x'' → x ≅V x''
Vtrans zero     zero      = zero
Vtrans (suc eq) (suc eq') = suc (Vtrans eq eq')

-- Coercion and coherence for variables.

castVar : ∀{Γ Δ a b} (Γ≅Δ : Γ ≅C Δ) (a≅b : a ≅ b) (x : Var Γ a) → Var Δ b
castVar (a'≅b' ∷ Γ≅Δ) a≅b (zero a'≅a) = zero (≅fill a'≅b' a'≅a a≅b)
castVar (_     ∷ Γ≅Δ) a≅b (suc x)     = suc  (castVar Γ≅Δ a≅b x)

cohV : ∀{Γ Δ a b} (eqC : Γ ≅C Δ) (eq : a ≅ b) (x : Var Γ a) → castVar eqC eq x ≅V x
cohV (x∼y ∷ eqC) eq (zero eq₁) = zero
cohV (x∼y ∷ eqC) eq (suc x₁)   = suc (cohV eqC eq x₁)

-- * Terms
------------------------------------------------------------------------

-- Well-typed terms.

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

-- Variable congruence extended to terms.

data _≅T_ {Γ Γ' : Cxt} : {a a' : Ty} → Tm Γ a → Tm Γ' a' → Set where

  var  : ∀ {a a'}
         → {x : Var Γ a}         {x' : Var Γ' a'}         → ([x] : x ≅V x')
         → var x ≅T var x'

  abs  : ∀ {a b a' b'}
         → {t : Tm (a ∷ Γ) b}    {t' : Tm (a' ∷ Γ') b'}   → ([t] : t ≅T t')
         → abs t ≅T abs t'

  app  : ∀ {a b a' b'}
         → {t : Tm Γ (a →̂ b)}    {t' : Tm Γ' (a' →̂ b')}   → ([t] : t ≅T t')
         → {u : Tm Γ a}          {u' : Tm Γ' a'}          → ([u] : u ≅T u')
         → app t u ≅T app t' u'

  pair : ∀ {a b a' b'}
         → {t : Tm Γ a}          {t' : Tm Γ' a'}          → ([t] : t ≅T t')
         → {u : Tm Γ b}          {u' : Tm Γ' b'}          → ([u] : u ≅T u')
         → pair t u ≅T pair t' u'

  fst  : ∀ {a b a' b'}
         → {t : Tm Γ (a ×̂ b)}    {t' : Tm Γ' (a' ×̂ b')}   → ([t] : t ≅T t')
         → fst t ≅T fst t'

  snd  : ∀ {a b a' b'}
         → {t : Tm Γ (a ×̂ b)}    {t' : Tm Γ' (a' ×̂ b')}   → ([t] : t ≅T t')
         → snd t ≅T snd t'

  ▹_   : ∀ {a∞ a∞'}
         → {t : Tm Γ (force a∞)} {t' : Tm Γ' (force a∞')} → ([t] : t ≅T t')
         → ▹_ {a∞ = a∞} t ≅T ▹_ {a∞ = a∞'} t'

  -- `applicative'
  _∗_  : ∀ {a : Ty}{b∞}{a' : Ty}{b∞'}
         → {t  : Tm Γ  (▸̂ (delay a  ⇒ b∞ ))}
         → {t' : Tm Γ' (▸̂ (delay a' ⇒ b∞'))}              → ([t] : t ≅T t')
         → {u : Tm Γ (▸ a)} {u' : Tm Γ' (▸ a')}           → ([u] : u ≅T u')
         → (t ∗ u) ≅T (t' ∗ u')

-- The term congruence is an equivalence relation.

Trefl : ∀ {Γ : Cxt} {a : Ty} → {t : Tm Γ a} → t ≅T t
Trefl {t = var x}     = var Vrefl
Trefl {t = abs t}     = abs Trefl
Trefl {t = app t u}   = app Trefl Trefl
Trefl {t = ▹ t}       = ▹ Trefl
Trefl {t = t ∗ u}     = Trefl ∗ Trefl
Trefl {t = pair t u}  = pair Trefl Trefl
Trefl {t = fst t}     = fst Trefl
Trefl {t = snd t}     = snd Trefl

Tsym : ∀ {Γ Γ' a a'} {t : Tm Γ a} {t' : Tm Γ' a'} → t ≅T t' → t' ≅T t
Tsym (var [x]) = var (Vsym [x])
Tsym (abs t)     = abs (Tsym t)
Tsym (app t u)   = app (Tsym t) (Tsym u)
Tsym (▹ t)       = ▹ (Tsym t)
Tsym (t ∗ u)     = (Tsym t) ∗ (Tsym u)
Tsym (pair t u)  = pair (Tsym t) (Tsym u)
Tsym (fst t)     = fst (Tsym t)
Tsym (snd t)     = snd (Tsym t)

Ttrans : ∀ {Γ Γ' Γ'' a a' a''} {t : Tm Γ a} {t' : Tm Γ' a'} {t'' : Tm Γ'' a''}
         → t ≅T t' → t' ≅T t'' → t ≅T t''
Ttrans (var [x])  (var [x'])   = var (Vtrans [x] [x'])
Ttrans (abs t)    (abs t')     = abs (Ttrans t t')
Ttrans (app t u)  (app t' u')  = app (Ttrans t t') (Ttrans u u')
Ttrans (▹ t)      (▹ t')       = ▹ (Ttrans t t')
Ttrans (t ∗ u)    (t' ∗ u')    = (Ttrans t t') ∗ (Ttrans u u')
Ttrans (pair t u) (pair t' u') = pair (Ttrans t t') (Ttrans u u')
Ttrans (fst t)    (fst t')     = fst (Ttrans t t')
Ttrans (snd t)    (snd t')     = snd (Ttrans t t')

-- Coercion and coherence for terms.

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

coh : ∀{Γ Δ a b} (eqC : Γ ≅C Δ) (eq : a ≅ b) (t : Tm Γ a) → castC eqC eq t ≅T t
coh eqC eq         (var x)     = var (cohV eqC eq x)
coh eqC (eq →̂ eq₁) (abs t)     = abs (coh (eq ∷ eqC) eq₁ t)
coh eqC eq         (app t t₁)  = app (coh eqC (≅refl →̂ eq) t) (coh eqC ≅refl t₁)
coh eqC (eq ×̂ eq₁) (pair t t₁) = pair (coh eqC eq t) (coh eqC eq₁ t₁)
coh eqC eq         (fst t)     = fst (coh eqC (eq ×̂ ≅refl) t)
coh eqC eq         (snd t)     = snd (coh eqC (≅refl ×̂ eq) t)
coh eqC (▸̂ a≅)     (▹ t)       = ▹_ (coh eqC (≅force a≅) t)
coh eqC (▸̂ a≅)     (t ∗ t₁)    = coh eqC (▸̂ ≅delay (≅refl →̂ ≅force a≅)) t ∗ coh eqC ≅refl t₁


-- Variants of _∗_.

▹app : ∀{Γ c∞ b∞}{a : Ty} (eq : c∞ ∞≅ (delay a ⇒ b∞))
                          (t : Tm Γ (▸̂ c∞)) (u : Tm Γ (▸ a)) → Tm Γ (▸̂ b∞)
▹app eq t u = cast (▸̂ eq) t ∗ u

_∗'_  : ∀{Γ a∞ b∞} (t : Tm Γ (▸̂ (a∞ ⇒ b∞))) (u : Tm Γ (▸̂ a∞)) → Tm Γ (▸̂ b∞)
_∗'_ {a∞ = a∞} t u = _∗_ {a = force a∞} (cast (▸̂ (≅delay ≅refl)) t) (cast ((▸̂ (≅delay ≅refl))) u)

_<$>_ : ∀{Γ}{a : Ty}{b∞} (t : Tm Γ (a →̂ force b∞)) (u : Tm Γ (▸ a)) → Tm Γ (▸̂ b∞)
t <$> u = ▹ t ∗ u

-- Type annotation.

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
