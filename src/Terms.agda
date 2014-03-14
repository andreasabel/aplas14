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

_≅C_ : Cxt → Cxt → Set
_≅C_ = ≅L _≅_

castVar : ∀{Γ Δ a b} → (eqC : Γ ≅C Δ) (eq : a ≅ b)  (t : Var Γ a) → Var Δ b
castVar (x∼y ∷ eqC) eq (zero eq₁) = zero TODO
castVar (x∼y ∷ eqC) eq (suc x₁) = suc (castVar eqC eq x₁)

castC : ∀{Γ Δ a b} (eqC : Γ ≅C Δ) (eq : a ≅ b)  (t : Tm Γ a)      → Tm Δ b
castC eqC eq (var x) = var (castVar eqC eq x)
castC eqC (eq →̂ eq₁) (abs t) = abs (castC (eq ∷ eqC) eq₁ t)
castC eqC eq (app t t₁) = app (castC eqC (≅refl →̂ eq) t) (castC eqC ≅refl t₁)
castC eqC (eq ×̂ eq₁) (pair t t₁) = pair (castC eqC eq t) (castC eqC eq₁ t₁)
castC eqC eq (fst t) = fst (castC eqC (eq ×̂ ≅refl) t)
castC eqC eq (snd t) = snd (castC eqC (≅refl ×̂ eq) t)
castC eqC (▸̂ a≅) (▹ t) = ▹ (castC eqC (≅force a≅) t)
castC eqC (▸̂ a≅) (t ∗ t₁) = (castC eqC (▸̂ (≅delay (≅refl →̂ (≅force a≅)))) t) ∗ (castC eqC ≅refl t₁)

cast : ∀{Γ a b} (eq : a ≅ b) (t : Tm Γ a) → Tm Γ b
cast = castC (≅L.refl ≅refl)

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
         → app t u ≡ app t' u'
         → (P : {a : Ty} → Tm Γ a → Set) → P t → P t'
≡app₁ ≡.refl P x = x

≡appTy : ∀{Γ a a' b}{t : Tm Γ (a →̂ b)}{t' : Tm Γ (a' →̂ b)}{u u'} → app t u ≡ app t' u' → a ≡ a'
≡appTy ≡.refl = ≡.refl

≡app₁' : ∀{Γ a b}{t t' : Tm Γ (a →̂ b)}{u u'} → app t u ≡ app t' u' → t ≡ t'
≡app₁' ≡.refl = ≡.refl
