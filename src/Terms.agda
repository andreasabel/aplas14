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
