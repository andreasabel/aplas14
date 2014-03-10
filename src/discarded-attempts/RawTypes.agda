module RawTypes where

open import Library

TyCxt = ℕ
TyVar = Fin

data Ty (Δ : TyCxt) : Set where
  var : ∀ (x : TyVar Δ)    → Ty Δ
  ▸̂_  : ∀ (a : Ty Δ)       → Ty Δ
  1̂   :                      Ty Δ
  _×̂_ : ∀ (a b : Ty Δ)     → Ty Δ
  _+̂_ : ∀ (a b : Ty Δ)     → Ty Δ
  _→̂_ : ∀ (a b : Ty Δ)     → Ty Δ
  μ̂_  : ∀ (f : Ty (suc Δ)) → Ty Δ


-- Well-kinded type substitutions

data TySubst (Γ : TyCxt) : (Δ : TyCxt) → Set where
  []  : TySubst Γ 0
  _∷_ : ∀{Δ} (a : Ty Γ) (τ : TySubst Γ Δ) → TySubst Γ (suc Δ)
