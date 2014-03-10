{-# OPTIONS --copatterns --sized-types #-}

module Substitution where

open import Library
open import SizedInfiniteTypes
open import Terms

-- VarTm n specifies whether the substitution produces variables or terms.
-- The index is used to impose and order on the constructors
-- and so pass termination checking in lift/subst.
data VarTm : ℕ → Set where
  `Var : VarTm 0
  `Tm  : VarTm 1

max01 : ℕ → ℕ → ℕ
max01 0 m = m
max01 n m = n

_∙VT_ : ∀ {m n} → VarTm m → VarTm n → VarTm (max01 m n)
`Var ∙VT vt = vt
`Tm  ∙VT vt = `Tm

VT : ∀ {m} → VarTm m → Cxt → Ty → Set
VT `Var Γ a = Var Γ a
VT `Tm  Γ a = Tm Γ a


vt2tm : ∀ {Γ a} → ∀ {m} vt → VT {m} vt Γ a → Tm Γ a
vt2tm `Var  x = var x
vt2tm `Tm t = t

RenSub : ∀ {m} → VarTm m → Cxt → Cxt → Set
RenSub vt Γ Δ = ∀ {a} → Var Γ a → VT vt Δ a

mutual
  -- Lifiting a substitution

  lifts : ∀ {m vt Γ Δ a} → RenSub {m} vt Γ Δ → RenSub vt (a ∷ Γ) (a ∷ Δ)
  lifts {vt = `Var} σ zero    = zero
  lifts {vt = `Var} σ (suc x) = suc (σ x)
  lifts {vt = `Tm}  σ zero    = var zero
  lifts {vt = `Tm}  σ (suc x) = subst {vt = `Var} suc (σ x)

  -- Performing a substitution

  subst : ∀ {m vt Γ Δ τ} → RenSub {m} vt Γ Δ → Tm Γ τ → Tm Δ τ

  subst σ (abs t)     = abs (subst (lifts σ) t)
  subst σ (app t u)   = app (subst σ t) (subst σ u)
  subst σ (▹ t)       = ▹ (subst σ t)
  subst σ (t ∗ u)     = (subst σ t) ∗ (subst σ u)
  subst σ (pair t u)  = pair (subst σ t) (subst σ u)
  subst σ (fst t)     = fst (subst σ t)
  subst σ (snd t)     = snd (subst σ t)
  subst σ (cast eq t) = cast eq (subst σ t)
  subst σ (var x)     = vt2tm _ (σ x)

-- substitution composition

_•s_ : ∀ {Γ₀ Γ₁ Γ₂}
         {n}{vt2 : VarTm n}(tau   : RenSub vt2 Γ₁ Γ₂)
         {m}{vt1 : VarTm m}(sigma : RenSub vt1 Γ₀ Γ₁) → RenSub (vt1 ∙VT vt2) Γ₀ Γ₂
_•s_ tau {vt1 = `Var} sigma x = tau (sigma x)
_•s_ tau {vt1 = `Tm } sigma x = subst tau (sigma x)


-- Term substitution

Subst : Cxt → Cxt → Set
Subst Γ Δ = ∀ {a : Ty} → Var Γ a → Tm Δ a

-- Identity substitution

ids : ∀ {Γ} → Subst Γ Γ
ids = var

-- Substitution for 0th variable

sgs : ∀ {Γ a} → Tm Γ a → Subst (a ∷ Γ) Γ
sgs t zero    = t
sgs t (suc x) = var x

-- Substituting for the 0th variable [u/0]t

subst0 : ∀ {Γ a b} → Tm Γ a → Tm (a ∷ Γ) b → Tm Γ b
subst0 u = subst (sgs u)


_≤_  : (Γ Δ : Cxt) → Set
_≤_ Γ Δ = RenSub `Var Δ Γ

rename : ∀ {Γ Δ : Cxt} {a : Ty} (η : Γ ≤ Δ) (x : Tm Δ a) → Tm Γ a
rename = subst

renId : ∀ {Γ a}{t : Tm Γ a} → rename (λ x → x) t ≡ t
renId = TODO
