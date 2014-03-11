{-# OPTIONS --copatterns --sized-types #-}
{-# OPTIONS --no-termination-check #-} -- too slow

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

-- Identity substitution

ids : ∀ {i vt Γ} → RenSub {i} vt Γ Γ
ids {vt = `Var} x = x
ids {vt = `Tm } x = var x

-- substitution composition

_•s_ : ∀ {Γ₀ Γ₁ Γ₂}
         {n}{vt2 : VarTm n}(tau   : RenSub vt2 Γ₁ Γ₂)
         {m}{vt1 : VarTm m}(sigma : RenSub vt1 Γ₀ Γ₁) → RenSub (vt1 ∙VT vt2) Γ₀ Γ₂
_•s_ tau {vt1 = `Var} sigma x = tau (sigma x)
_•s_ tau {vt1 = `Tm } sigma x = subst tau (sigma x)


-- Term substitution

Subst : Cxt → Cxt → Set
Subst Γ Δ = ∀ {a : Ty} → Var Γ a → Tm Δ a


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

-- Properties

mutual
  subst-ext : ∀ {Γ Δ} {m vt} {f g : RenSub {m} vt Γ Δ} → (∀ {a} x → f {a} x ≡ g x) → ∀ {a} (t : Tm Γ a) → subst f t ≡ subst g t
  subst-ext f≐g (var v)     = ≡.cong (vt2tm _) (f≐g v)
  subst-ext f≐g (abs t)     = ≡.cong abs (subst-ext (lifts-ext f≐g) t)
  subst-ext f≐g (app t t₁)  = ≡.cong₂ app (subst-ext f≐g t) (subst-ext f≐g t₁)
  subst-ext f≐g (pair t t₁) = ≡.cong₂ pair (subst-ext f≐g t) (subst-ext f≐g t₁)
  subst-ext f≐g (fst t)     = ≡.cong fst (subst-ext f≐g t)
  subst-ext f≐g (snd t)     = ≡.cong snd (subst-ext f≐g t)
  subst-ext f≐g (▹ t)       = ≡.cong ▹_ (subst-ext f≐g t)
  subst-ext f≐g (t ∗ t₁)    = ≡.cong₂ _∗_ (subst-ext f≐g t) (subst-ext f≐g t₁)
  subst-ext f≐g (cast eq t) = ≡.cong (cast eq) (subst-ext f≐g t)

  lifts-ext : ∀ {Γ Δ b} {m vt} {f g : RenSub {m} vt Γ Δ} → (∀ {a} x → f {a} x ≡ g x) → ∀ {a} x → lifts {a = b} f {a} x ≡ lifts g x
  lifts-ext {vt = `Var} f≐g zero    = ≡.refl
  lifts-ext {vt = `Var} f≐g (suc x) = ≡.cong suc (f≐g x)
  lifts-ext {vt = `Tm}  f≐g zero    = ≡.refl
  lifts-ext {vt = `Tm}  f≐g (suc x) = ≡.cong (subst suc) (f≐g x)

mutual
  subst-∙ : ∀ {Γ₀ Γ₁ Γ₂}
           {n}{vt2 : VarTm n}(τ   : RenSub vt2 Γ₁ Γ₂)
           {m}{vt1 : VarTm m}(σ : RenSub vt1 Γ₀ Γ₁) → ∀ {a} (t : Tm Γ₀ a) → subst (τ •s σ) t ≡ subst τ (subst σ t)
  subst-∙ τ {vt1 = `Var} σ (var x) = ≡.refl
  subst-∙ τ {vt1 = `Tm} σ (var x) = ≡.refl
  subst-∙ τ σ (abs t)     = ≡.cong abs (≡.trans (subst-ext (lifts-∙ τ σ) t) (subst-∙ (lifts τ) (lifts σ) t))
  subst-∙ τ σ (app t t₁)  = ≡.cong₂ app (subst-∙ τ σ t) (subst-∙ τ σ t₁)
  subst-∙ τ σ (pair t t₁) = ≡.cong₂ pair (subst-∙ τ σ t) (subst-∙ τ σ t₁)
  subst-∙ τ σ (fst t)     = ≡.cong fst (subst-∙ τ σ t)
  subst-∙ τ σ (snd t)     = ≡.cong snd (subst-∙ τ σ t)
  subst-∙ τ σ (▹ t)       = ≡.cong ▹_ (subst-∙ τ σ t)
  subst-∙ τ σ (t ∗ t₁)    = ≡.cong₂ _∗_ (subst-∙ τ σ t) (subst-∙ τ σ t₁)
  subst-∙ τ σ (cast eq t) = ≡.cong (cast eq) (subst-∙ τ σ t)

  lifts-∙ : ∀ {Γ₀ Γ₁ Γ₂}
         {n}{vt2 : VarTm n}(τ   : RenSub vt2 Γ₁ Γ₂)
         {m}{vt1 : VarTm m}(σ : RenSub vt1 Γ₀ Γ₁) → ∀ {b a} (x : Var (b ∷ Γ₀) a) → lifts (τ •s σ) x ≡ (lifts τ •s lifts σ) x
  lifts-∙ {vt2 = `Var} τ {vt1 = `Var} σ zero    = ≡.refl
  lifts-∙ {vt2 = `Tm}  τ {vt1 = `Var} σ zero    = ≡.refl
  lifts-∙ {vt2 = `Var} τ {vt1 = `Var} σ (suc x) = ≡.refl
  lifts-∙ {vt2 = `Tm}  τ {vt1 = `Var} σ (suc x) = ≡.refl
  lifts-∙ {vt2 = `Var} τ {vt1 = `Tm}  σ zero    = ≡.refl
  lifts-∙ {vt2 = `Tm}  τ {vt1 = `Tm}  σ zero    = ≡.refl
  lifts-∙ {vt2 = `Var} τ {vt1 = `Tm}  σ (suc x) = ≡.trans (≡.sym (subst-∙ suc τ (σ x))) (subst-∙ (lifts τ) suc (σ x))
  lifts-∙ {vt2 = `Tm}  τ {vt1 = `Tm}  σ (suc x) = ≡.trans (≡.sym (subst-∙ suc τ (σ x))) (subst-∙ (lifts τ) suc (σ x))

mutual
  subst-id : ∀ {m vt Γ a} → (t : Tm Γ a) → subst (ids {m} {vt}) t ≡ t
  subst-id {vt = `Var} (var v) = ≡.refl
  subst-id {vt = `Tm}  (var v) = ≡.refl
  subst-id (abs t)     = ≡.cong abs (≡.trans (subst-ext lifts-id t) (subst-id t))
  subst-id (app t t₁)  = ≡.cong₂ app (subst-id t) (subst-id t₁)
  subst-id (pair t t₁) = ≡.cong₂ pair (subst-id t) (subst-id t₁)
  subst-id (fst t)     = ≡.cong fst (subst-id t)
  subst-id (snd t)     = ≡.cong snd (subst-id t)
  subst-id (▹ t)       = ≡.cong ▹_ (subst-id t)
  subst-id (t ∗ t₁)    = ≡.cong₂ _∗_ (subst-id t) (subst-id t₁)
  subst-id (cast eq t) = ≡.cong (cast eq) (subst-id t)

  lifts-id : ∀ {m vt Γ b a} → (x : Var (b ∷ Γ) a) → lifts (ids {m} {vt}) x ≡ ids x
  lifts-id {vt = `Var} zero    = ≡.refl
  lifts-id {vt = `Var} (suc x) = ≡.refl
  lifts-id {vt = `Tm}  zero    = ≡.refl
  lifts-id {vt = `Tm}  (suc x) = ≡.refl


renId : ∀ {Γ a}{t : Tm Γ a} → rename (λ x → x) t ≡ t
renId = subst-id _

