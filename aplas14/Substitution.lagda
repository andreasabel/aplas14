\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}

module Substitution where

open import Library
open import InfiniteTypes
open import Terms
\end{code}
}

\AgdaHide{
\begin{code}
-- VarTm n specifies whether the substitution produces variables or terms.
-- The index is used to impose an order on the constructors
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
\end{code}

\begin{code}
-- Lifiting a substitution
lifts : ∀ {m vt Γ Δ a} → RenSub {m} vt Γ Δ → RenSub vt (a ∷ Γ) (a ∷ Δ)
-- Performing a substitution
subst : ∀ {m vt Γ Δ τ} → RenSub {m} vt Γ Δ → Tm Γ τ → Tm Δ τ
\end{code}

\AgdaHide{
\begin{code}
lifts {vt = `Var} σ (zero)    = zero
lifts {vt = `Var} σ (suc x) = suc (σ x)
lifts {vt = `Tm}  σ (zero)    = var (zero)
lifts {vt = `Tm}  σ (suc x) = subst {vt = `Var} suc (σ x)

subst σ (abs t)     = abs (subst (lifts σ) t)
subst σ (app t u)   = app (subst σ t) (subst σ u)
subst σ (next t)       = next (subst σ t)
subst σ (t ∗ u)     = subst σ t ∗ subst σ u
subst σ (pair t u)  = pair (subst σ t) (subst σ u)
subst σ (fst t)     = fst (subst σ t)
subst σ (snd t)     = snd (subst σ t)
subst σ (var x)     = vt2tm _ (σ x)
\end{code}
}
\begin{code}
-- Identity substitution

ids : ∀ {i vt Γ} → RenSub {i} vt Γ Γ
ids {vt = `Var} x = x
ids {vt = `Tm } x = var x

-- substitution composition

_•s_ : ∀ {Γ₀ Γ₁ Γ₂}
         {n}{vt2 : VarTm n}(τ : RenSub vt2 Γ₁ Γ₂)
         {m}{vt1 : VarTm m}(σ : RenSub vt1 Γ₀ Γ₁) → RenSub (vt1 ∙VT vt2) Γ₀ Γ₂
_•s_ τ {vt1 = `Var} σ x = τ (σ x)
_•s_ τ {vt1 = `Tm } σ x = subst τ (σ x)

-- Term substitution

Subst : Cxt → Cxt → Set
Subst Γ Δ = ∀ {a : Ty} → Var Γ a → Tm Δ a


-- Extending a substitution

_∷s_ : ∀ {Γ Δ a} → Tm Γ a → Subst Δ Γ → Subst (a ∷ Δ) Γ
(t ∷s σ) (zero) = t
(t ∷s σ) (suc x) = σ x

-- Substitution for 0th variable

sgs : ∀ {Γ a} → Tm Γ a → Subst (a ∷ Γ) Γ
sgs t = t ∷s ids

-- Substituting for the 0th variable [u/0]t

subst0 : ∀ {Γ a b} → Tm Γ a → Tm (a ∷ Γ) b → Tm Γ b
subst0 u = subst (sgs u)

-- Renamings

Ren : (Γ Δ : Cxt) → Set
Ren = RenSub `Var

_≤_  : (Γ Δ : Cxt) → Set
_≤_ Γ Δ = ∀ {a} → Var Δ a → Var Γ a

rename : ∀ {Γ Δ : Cxt} {a : Ty} (η : Γ ≤ Δ) (x : Tm Δ a) → Tm Γ a
rename = subst

-- Weakening renaming

weak : ∀{Γ a} → (a ∷ Γ) ≤ Γ
weak = suc

-- Weakening substitution

weaks : ∀{n}{vt : VarTm n}{a Γ Δ} (σ : RenSub vt Γ Δ) → RenSub vt (Γ) (a ∷ Δ)
weaks {vt = `Var} σ x = suc (σ x)
weaks {vt = `Tm} σ x = rename suc (σ x)


_≡s_ : ∀ {Γ Δ} {m n vt1 vt2} → (f : RenSub {m} vt1 Γ Δ)(g : RenSub {n} vt2 Γ Δ) → Set
f ≡s g = ∀ {a} x → vt2tm _ (f {a} x) ≡ vt2tm _ (g x)
\end{code}

\begin{code}
subst-ext :  ∀ {Γ Δ} {m n vt1 vt2} {f : RenSub {m} vt1 Γ Δ}{g : RenSub {n} vt2 Γ Δ} →
             f ≡s g → ∀ {a} (t : Tm Γ a) → subst f t ≡ subst g t
\end{code}
\AgdaHide{
\begin{code}
lifts-ext : ∀ {Γ Δ b} {m n vt1 vt2} {f : RenSub {m} vt1 Γ Δ}{g : RenSub {n} vt2 Γ Δ} → f ≡s g → lifts {a = b} f ≡s lifts g
subst-ext f≐g (var v) = (f≐g v)
subst-ext {f = f} {g = g} f≐g (abs t)     = ≡.cong abs (subst-ext (lifts-ext {f = f} {g = g} f≐g) t)
subst-ext f≐g (app t t₁)  = ≡.cong₂ app (subst-ext f≐g t) (subst-ext f≐g t₁)
subst-ext f≐g (pair t t₁) = ≡.cong₂ pair (subst-ext f≐g t) (subst-ext f≐g t₁)
subst-ext f≐g (fst t)     = ≡.cong fst (subst-ext f≐g t)
subst-ext f≐g (snd t)     = ≡.cong snd (subst-ext f≐g t)
subst-ext f≐g (next t)       = ≡.cong next (subst-ext f≐g t)
subst-ext f≐g (t ∗ t₁)    = ≡.cong₂ _∗_ (subst-ext f≐g t) (subst-ext f≐g t₁)

lifts-ext {vt1 = `Var} {`Var} f≐g (zero) = ≡.refl
lifts-ext {vt1 = `Var} {`Var} {f} {g} f≐g (suc x) with f x | g x | f≐g x
lifts-ext {Γ} {Δ} {b} {._} {._} {`Var} {`Var} f≐g (suc x) | z | .z | ≡.refl = ≡.refl
lifts-ext {vt1 = `Var} {`Tm} f≐g (zero) = ≡.refl
lifts-ext {vt1 = `Var} {`Tm} f≐g (suc x) rewrite ≡.sym (f≐g x) = ≡.refl
lifts-ext {vt1 = `Tm} {`Var} f≐g (zero) = ≡.refl
lifts-ext {vt1 = `Tm} {`Var} f≐g (suc x) rewrite (f≐g x) = ≡.refl
lifts-ext {vt1 = `Tm} {`Tm} f≐g (zero) = ≡.refl
lifts-ext {vt1 = `Tm} {`Tm} f≐g (suc x) = ≡.cong (subst suc) (f≐g x)
\end{code}
}

\begin{code}
subst-∙ :  ∀ {Γ₀ Γ₁ Γ₂}
           {n}{vt2 : VarTm n}(τ : RenSub vt2 Γ₁ Γ₂)
           {m}{vt1 : VarTm m}(σ : RenSub vt1 Γ₀ Γ₁)
           → ∀ {a} (t : Tm Γ₀ a) → subst (τ •s σ) t ≡ subst τ (subst σ t)
\end{code}
\AgdaHide{
\begin{code}
lifts-∙ :  ∀ {Γ₀ Γ₁ Γ₂}
           {n}{vt2 : VarTm n}(τ : RenSub vt2 Γ₁ Γ₂)
           {m}{vt1 : VarTm m}(σ : RenSub vt1 Γ₀ Γ₁)
           → ∀ {a} → lifts {a = a} (τ •s σ) ≡s (lifts τ •s lifts σ)
subst-∙ τ {vt1 = `Var} σ (var x) = ≡.refl
subst-∙ τ {vt1 = `Tm} σ (var x) = ≡.refl
subst-∙ τ σ (abs t)     = ≡.cong abs (≡.trans (subst-ext (lifts-∙ τ σ) t) (subst-∙ (lifts τ) (lifts σ) t))
subst-∙ τ σ (app t t₁)  = ≡.cong₂ app (subst-∙ τ σ t) (subst-∙ τ σ t₁)
subst-∙ τ σ (pair t t₁) = ≡.cong₂ pair (subst-∙ τ σ t) (subst-∙ τ σ t₁)
subst-∙ τ σ (fst t)     = ≡.cong fst (subst-∙ τ σ t)
subst-∙ τ σ (snd t)     = ≡.cong snd (subst-∙ τ σ t)
subst-∙ τ σ (next t)       = ≡.cong next (subst-∙ τ σ t)
subst-∙ τ σ (t ∗ t₁)    = ≡.cong₂ _∗_ (subst-∙ τ σ t) (subst-∙ τ σ t₁)

lifts-∙ {vt2 = `Var} τ {vt1 = `Var} σ (zero)    = ≡.refl
lifts-∙ {vt2 = `Tm}  τ {vt1 = `Var} σ (zero)    = ≡.refl
lifts-∙ {vt2 = `Var} τ {vt1 = `Var} σ (suc x) = ≡.refl
lifts-∙ {vt2 = `Tm}  τ {vt1 = `Var} σ (suc x) = ≡.refl
lifts-∙ {vt2 = `Var} τ {vt1 = `Tm}  σ (zero)    = ≡.refl
lifts-∙ {vt2 = `Tm}  τ {vt1 = `Tm}  σ (zero)    = ≡.refl
lifts-∙ {vt2 = `Var} τ {vt1 = `Tm}  σ (suc x) = ≡.trans (≡.sym (subst-∙ suc τ (σ x))) (subst-∙ (lifts τ) suc (σ x))
lifts-∙ {vt2 = `Tm}  τ {vt1 = `Tm}  σ (suc x) = ≡.trans (≡.sym (subst-∙ suc τ (σ x))) (subst-∙ (lifts τ) suc (σ x))
\end{code}
}
\begin{code}
subst-id : ∀ {m vt Γ a} → (t : Tm Γ a) → subst (ids {m} {vt}) t ≡ t
\end{code}

\AgdaHide{
\begin{code}
lifts-id : ∀ {m vt Γ b} → lifts {a = b} (ids {m} {vt} {Γ = Γ}) ≡s ids {m} {vt} {Γ = b ∷ Γ}
subst-id {vt = `Var} (var v) = ≡.refl
subst-id {vt = `Tm}  (var v) = ≡.refl
subst-id {m} {vt} {Γ} (abs t)     = ≡.cong abs (≡.trans (subst-ext {n = m} {vt2 = vt} (lifts-id {m} {vt}) t) (subst-id t))
subst-id (app t t₁)  = ≡.cong₂ app (subst-id t) (subst-id t₁)
subst-id (pair t t₁) = ≡.cong₂ pair (subst-id t) (subst-id t₁)
subst-id (fst t)     = ≡.cong fst (subst-id t)
subst-id (snd t)     = ≡.cong snd (subst-id t)
subst-id (next t)       = ≡.cong next (subst-id t)
subst-id (t ∗ t₁)    = ≡.cong₂ _∗_ (subst-id t) (subst-id t₁)

lifts-id {vt = `Var} (zero)    = ≡.refl
lifts-id {vt = `Var} (suc x) = ≡.refl
lifts-id {vt = `Tm}  (zero)    = ≡.refl
lifts-id {vt = `Tm}  (suc x) = ≡.refl
\end{code}
}

%% not sure how many of these we want to show
\begin{code}
sgs-lifts :  ∀ {m vt Γ Δ a} {σ : RenSub {m} vt Γ Δ} {u : Tm Γ a}
             → (sgs (subst σ u) •s lifts σ) ≡s (σ •s sgs u)
sgs-lifts-term : ∀ {m vt Γ Δ a b} {σ : RenSub {m} vt Γ Δ} {u : Tm Γ a}{t : Tm (a ∷ Γ) b}
                 → subst (sgs (subst σ u)) (subst (lifts σ) t) ≡ subst σ (subst (sgs u) t)
renId : ∀ {Γ a}{t : Tm Γ a} → rename id t ≡ t
contract : ∀ {a Γ} → RenSub `Var (a ∷ a ∷ Γ) (a ∷ Γ)
contract-sgs : ∀ {a Γ} → contract {a} {Γ} ≡s sgs (var zero)
sgs-weak₀ : ∀ {Γ a} {u : Tm Γ a} {b} (x : Var Γ b) → sgs u (suc x) ≡ var x
sgs-weak₁ : ∀ {Γ a} {u : Tm Γ a} → (sgs u ∘ suc) ≡s (ids {vt = `Tm})
sgs-weak : ∀ {Γ a} {u : Tm Γ a} → (sgs u •s weak) ≡s (ids {vt = `Tm})
cons-to-sgs :  ∀ {Γ Δ a} (u : Tm Δ a) (σ : Subst Γ Δ)
               → (u ∷s σ) ≡s (sgs u •s lifts σ)
\end{code}

\AgdaHide{
\begin{code}
sgs-lifts {vt = `Var} = (λ { (zero) → ≡.refl ; (suc x) → ≡.refl })
sgs-lifts {vt = `Tm} {σ = σ} {u} = (λ { (zero) → ≡.refl ; (suc x) → ≡.sym (≡.trans (≡.sym (subst-id (σ x)))
                                                                               (subst-∙ (sgs (subst σ u)) {vt1 = `Var} suc (σ x))) })
sgs-lifts-term {σ = σ} {u} {t} = (≡.trans (≡.sym (subst-∙ (sgs (subst σ u)) (lifts σ) t))
                                 (≡.trans (subst-ext sgs-lifts t)
                                          (subst-∙ σ (sgs u) t)))

renId = subst-id _

contract (zero)    = zero
contract (suc x) = x

contract-sgs (zero)  = ≡.refl
contract-sgs (suc x) = ≡.refl

sgs-weak₀ x = ≡.refl

sgs-weak₁ x = ≡.refl

sgs-weak x = ≡.refl

cons-to-sgs u σ (zero) = ≡.refl
cons-to-sgs u σ (suc x) = begin
    σ x                               ≡⟨ ≡.sym (subst-id (σ x)) ⟩
    subst (ids {vt = `Tm}) (σ x)      ≡⟨ subst-ext (λ _ → ≡.refl) (σ x) ⟩
    subst (sgs u •s weak) (σ x)       ≡⟨ subst-∙ (sgs u) weak (σ x) ⟩
    subst (sgs u) (subst suc (σ x))
  ∎
  where open ≡-Reasoning
\end{code}
}
}
