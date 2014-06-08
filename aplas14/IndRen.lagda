\AgdaHide{
\begin{code}
module IndRen where
open import Library
open import InfiniteTypes
open import Terms
open import Substitution
\end{code}
}
\begin{code}
data IndRen  {Γ Δ} (σ : Δ ≤ Γ) : ∀ {a} → Tm Γ a → Tm Δ a → Set
\end{code}
\AgdaHide{
\begin{code}
 where
  var  : ∀{a y}          (x : Var Γ a) → (σ x) ≡ y         → IndRen σ (var x) (var y)
  abs  : ∀{a b}{t : Tm (a ∷ Γ) b}{t'} → IndRen (lifts σ) t t' → IndRen σ (abs t) (abs t')
  app  : ∀{a b}{t : Tm Γ (a →̂ b)}{u : Tm Γ a}{t' u'} → IndRen σ t t' → IndRen σ u u' → IndRen σ (app t u) (app t' u')
  pair : ∀{a b}{t : Tm Γ a} {u : Tm Γ b}{t' u'} → IndRen σ t t' → IndRen σ u u' → IndRen σ (pair t u) (pair t' u')
  fst  : ∀{a b}{t : Tm Γ (a ×̂ b)}{t'} → IndRen σ t t' → IndRen σ (fst t) (fst t')
  snd  : ∀{a b}{t : Tm Γ (a ×̂ b)}{t'} → IndRen σ t t' → IndRen σ (snd t) (snd t')
  next   : ∀{a∞}{t : Tm Γ (force a∞)}{t'} → IndRen σ t t' → IndRen σ (next {a∞ = a∞} t) (next t')

  -- `applicative'
  _∗_  : ∀{a∞}{b∞}{t : Tm Γ (▸̂ (a∞ ⇒ b∞))} {u : Tm Γ (▸̂  a∞)}{t' u'}
         →  IndRen σ t t' → IndRen σ u u' → IndRen σ (t ∗ u) (t' ∗ u')

Ind→prop : ∀ {Γ Δ} (σ : RenSub `Var Γ Δ) {τ} {t : Tm Γ τ} {t' : Tm Δ τ} → IndRen σ t t' → subst σ t ≡ t'
Ind→prop σ (var x ≡.refl) = ≡.refl
Ind→prop σ (abs t)     = ≡.cong abs (Ind→prop (lifts σ) t)
Ind→prop σ (app t t₁)  = ≡.cong₂ app (Ind→prop σ t) (Ind→prop σ t₁)
Ind→prop σ (pair t t₁) = ≡.cong₂ pair (Ind→prop σ t) (Ind→prop σ t₁)
Ind→prop σ (fst t)     = ≡.cong fst (Ind→prop σ t)
Ind→prop σ (snd t)     = ≡.cong snd (Ind→prop σ t)
Ind→prop σ (next t)       = ≡.cong next (Ind→prop σ t)
Ind→prop σ (t ∗ t₁)    = ≡.cong₂ _∗_ (Ind→prop σ t) (Ind→prop σ t₁)
--Ind→prop σ (cast eq t) = ≡.cong (cast eq) (Ind→prop σ t)

prop→Ind' : ∀ {Γ Δ} (σ : RenSub `Var Γ Δ) {τ} (t : Tm Γ τ) → IndRen σ t (subst σ t)
prop→Ind' σ (var x) = var x ≡.refl
prop→Ind' σ (abs t)     = abs (prop→Ind' (lifts σ) t)
prop→Ind' σ (app t u)   = app (prop→Ind' σ t) (prop→Ind' σ u)
prop→Ind' σ (next t)       = next (prop→Ind' σ t)
prop→Ind' σ (t ∗ u)     = (prop→Ind' σ t) ∗ (prop→Ind' σ u)
prop→Ind' σ (pair t u)  = pair (prop→Ind' σ t) (prop→Ind' σ u)
prop→Ind' σ (fst t)     = fst (prop→Ind' σ t)
prop→Ind' σ (snd t)     = snd (prop→Ind' σ t)
--prop→Ind' σ (cast eq t) = cast eq (prop→Ind' σ t)

prop→Ind : ∀ {Γ Δ} (σ : RenSub `Var Γ Δ) {τ} {t : Tm Γ τ} {t' : Tm Δ τ} → subst σ t ≡ t' → IndRen σ t t'
prop→Ind _ ≡.refl = prop→Ind' _ _

\end{code}
}
