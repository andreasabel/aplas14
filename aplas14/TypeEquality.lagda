\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}

module TypeEquality where

open import Library
open import InfiniteTypes
open import Terms
\end{code}
}


%-- Which terms are accepted by this well-typed syntax is affected by
%-- which types are considered equal.  Unfortunately Agda's own notion of
%-- equality is too intensional, we can however define bisimulation
%-- explicitly as a coinductive type, and prove it is in fact an
%-- equivalence relation.

\begin{code}
mutual
  data _≅_ : (a b : Ty) → Set where
    _×̂_  : ∀{a a' b b'} (a≅ : a ≅ a') (b≅ : b ≅ b')  → (a ×̂ b) ≅ (a' ×̂ b')
    _→̂_  : ∀{a a' b b'} (a≅ : a' ≅ a) (b≅ : b ≅ b')  → (a →̂ b) ≅ (a' →̂ b')
    ▸̂_   : ∀{a∞ b∞}     (a≅ : a∞ ∞≅ b∞)              → ▸̂ a∞    ≅ ▸̂ b∞

  record _∞≅_ (a∞ b∞ : ∞Ty) : Set where
    coinductive
    constructor  ≅delay
    field        ≅force : force a∞ ≅ force b∞
\end{code}
\AgdaHide{
\begin{code}
open _∞≅_ public
\end{code}
}

$\Ty$-equality is indeed an equivalence relation (we omit the standard proof).

\begin{code}
≅refl   : ∀{a}      → a ≅ a
≅sym    : ∀{a b}    → a ≅ b  → b ≅ a
≅trans  : ∀{a b c}  → a ≅ b  → b ≅ c → a ≅ c
\end{code}

\AgdaHide{
\begin{code}

≅refl∞ : ∀{a∞} → a∞ ∞≅ a∞

≅refl {a ×̂ b}  = (≅refl {a}) ×̂ (≅refl {b})
≅refl {a →̂ b}  = (≅refl {a}) →̂ (≅refl {b})
≅refl {▸̂ a∞ }  = ▸̂ (≅refl∞ {a∞})

≅force ≅refl∞ = ≅refl

≅sym∞ : ∀{a∞ b∞} → a∞ ∞≅ b∞ → b∞ ∞≅ a∞

≅sym (eq ×̂ eq₁)  = (≅sym eq) ×̂ (≅sym eq₁)
≅sym (eq →̂ eq₁)  = (≅sym eq) →̂ (≅sym eq₁)
≅sym (▸̂ a≅)      = ▸̂ (≅sym∞ a≅)

≅force (≅sym∞ eq) = ≅sym (≅force eq)

≅trans∞ : ∀{a∞ b∞ c∞} → a∞ ∞≅ b∞ → b∞ ∞≅ c∞ → a∞ ∞≅ c∞

≅trans (eq₁ ×̂ eq₂) (eq₁' ×̂ eq₂')  = (≅trans eq₁ eq₁') ×̂ (≅trans eq₂ eq₂')
≅trans (eq₁ →̂ eq₂) (eq₁' →̂ eq₂')  = (≅trans eq₁' eq₁) →̂ (≅trans eq₂ eq₂')
≅trans (▸̂ eq) (▸̂ eq')             = ▸̂ (≅trans∞ eq eq')

≅force (≅trans∞ eq eq') = ≅trans (≅force eq) (≅force eq')

-- Type equality lifted to contexts.

_≅C_ : Cxt → Cxt → Set
_≅C_ = ≅L _≅_
\end{code}
} % END AGDAHIDE

However, unlike for $\propeq$ we do not get a generic substitution
principle for $\bisim$, but have to prove it for any function and
predicate on $\Ty$.  In particular, we have to show that we can cast a
term in $\Tm\;\Gam\;\va$ to $\Tm\;\Gam\;\vb$ if $\va \bisim \vb$, which
would require us to build type equality at least into
$\Var\;\Gam\;\va$.  In essence, this would amount to work with setoids
across all our development, which would add complexity without
strengthening our result.  Hence, we fall for the shortcut:

It is consistent to postulate that bisimulation implies equality,
similarly to the functional extensionality principle for function
types.
% \begin{code}
% postulate
%   ≅-to-≡ : ∀ {a b} → a ≅ b → a ≡ b
% \end{code}
This lets us define the function $\tcast$ to convert terms between
bisimilar types.
\begin{code}
postulate ≅-to-≡ : ∀ {a b} → a ≅ b → a ≡ b

cast : ∀{Γ a b} (eq : a ≅ b) (t : Tm Γ a) → Tm Γ b
\end{code}
\AgdaHide{
\begin{code}
castVar : ∀{Γ Δ a b} (Γ≅Δ : Γ ≅C Δ) (a≅b : a ≅ b) (x : Var Γ a) → Var Δ b
castVar (a'≅b' ∷ Γ≅Δ) a≅b zero rewrite ≅-to-≡ (≅trans (≅sym a'≅b') a≅b) = zero
castVar (_     ∷ Γ≅Δ) a≅b (suc x)                                       = suc  (castVar Γ≅Δ a≅b x)


castC : ∀{Γ Δ a b} (eqC : Γ ≅C Δ) (eq : a ≅ b)  (t : Tm Γ a)      → Tm Δ b
castC eqC eq         (var x)     = var (castVar eqC eq x)
castC eqC (eq →̂ eq₁) (abs t)     = abs (castC (≅sym eq ∷ eqC) eq₁ t)
castC eqC eq         (app t t₁)  = app (castC eqC (≅refl →̂ eq) t) (castC eqC ≅refl t₁)
castC eqC (eq ×̂ eq₁) (pair t t₁) = pair (castC eqC eq t) (castC eqC eq₁ t₁)
castC eqC eq         (fst t)     = fst (castC eqC (eq ×̂ ≅refl) t)
castC eqC eq         (snd t)     = snd (castC eqC (≅refl ×̂ eq) t)
castC eqC (▸̂ a≅)     (next t)       = next (castC eqC (≅force a≅) t)
castC eqC (▸̂ a≅)     (t ∗ t₁)    = (castC eqC (▸̂ (≅delay (≅refl →̂ (≅force a≅)))) t) ∗ (castC eqC ≅refl t₁)

cast = castC (≅L.refl ≅refl)
\end{code}
}

We shall require $\tcast$ in uses of functorial application, to
convert a type $\vcinf : \infTy$ into something that can be $\tforce$d
into a function type.
\begin{code}
▸app : ∀{Γ c∞ b∞ a}  (eq : c∞ ∞≅ (delay a ⇒ b∞))
                     (t : Tm Γ (▸̂ c∞)) (u : Tm Γ (▸ a)) → Tm Γ (▸̂ b∞)
▸app eq t u = cast (▸̂ eq) t ∗ u
\end{code}

