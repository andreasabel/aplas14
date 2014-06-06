\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}

module AgdaExamples where

open import Library
open import SizedInfiniteTypes
open import Terms
\end{code}
}
\begin{code}
μ̂ : ∀{i} → (∀{j : Size< i} → ∞Ty {j} → Ty {j}) → ∞Ty {i}
(force (μ̂ {i} F)) {j} = F (μ̂ {j} F)
\end{code}


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
open _∞≅_ public
\end{code}


\begin{code}
≅refl  : ∀{a}     → a ≅ a
≅sym   : ∀{a b}   → a ≅ b → b ≅ a
≅trans : ∀{a b c} → a ≅ b → b ≅ c → a ≅ c
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
\end{code}
} % END AGDAHIDE

\begin{code}
postulate
  ≅-to-≡ : ∀ {a b} → a ≅ b → a ≡ b
\end{code}

\AgdaHide{
\begin{code}
postulate
\end{code}
}


\begin{code}
  cast : ∀{Γ a b} (eq : a ≅ b) (t : Tm Γ a) → Tm Γ b
\end{code}

\begin{code}
▹app : ∀{Γ c∞ b∞}{a : Ty} (eq : c∞ ∞≅ (delay a ⇒ b∞))
                          (t : Tm Γ (▸̂ c∞)) (u : Tm Γ (▸ a)) → Tm Γ (▸̂ b∞)
▹app eq t u = cast (▸̂ eq) t ∗ u

Fix_ : Ty → ∞Ty
force Fix A = ▸̂ Fix A →̂ A

omega : ∀{Γ A} → Tm Γ (▸̂ Fix A) → Tm Γ (▸ A)
omega x = ▹app (≅delay ≅refl) x (next x)

Y : ∀{Γ A} → Tm Γ ((▸ A →̂ A) →̂ A)
Y = abs (app L (next L))
  where
    f = var (suc v₀)
    x = var v₀
    L = abs (app f (omega x))
\end{code}

\begin{code}
mutual
  Stream : Ty → Ty
  Stream A = A ×̂ ▸̂ Stream∞ A

  Stream∞ : Ty → ∞Ty
  force (Stream∞ A) = Stream A

cons : ∀{Γ A} → Tm Γ A → Tm Γ (▸ Stream A) → Tm Γ (Stream A)
cons a s = pair a (cast (▸̂ (≅delay ≅refl)) s)

head : ∀{Γ A} → Tm Γ (Stream A) → Tm Γ A
head s = fst s

tail : ∀{Γ A} → Tm Γ (Stream A) → Tm Γ (▸ Stream A)
tail s = cast (▸̂ (≅delay ≅refl)) (snd s)
\end{code}

