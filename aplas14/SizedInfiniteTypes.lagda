\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}

module SizedInfiniteTypes where

open import Library
\end{code}
}



\begin{code}
mutual
  data Ty {i : Size} : Set where
    _×̂_   : ∀ (a b : Ty {i})  → Ty {i}
    _→̂_   : ∀ (a b : Ty {i})  → Ty {i}
    ▸̂_    : ∀ (a∞ : ∞Ty {i})  → Ty {i}

  record ∞Ty {i : Size} : Set where
    coinductive
    constructor  delay_
    field        force_ : ∀{j : Size< i} → Ty {j}
open ∞Ty public
\end{code}


\begin{code}
▸_ : ∀{i} → Ty {i} → Ty {↑ i}
▸ A = ▸̂ delay A

_⇒_ : ∀{i} (a∞ b∞ : ∞Ty {i}) → ∞Ty {i}
force (a∞ ⇒ b∞) = force a∞ →̂ force b∞
\end{code}


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
