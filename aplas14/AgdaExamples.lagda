\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}

module AgdaExamples where

open import Library
open import SizedInfiniteTypes
open import Terms
\end{code}
}
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

