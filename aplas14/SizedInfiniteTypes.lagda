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


