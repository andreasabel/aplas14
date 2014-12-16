\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns #-}

module TypesTalk where

open import Library
\end{code}
}

\begin{code}
mutual
  data Ty : Set where
    _→̂_   : (a b : Ty)  → Ty
    ▸̂_    : (a∞ : ∞Ty)  → Ty

  record ∞Ty : Set where
    coinductive
    constructor  delay_
    field        force_ : Ty
\end{code}
