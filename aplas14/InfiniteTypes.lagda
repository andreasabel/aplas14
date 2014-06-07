\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns #-}

module InfiniteTypes where

open import Library
\end{code}
}

In Agda~2.4, mixed coinductive-inductive types are represented by a datatype (inductive component) mutually defined with a record (coinductive component).

\begin{code}
mutual
  data Ty : Set where
    _×̂_   : (a b : Ty)  → Ty
    _→̂_   : (a b : Ty)  → Ty
    ▸̂_    : (a∞ : ∞Ty)  → Ty

  record ∞Ty : Set where
    coinductive
    constructor  delay_
    field        force_ : Ty
\end{code}

\AgdaHide{
\begin{code}
open ∞Ty public
\end{code}
}

\begin{code}
▸_ : Ty → Ty
▸ a = ▸̂ delay a

_⇒_ : (a∞ b∞ : ∞Ty) → ∞Ty
force (a∞ ⇒ b∞) = force a∞ →̂ force b∞
\end{code}


