\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}

module Rename where

open import Library
open import InfiniteTypes
open import Terms
import Substitution as S
\end{code}
}

\begin{code}
_≤_  : (Γ Δ : Cxt) → Set
_≤_ Γ Δ = ∀ {a} → Var Δ a → Var Γ a

rename : ∀ {Γ Δ : Cxt} {a : Ty} (η : Γ ≤ Δ) (x : Tm Δ a) → Tm Γ a
\end{code}
\AgdaHide{
\begin{code}
rename = S.rename
\end{code}
}
