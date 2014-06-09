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
_≤_  : (Δ Γ : Cxt) → Set
_≤_ Δ Γ = ∀ {a} → Var Γ a → Var Δ a

rename : ∀ {Γ Δ : Cxt} {a : Ty} (η : Δ ≤ Γ) (x : Tm Γ a) → Tm Δ a
\end{code}
\AgdaHide{
\begin{code}
rename {Γ} {Δ} = S.rename {Δ} {Γ}
\end{code}
}
