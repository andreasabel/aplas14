\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}

module Subst0 where

open import Library
open import InfiniteTypes
open import Terms
import Substitution as S
\end{code}
}


\begin{code}
subst0 : ∀ {Γ a b} → Tm Γ a → Tm (a ∷ Γ) b → Tm Γ b
\end{code}
\AgdaHide{
\begin{code}
subst0 = S.subst0
\end{code}
}

