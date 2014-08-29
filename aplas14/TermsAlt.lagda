\AgdaHide{
\begin{code}
module _ where

open import Library
open import InfiniteTypes

Cxt = List Ty
data Tm (Γ : Cxt) : (a : Ty) → Set where
\end{code}
}
\begin{code}
  next  : ∀{a}    (t : Tm Γ a)                             → Tm Γ (▸ a)
  _∗_   : ∀{a b}  (t : Tm Γ (▸(a →̂ b))) (u : Tm Γ (▸ a))  → Tm Γ (▸ b)
\end{code}
