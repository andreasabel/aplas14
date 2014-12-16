\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}

module TermsTalk where

open import Library
open import InfiniteTypes

\end{code}}

\AgdaHide{
\begin{code}
Cxt = List Ty

data Var : (Γ : Cxt) (a : Ty) → Set where
  zero : ∀{Γ a}                  → Var (a ∷ Γ) a
  suc  : ∀{Γ a b} (x : Var Γ a)  → Var (b ∷ Γ) a
\end{code}
\begin{code}
v₀ : ∀ {a Γ} → Var (a ∷ Γ) a
v₀ = zero
\end{code}
}

\begin{code}
data Tm (Γ : Cxt) : (a : Ty) → Set where
  var   : ∀{a}      (x : Var Γ a)                                → Tm Γ a
  abs   : ∀{a b}    (t : Tm (a ∷ Γ) b)                           → Tm Γ (a →̂ b)
  app   : ∀{a b}    (t : Tm Γ (a →̂ b))      (u : Tm Γ a)        → Tm Γ b
  next  : ∀{a∞}     (t : Tm Γ (force a∞))                        → Tm Γ (▸̂ a∞)
  _∗_   : ∀{a∞ b∞}  (t : Tm Γ (▸̂(a∞ ⇒ b∞))) (u : Tm Γ (▸̂ a∞))  → Tm Γ (▸̂ b∞)
\end{code}
