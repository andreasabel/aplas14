\AgdaHide{
\begin{code}

module NContexts where
open import Data.Sum
open import Library
open import InfiniteTypes
open import Terms
open import Substitution

\end{code}
}

\begin{small}
\begin{code}
data NβCxt : (Δ Γ : Cxt) (a b : Ty) (n n' : ℕ) → Set where
  abs    :  ∀  {Γ n a b}                         → NβCxt (a ∷ Γ) Γ b (a →̂  b) n n
  appl   :  ∀  {Γ n a b} (u  : Tm Γ a)           → NβCxt Γ Γ (a →̂ b) b n n
  appr   :  ∀  {Γ n a b} (t  : Tm Γ (a →̂ b))    → NβCxt Γ Γ a b n n
  pairl  :  ∀  {Γ n a b} (u  : Tm Γ b)           → NβCxt Γ Γ a (a ×̂ b) n n
  pairr  :  ∀  {Γ n a b} (t  : Tm Γ a)           → NβCxt Γ Γ b (a ×̂ b) n n
  fst    :  ∀  {Γ n a b}                         → NβCxt Γ Γ (a ×̂ b) a n n
  snd    :  ∀  {Γ n a b}                         → NβCxt Γ Γ (a ×̂ b) b n n
  next   :  ∀  {Γ n a∞}                          → NβCxt Γ Γ (force a∞) (▸̂ a∞) n (1 + n)
  ∗l_    :  ∀  {Γ n a∞ b∞} (u : Tm Γ (▸̂ a∞))    → NβCxt Γ Γ (▸̂ (a∞ ⇒ b∞)) (▸̂ b∞) n n
  ∗r_    :  ∀  {Γ n a∞ b∞}
               (t : Tm Γ (▸̂ (a∞ ⇒ b∞)))         → NβCxt Γ Γ (▸̂ a∞) (▸̂ b∞) n n
\end{code}
\begin{code}
data NβHole  {n : ℕ} {Γ : Cxt} : {n' : ℕ} {Δ : Cxt} {b a : Ty} →
             Tm Γ b → NβCxt Δ Γ a b n n' → Tm Δ a → Set
\end{code}
\end{small}
\AgdaHide{
\begin{code}
 where
  appl  : ∀ {a b t} (u : Tm Γ a)                          → NβHole (app t u) (appl u) (t ∶ (a →̂ b))
  appr  : ∀ {a b u} (t : Tm Γ (a →̂ b))                   → NβHole (app t u) (appr t) u
  pairl : ∀ {a b}{t} (u : Tm Γ b)                         → NβHole (pair t u) (pairl u) (t ∶ a)
  pairr : ∀ {a b}{u} (t : Tm Γ a)                         → NβHole (pair t u) (pairr t) (u ∶ b)
  fst   : ∀ {a b t}                                       → NβHole {a = a ×̂ b} (fst t) fst t
  snd   : ∀ {a b t}                                       → NβHole {a = a ×̂ b} (snd t) snd t
  ∗l_   : ∀ {a∞ b∞ t} (u : Tm Γ (▸̂ a∞))                     → NβHole {a = (▸̂ (a∞ ⇒ b∞))} (t ∗ u) (∗l u) t
  ∗r_   : ∀ {a∞ b∞}{u} (t : Tm Γ (▸̂ (a∞ ⇒ b∞))) → NβHole ((t ∗ (u ∶ ▸̂ a∞)) ∶ ▸̂ b∞) (∗r t) u
  abs   : ∀ {a b} {t : Tm (a ∷ Γ) b}                      → NβHole (abs t) abs t
  next  : ∀ {a∞} {t : Tm Γ (force a∞)}                    → NβHole (next {a∞ = a∞} t) next t
\end{code}
}

\AgdaHide{
\begin{code}
mkHole : ∀ {n n' Γ Δ} {a b} (E : NβCxt Γ Δ a b n n') {t} → Σ _ \ E[t] → NβHole E[t] E t
mkHole (appl u)  = _ , appl u
mkHole (appr t)  = _ , appr t
mkHole (pairl u) = _ , pairl u
mkHole (pairr t) = _ , pairr t
mkHole fst       = _ , fst
mkHole snd       = _ , snd
mkHole (∗l u)    = _ , ∗l u
mkHole (∗r t)    = _ , ∗r t
mkHole abs       = _ , abs
mkHole next        = _ , next
\end{code}
}
