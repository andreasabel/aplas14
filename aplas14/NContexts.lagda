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


\begin{code}
data NβECxt (Γ : Cxt) : (Δ : Cxt) (a b : Ty) → (n n' : ℕ) → Set where
  next   : ∀ {n a∞}                               → NβECxt Γ Γ (force a∞) (▸̂  a∞) n (suc n)
  appl   : ∀ {n a b} (u : Tm Γ a)                 → NβECxt Γ Γ (a →̂ b) b n n
  appr   : ∀ {n a b} (t : Tm Γ (a →̂  b))         → NβECxt Γ Γ a b n n
  pairl  : ∀ {n a b} (u : Tm Γ b)                 → NβECxt Γ Γ a (a ×̂ b) n n
  pairr  : ∀ {n a b} (t : Tm Γ a)                 → NβECxt Γ Γ b (a ×̂ b) n n
  fst    : ∀ {n a b}                              → NβECxt Γ Γ (a ×̂ b) a n n
  snd    : ∀ {n a b}                              → NβECxt Γ Γ (a ×̂ b) b n n
  _∗l    : ∀ {n a∞ b∞} (u : Tm Γ (▸̂ a∞))         → NβECxt Γ Γ (▸̂ (a∞ ⇒ b∞)) (▸̂ b∞) n n
  ∗r_    : ∀ {n a∞ b∞} (t : Tm Γ (▸̂ (a∞ ⇒ b∞)))  → NβECxt Γ Γ (▸̂ a∞) (▸̂ b∞) n n
  abs    : ∀ {n a b}                              → NβECxt Γ (a ∷ Γ) b (a →̂  b) n n
\end{code}

\begin{code}
data NβEhole  {n : ℕ} {Γ : Cxt} : {n' : ℕ} {Δ : Cxt} {b a : Ty} →
              Tm Γ b → NβECxt Γ Δ a b n n' → Tm Δ a → Set where
\end{code}
\AgdaHide{
\begin{code}
  appl  : ∀ {a b t} (u : Tm Γ a)                          → NβEhole (app t u) (appl u) (t ∶ (a →̂ b))
  appr  : ∀ {a b u} (t : Tm Γ (a →̂  b))                   → NβEhole (app t u) (appr t) u
  pairl : ∀ {a b}{t} (u : Tm Γ b)                         → NβEhole (pair t u) (pairl u) (t ∶ a)
  pairr : ∀ {a b}{u} (t : Tm Γ a)                         → NβEhole (pair t u) (pairr t) (u ∶ b)
  fst   : ∀ {a b t}                                       → NβEhole {a = a ×̂ b} (fst t) fst t
  snd   : ∀ {a b t}                                       → NβEhole {a = a ×̂ b} (snd t) snd t
  _∗l   : ∀ {a∞ b∞ t} (u : Tm Γ (▸̂ a∞))                     → NβEhole {a = (▸̂ (a∞ ⇒ b∞))} (t ∗ u) (u ∗l) t
  ∗r_   : ∀ {a∞ b∞}{u} (t : Tm Γ (▸̂ (a∞ ⇒ b∞))) → NβEhole ((t ∗ (u ∶ ▸̂ a∞)) ∶ ▸̂ b∞) (∗r t) u
  abs   : ∀ {a b} {t : Tm (a ∷ Γ) b}                      → NβEhole (abs t) abs t
  next  : ∀ {a∞} {t : Tm Γ (force a∞)}                    → NβEhole (next {a∞ = a∞} t) next t
\end{code}
}

\AgdaHide{
\begin{code}
mkHole : ∀ {n n' Γ Δ} {a b} (E : NβECxt Γ Δ a b n n') {t} → Σ _ \ E[t] → NβEhole E[t] E t
mkHole (appl u)  = _ , appl u
mkHole (appr t)  = _ , appr t
mkHole (pairl u) = _ , pairl u
mkHole (pairr t) = _ , pairr t
mkHole fst       = _ , fst
mkHole snd       = _ , snd
mkHole (u ∗l)    = _ , u ∗l
mkHole (∗r t)    = _ , ∗r t
mkHole abs       = _ , abs
mkHole next        = _ , next
\end{code}
}
