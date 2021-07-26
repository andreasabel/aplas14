\AgdaHide{
\begin{code}

module NReduction where
open import Data.Sum
open import Library
open import InfiniteTypes
open import Terms
open import Substitution
open import NContexts public -- reexport

\end{code}
}

\begin{code}
infix 1 _⟨_⟩⇒β_
data _⟨_⟩⇒β_ {Γ} : ∀ {a} → Tm Γ a → ℕ → Tm Γ a → Set where

  β     : ∀ {n a b}{t : Tm (a ∷ Γ) b}{u}
        → app (abs t) u ⟨ n ⟩⇒β subst0 u t

  βfst  : ∀ {n a b}{t : Tm Γ a}{u : Tm Γ b}
        → fst (pair t u) ⟨ n ⟩⇒β t

  βsnd  : ∀ {n a b}{t : Tm Γ a}{u : Tm Γ b}
        → snd (pair t u) ⟨ n ⟩⇒β u

  β▸    : ∀ {n a∞ b∞}{t : Tm Γ (force a∞ →̂  force b∞)}{u : Tm Γ (force a∞)}
        → (next t ∗ next {a∞ = a∞} u) ⟨ n ⟩⇒β (next {a∞ = b∞} (app t u))

  cong  : ∀ {n n' Δ a b t t' Ct Ct'}{C : NβCxt Δ Γ a b n n'}
        → (𝑪𝒕   : Ct ≡ C [ t ])
        → (𝑪𝒕'  : Ct' ≡ C [ t' ])
        → (t⇒β  : t ⟨ n ⟩⇒β t')
        → Ct ⟨ n' ⟩⇒β Ct'
\end{code}
