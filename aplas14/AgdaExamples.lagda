\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}

module AgdaExamples where

open import Library
open import InfiniteTypes
open import Terms
open import TypeEquality
\end{code}
}


We can adapt the Y combinator from the untyped lambda calculus to
define a guarded fixed point combinator.  The type \AgdaFunction{Fix}
\AgdaBound{A} allows safe self application, since the input will only
be available "later". This fits with the type we want for the
\AgdaFunction{fix} combinator, the function of which we are taking the
fixed point will only be able to use its input in the next time slot.

\begin{code}
Fix_ : Ty → ∞Ty
force Fix A = ▸̂ Fix A →̂ A

omega : ∀{Γ A} → Tm Γ (▸̂ Fix A) → Tm Γ (▸ A)
omega x = ▸app (≅delay ≅refl) x (next x)

fix : ∀{Γ A} → Tm Γ ((▸ A →̂ A) →̂ A)
fix = abs (app L (next L))
  where
    f = var (suc v₀)
    x = var v₀
    L = abs (app f (omega x))
\end{code}

The definition above correponds to the following with named variables.
\begin{verbatim}
fix = λ f. (λ x. f (omega x)) (next (λ x. f (omega x)))
\end{verbatim}

Another standard example is the type of streams, which we can also
define through corecursion.
\begin{code}
mutual
  Stream : Ty → Ty
  Stream A = A ×̂ ▸̂ Stream∞ A

  Stream∞ : Ty → ∞Ty
  force (Stream∞ A) = Stream A

cons : ∀{Γ A} → Tm Γ A → Tm Γ (▸ Stream A) → Tm Γ (Stream A)
cons a s = pair a (cast (▸̂ (≅delay ≅refl)) s)

head : ∀{Γ A} → Tm Γ (Stream A) → Tm Γ A
head s = fst s

tail : ∀{Γ A} → Tm Γ (Stream A) → Tm Γ (▸ Stream A)
tail s = cast (▸̂ (≅delay ≅refl)) (snd s)
\end{code}

Note that \AgdaFunction{tail} returns a stream inside the later
modality.  This ensures that functions that transform streams have to
be causal, i.e. can only have access to the first $n$ elements of the
input when producing the $n$th element of the output.
A simple example is mapping a function over a stream.
\begin{code}
mapS : ∀{Γ A B} → Tm Γ ((A →̂ B) →̂ (Stream A →̂ Stream B))
\end{code}
\AgdaHide{
\begin{code}
mapS = TODO
\end{code}
}
\begin{verbatim}
mapS = λ f. fix λ mapS s. pair (f s) (▸app (≅delay ≅refl) mapS (tail s))
\end{verbatim}

