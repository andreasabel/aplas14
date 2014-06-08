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


We can adapt the $Y$ combinator from the untyped lambda calculus to
define a guarded fixed point combinator.  The type \AgdaFunction{Fix}
\va{} allows safe self application, since the input will only
be available "later". This fits with the type we want for the
\AgdaFunction{fix} combinator, the function of which we are taking the
fixed point will only be able to use its input in the next time slot.

\begin{code}
Fix_ : Ty → ∞Ty
force (Fix a) = ▸̂ Fix a →̂ a

selfApp : ∀{Γ a} → Tm Γ (▸̂ Fix a) → Tm Γ (▸ a)
selfApp x = ▸app (≅delay ≅refl) x (next x)

fix : ∀{Γ a} → Tm Γ ((▸ a →̂ a) →̂ a)
fix = abs (app L (next L))
  where
    f = var (suc zero)
    x = var zero
    L = abs (app f (selfApp x))
\end{code}

The definition above correponds to the following with named variables.
\begin{verbatim}
fix = λ f. (λ x. f (selfApp x)) (next (λ x. f (selfApp x)))
\end{verbatim}

Another standard example is the type of streams, which we can also
define through corecursion.
\begin{code}
mutual
  Stream : Ty → Ty
  Stream a = a ×̂ ▸̂ Stream∞ a

  Stream∞ : Ty → ∞Ty
  force (Stream∞ a) = Stream a

cons : ∀{Γ a} → Tm Γ a → Tm Γ (▸ Stream a) → Tm Γ (Stream a)
cons a s = pair a (cast (▸̂ (≅delay ≅refl)) s)

head : ∀{Γ a} → Tm Γ (Stream a) → Tm Γ a
head s = fst s

tail : ∀{Γ a} → Tm Γ (Stream a) → Tm Γ (▸ Stream a)
tail s = cast (▸̂ (≅delay ≅refl)) (snd s)
\end{code}

Note that \AgdaFunction{tail} returns a stream inside the later
modality.  This ensures that functions that transform streams have to
be causal, i.e. can only have access to the first $n$ elements of the
input when producing the $n$th element of the output.
A simple example is mapping a function over a stream.
\begin{code}
mapS : ∀{Γ a b} → Tm Γ ((a →̂ b) →̂ (Stream a →̂ Stream b))
\end{code}
\AgdaHide{
\begin{code}
mapS = abs (app fix (abs (abs
  (let f   = var (suc (suc v₀))
       map = var (suc v₀)
       s   = var v₀
   in pair (app f (head s)) (▸app (≅delay ≅refl) map (tail s))))))
\end{code}
}
\begin{verbatim}
mapS = λ f. fix λ mapS s. pair (f s) (▸app (≅delay ≅refl) mapS (tail s))
\end{verbatim}

