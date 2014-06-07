\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}

module AgdaExamples where

open import Library
open import InfiniteTypes
open import Terms
\end{code}
}

Which terms are accepted by this well-typed syntax is affected by
which types are considered equal.  Unfortunately Agda's own notion of
equality is too intensional, we can however define bisimulation
explicitly as a coinductive type, and prove it is in fact an
equivalence relation.

\begin{code}
mutual
  data _≅_ : (a b : Ty) → Set where
    _×̂_  : ∀{a a' b b'} (a≅ : a ≅ a') (b≅ : b ≅ b')  → (a ×̂ b) ≅ (a' ×̂ b')
    _→̂_  : ∀{a a' b b'} (a≅ : a' ≅ a) (b≅ : b ≅ b')  → (a →̂ b) ≅ (a' →̂ b')
    ▸̂_   : ∀{a∞ b∞}     (a≅ : a∞ ∞≅ b∞)              → ▸̂ a∞    ≅ ▸̂ b∞

  record _∞≅_ (a∞ b∞ : ∞Ty) : Set where
    coinductive
    constructor  ≅delay
    field        ≅force : force a∞ ≅ force b∞
open _∞≅_ public
\end{code}
\begin{code}
≅refl  : ∀{a}     → a ≅ a
≅sym   : ∀{a b}   → a ≅ b → b ≅ a
≅trans : ∀{a b c} → a ≅ b → b ≅ c → a ≅ c
\end{code}

\AgdaHide{
\begin{code}

≅refl∞ : ∀{a∞} → a∞ ∞≅ a∞

≅refl {a ×̂ b}  = (≅refl {a}) ×̂ (≅refl {b})
≅refl {a →̂ b}  = (≅refl {a}) →̂ (≅refl {b})
≅refl {▸̂ a∞ }  = ▸̂ (≅refl∞ {a∞})

≅force ≅refl∞ = ≅refl

≅sym∞ : ∀{a∞ b∞} → a∞ ∞≅ b∞ → b∞ ∞≅ a∞

≅sym (eq ×̂ eq₁)  = (≅sym eq) ×̂ (≅sym eq₁)
≅sym (eq →̂ eq₁)  = (≅sym eq) →̂ (≅sym eq₁)
≅sym (▸̂ a≅)      = ▸̂ (≅sym∞ a≅)

≅force (≅sym∞ eq) = ≅sym (≅force eq)

≅trans∞ : ∀{a∞ b∞ c∞} → a∞ ∞≅ b∞ → b∞ ∞≅ c∞ → a∞ ∞≅ c∞

≅trans (eq₁ ×̂ eq₂) (eq₁' ×̂ eq₂')  = (≅trans eq₁ eq₁') ×̂ (≅trans eq₂ eq₂')
≅trans (eq₁ →̂ eq₂) (eq₁' →̂ eq₂')  = (≅trans eq₁' eq₁) →̂ (≅trans eq₂ eq₂')
≅trans (▸̂ eq) (▸̂ eq')             = ▸̂ (≅trans∞ eq eq')

≅force (≅trans∞ eq eq') = ≅trans (≅force eq) (≅force eq')
\end{code}
} % END AGDAHIDE

It is consistent to postulate that bisimulation implies equality,
similarly to the functional extensionality principle for function
types. The alternative would be to work with setoids across all our
development, which would add complexity without strengthening our result.
\begin{code}
postulate
  ≅-to-≡ : ∀ {a b} → a ≅ b → a ≡ b
\end{code}

This let us define the function cast to convert terms between
bisimilar types, and a variant of application under later with a more
general type.
\begin{code}
cast : ∀{Γ a b} (eq : a ≅ b) (t : Tm Γ a) → Tm Γ b
\end{code}
\AgdaHide{
\begin{code}
cast = TODO
\end{code}
}
\begin{code}
▸app : ∀{Γ c∞ b∞}{a : Ty} (eq : c∞ ∞≅ (delay a ⇒ b∞))
                          (t : Tm Γ (▸̂ c∞)) (u : Tm Γ (▸ a)) → Tm Γ (▸̂ b∞)
▸app eq t u = cast (▸̂ eq) t ∗ u
\end{code}


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
define through a corecursive definition.
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

