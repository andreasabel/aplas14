\AgdaHide{
\begin{code}
module sn where
open import Data.Sum
open import Library
open import InfiniteTypes
open import Terms
open import Substitution
open import NReduction
\end{code}
}

Classically, a term is \emph{strongly normalizing} (sn) if there's no
infinite reduction sequence starting from it.  Constructively, the
tree of all the possible reductions from an sn term must be
well-founded, or, equivalently, an sn term must be in the accessible
part of the reduction relation.  In our case, reduction $\vt \nred n \vtprime$
is parametrized by a depth $\vn$, thus, we get the following family of $\sn$-predicates.
\begin{code}
data sn (n : ℕ) {a Γ} (t : Tm Γ a) : Set where
  acc : (∀ {t'} → t ⟨ n ⟩⇒β t' → sn n t') → sn n t
\end{code}


