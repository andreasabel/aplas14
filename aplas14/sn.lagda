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

Classically a term is strongly normalizing if there's no infinite
reduction sequence starting from it, the type \AgdaDefinition{sn}
characterizes the same property inductively, by stating that the tree
of all the possible reductions from a strongly normalizing term is well-founded.
\begin{code}
data sn {Γ} (n : ℕ) {a} (t : Tm Γ a) : Set where
  acc : (∀ {t'} → t ⟨ n ⟩⇒β t' → sn n t') → sn n t
\end{code}


