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

\begin{code}
data sn {Γ} (n : ℕ) {a} (t : Tm Γ a) : Set where
  acc : (∀ {t'} → t ⟨ n ⟩⇒β t' → sn n t') → sn n t
\end{code}

