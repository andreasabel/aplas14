\begin{code}
module NoConfluence where

open import Library
open import SizedInfiniteTypes
open import Terms
open import NReduction
open import Data.Empty
\end{code}

We show a term t with two distinct normal forms, t11 and t2, when only
reducing at a fixed depth (0 in this case).
This happens because the lambda in t = (λ x. next x) (fst (y , y))
"hides" its argument under a next where it's unreachable after beta
reduction.

A possible workaround could be the use of explicit substitutions, to
keep the substituted argument out of the next.

\begin{code}
module _ {a : Ty} where
  arg : Tm (a ∷ []) a
  arg = (fst (pair (var zero) (var zero)))

  t t1 t11 t2 : Tm (a ∷ []) (▸̂  (delay a))
  t = app (abs (▹ (var zero))) arg

  t1 = app (abs (▹ var zero)) (var zero)
  red1 : t ⟨ 0 ⟩⇒β t1
  red1 = cong (appr _) (appr _) βfst

  t11 = ▹ var zero
  red3 : t1 ⟨ 0 ⟩⇒β t11
  red3 = β 

  t2 = ▹ fst (pair (var zero) (var zero))
  red2 : t ⟨ 0 ⟩⇒β t2
  red2 = β

  nf-t11 : ∀ {z} → t11 ⟨ 0 ⟩⇒β z -> ⊥
  nf-t11 (cong () 𝑬𝒕' _)

  nf-t2 : ∀ {z} → t2 ⟨ 0 ⟩⇒β z -> ⊥
  nf-t2 (cong () 𝑬𝒕' _)
\end{code}