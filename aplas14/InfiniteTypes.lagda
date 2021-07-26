\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns #-}

module InfiniteTypes where

open import Library
\end{code}
}

In Agda~2.4, we represent this mixed coinductive-inductive type by a
datatype $\Ty$ (inductive component) mutually defined with a record
$\infTy$ (coinductive component).

\begin{code}
mutual
  data Ty : Set where
    _×̂_   : (a b : Ty)  → Ty
    _→̂_   : (a b : Ty)  → Ty
    ▸̂_    : (a∞ : ∞Ty)  → Ty

  record ∞Ty : Set where
    coinductive
    constructor  delay_
    field        force_ : Ty
\end{code}
\AgdaHide{
\begin{code}
    infixr 30 force_
  infixr 30 delay_
  infixr 25 ▸̂_
open ∞Ty public
\end{code}
}

\noindent
While the arguments $\va$ and $\vb$ of the infix constructors
$\hattimes$ and $\hatto$ are again in $\Ty$, the prefix constructor
$\hatlater$ expects and argument $\vainf$ in $\infTy$, which is
basically a wrapping\footnote{Similar to a \texttt{newtype}
  in the functional programming language Haskell.}
of $\Ty$.
The functions $\tdelay$ and $\tforce$ convert back and forth between $\Ty$ and $\infTy$ so that both types
are valid representations of the set of types of $\lambdalater$.
\[
\begin{array}{lll}
  \tdelay & : & \Ty \to \infTy \\
  \tforce & : & \infTy \to \Ty \\
\end{array}
\]
However, since $\infTy$ is declared $\tcoinductive$, its inhabitants
are not evaluated until $\tforce$d.  This allows us to represent
infinite type expressions, like $\ttop = \hatmu X (\hatlater X)$.

\begin{code}
top : ∞Ty
force top = ▸̂ top
\end{code}

\noindent
Technically, $\ttop$ is defined by \emph{copattern} matching
\citep{abelPientkaThibodeauSetzer:popl13}; $\ttop$ is uniquely defined
by the value of its only field, $\tforce\;\ttop$, which is given as
$\hatlater \ttop$.  Agda will use the given equation for its
internal normalization procedure during type-checking.  Alternatively,
we could have tried to define $\ttop : \Ty$ by $\ttop = \hatlater
\tdelay\; \ttop$.  However, Agda will rightfully complain here since rewriting with
this equation would keep expanding $\ttop$ forever, thus, be non-terminating.
In contrast, rewriting with
the original equation is terminating since at each step, one
application of $\tforce$ is removed.

The following two defined type constructors will prove useful in the
definition of well-typed terms to follow.
\begin{code}
▸_ : Ty → Ty
▸ a = ▸̂ delay a

_⇒_ : (a∞ b∞ : ∞Ty) → ∞Ty
force (a∞ ⇒ b∞) = force a∞ →̂ force b∞
\end{code}
\AgdaHide{
\begin{code}
infixr 25 ▸_
\end{code}
}
