\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}

module Terms where

open import Library
open import InfiniteTypes

\end{code}}

\subsection{Well-typed terms}

Instead of a raw syntax and a typing relation, we represent well-typed
terms directly by an inductive family
\citep{dybjer:inductiveFamilies}.
Our main motivation for this
choice is the beautiful inductive definition of strongly normalizing terms to
follow in Section~\ref{sec:sn}.  Since it relies on a classification
of terms into the three shapes \emph{introduction},
\emph{elimination}, and \emph{weak head redex}, it does not deal well with
junk terms such as $\fst (\lambda x x)$ contained in raw syntax.  Of
course, statically well-typed terms come also at cost: for almost all
our predicates on terms we need to show that they are natural in the
typing context, \ie, closed under well-typed renamings.  This expense
might be compensated by the extra assistance Agda can give us in
proof construction, which is due to the strong constraints on possible
solutions imposed by the rich typing.

Our encoding of well-typed terms follows closely \citet{alti:monadic,mcBride:renSubst,bentonHurKennedyMcBride:jar12}.
We represent variables $\vx : \Var\;\Gam\;\va$
by de Brujin indices, \ie, positions in a typing context $\Gam : \Cxt$
which is just a list of types.
% We represent variables by de Brujin indices, thus, a typing context \AgdaDatatype{Cxt} is just a list of types,
% the elements of the type \AgdaDatatype{Var} \AgdaBound{Γ} \AgdaBound{a} of variables then represent a position in such a context.
\begin{code}
Cxt = List Ty

data Var : (Γ : Cxt) (a : Ty) → Set where
  zero : ∀{Γ a}                  → Var (a ∷ Γ) a
  suc  : ∀{Γ a b} (x : Var Γ a)  → Var (b ∷ Γ) a
\end{code}

\AgdaHide{
\begin{code}
v₀ : ∀ {a Γ} → Var (a ∷ Γ) a
v₀ = zero
\end{code}
}

Terms are also indexed by a typing context and their type,
guaranteeing well-typedness and well-scopedness.  The syntax is mostly
the standard one of a simply typed lambda calculus with
products. Additionally we have the applicative functor methods of the
later modality, i.e. the introduction \AgdaInductiveConstructor{next}
and the operator for application under the modality
\AgdaInductiveConstructor{\_∗\_}.

\begin{code}
data Tm (Γ : Cxt) : (a : Ty) → Set where
  var   : ∀{a}           (x : Var Γ a)                     → Tm Γ a
  abs   : ∀{a b}         (t : Tm (a ∷ Γ) b)                → Tm Γ (a →̂ b)
  app   : ∀{a b}         (t : Tm Γ (a →̂ b)) (u : Tm Γ a)  → Tm Γ b
  pair  : ∀{a b}         (t : Tm Γ a) (u : Tm Γ b)         → Tm Γ (a ×̂ b)
  fst   : ∀{a b}         (t : Tm Γ (a ×̂ b))               → Tm Γ a
  snd   : ∀{a b}         (t : Tm Γ (a ×̂ b))               → Tm Γ b
  next  : ∀{a∞}          (t : Tm Γ (force a∞))             → Tm Γ (▸̂ a∞)
  _∗_   : ∀{a∞}{b∞}  (t : Tm Γ (▸̂  (a∞ ⇒ b∞)))
                         (u : Tm Γ (▸̂  a∞))                  → Tm Γ (▸̂ b∞)
\end{code}

\AgdaHide{
\begin{code}
-- Type annotation.

tmId : ∀ {Γ} a → Tm Γ a → Tm Γ a
tmId a t = t

syntax tmId a t = t ∶ a

\end{code}
}
