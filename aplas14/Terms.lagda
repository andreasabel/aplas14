\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}

module Terms where

open import Library
open import InfiniteTypes

\end{code}}

Our encoding of well-typed terms follows closely \citet{alti:monadic,mcBride:renSubst,bentonHurKennedyMcBride:jar12}.
We represent typed variables $\vx : \Var\;\Gam\;\va$
by de Brujin indices, \ie, positions in a typing context $\Gam : \Cxt$,
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

\noindent
Arguments enclosed in braces, such as $\Gam$, $\va$, and $\vb$ in the
types of the constructors $\tzero$ and $\tsuc$, are hidden and can in
most cases be inferred by Agda.  If needed, they can be passed in
braces, either as positional arguments (\eg, \{\Del\}) or as named
arguments (\eg, \{\AgdaArgument{Γ} = \Del\}).  If ∀
prefixes bindings in a function type, the types of the bound variables
may be omitted.  Thus, ∀\{\Gam\;\va\} → A is short for \{\Gam\ :
\Cxt\}\{\va\ : \Ty\} → A.

% Terms are represented by inhabitants of $\Tm\;\Gam\;\va$
Terms $\vt : \Tm\;\Gam\;\va$ are indexed by a typing context $\Gam$
and their type $\va$,
guaranteeing well-typedness and well-scopedness.
% The syntax is mostly
% the standard one of a simply typed lambda calculus with
% products. Additionally we have the applicative functor methods of the
% later modality, i.e., the introduction \AgdaInductiveConstructor{next}
% and the operator for application under the modality
% \AgdaInductiveConstructor{\_∗\_}.
In the following data type definition, $\Tm\;(\Gam : \Cxt)$ shall mean
that all constructors uniformly take $\Gam$ as their first (hidden)
argument.

\begin{code}
data Tm (Γ : Cxt) : (a : Ty) → Set where
  var   : ∀{a}      (x : Var Γ a)                                → Tm Γ a
  abs   : ∀{a b}    (t : Tm (a ∷ Γ) b)                           → Tm Γ (a →̂ b)
  app   : ∀{a b}    (t : Tm Γ (a →̂ b))      (u : Tm Γ a)        → Tm Γ b
  pair  : ∀{a b}    (t : Tm Γ a)             (u : Tm Γ b)        → Tm Γ (a ×̂ b)
  fst   : ∀{a b}    (t : Tm Γ (a ×̂ b))                          → Tm Γ a
  snd   : ∀{a b}    (t : Tm Γ (a ×̂ b))                          → Tm Γ b
  next  : ∀{a∞}     (t : Tm Γ (force a∞))                        → Tm Γ (▸̂ a∞)
  _∗_   : ∀{a∞ b∞}  (t : Tm Γ (▸̂(a∞ ⇒ b∞))) (u : Tm Γ (▸̂ a∞))  → Tm Γ (▸̂ b∞)
\end{code}

\noindent
The most natural typing for $\anext$ and $\appli$ would be using the
defined $\AgdaFunction{▸\_}\ \AgdaSymbol{:}\ \AgdaDatatype{Ty}\ \AgdaSymbol{→}\ \AgdaDatatype{Ty}$:

\input{TermsAlt}

\noindent
However, this would lead to indices like $\hatlater\;\tdelay\;\va$ and unification
problems Agda cannot solve, since matching on a coinductive constructor like $\tdelay$ is forbidden---it can lead to a loss of subject reduction
\citep{mcBride:calco09}.
The chosen alternative typing, which parametrizes over
$\vainf\;\vbinf : \infTy$ rather than $\va\;\vb : \Ty$, works better
in practice.

\AgdaHide{
\begin{code}
-- Type annotation.

tmId : ∀ {Γ} a → Tm Γ a → Tm Γ a
tmId a t = t

syntax tmId a t = t ∶ a

\end{code}
}
