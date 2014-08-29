\AgdaHide{
\begin{code}
module TermShape where

open import Relation.Unary using (_∈_; _⊆_)
open import Size
open import Library
open import InfiniteTypes
open import Terms
open import Substitution
\end{code}
}

\begin{code}
data ECxt (Γ : Cxt) : (a b : Ty) → Set
data _≅_[_] {Γ : Cxt} : {a b : Ty} → Tm Γ b → ECxt Γ a b → Tm Γ a → Set
\end{code}
\AgdaHide{
\begin{code}
EHole = _≅_[_]
data ECxt (Γ : Cxt) -- : (a b : Ty) → Set
 where
  appl  : ∀ {a b} (u : Tm Γ a)  → ECxt Γ (a →̂ b) b
  fst   : ∀ {a b} → ECxt Γ (a ×̂ b) a
  snd   : ∀ {a b} → ECxt Γ (a ×̂ b) b
  ∗l_   : ∀ {a∞ b∞} (u : Tm Γ (▸̂ a∞)) → ECxt Γ (▸̂ (a∞ ⇒ b∞)) (▸̂ b∞)
  ∗r_   : ∀ {a∞}{b∞} (t : Tm Γ (force a∞ →̂ force b∞)) → ECxt Γ (▸̂ a∞) (▸̂ b∞)
data _≅_[_] {Γ : Cxt} -- : {a b : Ty} → Tm Γ b → ECxt Γ a b → Tm Γ a → Set
 where
  appl  : ∀ {a b t} (u : Tm Γ a)  → EHole (app t u) (appl u) (t ∶ (a →̂ b))
  fst   : ∀ {a b t} → EHole {a = a ×̂ b} (fst t) fst t
  snd   : ∀ {a b t} → EHole {a = a ×̂ b} (snd t) snd t
  ∗l_   : ∀ {a∞ b∞ t} (u : Tm Γ (▸̂ a∞)) → EHole {a = (▸̂ (a∞ ⇒ b∞))} (t ∗ u) (∗l u) t
  ∗r_   : ∀ {a∞ b∞}{u} (t : Tm Γ (force a∞ →̂ force b∞)) → EHole (((next t) ∗ (u ∶ ▸̂ a∞)) ∶ ▸̂ b∞) (∗r t) u
\end{code}
}

$\Ehole {\vEt\,} {\,\vE} \vt$ witnesses the splitting of a term $\vEt$ into
evaluation context $\vE$ and hole content $\vt$.
%
\AgdaHide{
\begin{code}
substEC : ∀ {i vt Γ Δ a b} → (σ : RenSub {i} vt Γ Δ) → ECxt Γ a b → ECxt Δ a b
substEC σ (appl u) = appl (subst σ u)
substEC σ fst      = fst
substEC σ snd      = snd
substEC σ (∗l u)   = ∗l (subst σ u)
substEC σ (∗r t₁)  = ∗r subst σ t₁

substEh : ∀ {i vt Γ Δ a b} → (σ : RenSub {i} vt Γ Δ) → ∀ {E}{Et : Tm Γ b}{t : Tm Γ a} → (Eh : EHole Et E t)
            → EHole (subst σ Et) (substEC σ E) (subst σ t)
substEh σ (appl u) = appl (subst σ u)
substEh σ fst      = fst
substEh σ snd      = snd
substEh σ (∗l u)   = ∗l (subst σ u)
substEh σ (∗r t₁)  = ∗r subst σ t₁

mkEHole : ∀ {Γ} {a b} (E : ECxt Γ a b) {t} → Σ _ \ E[t] → EHole E[t] E t
mkEHole (appl u)  = _ , appl u
mkEHole fst       = _ , fst
mkEHole snd       = _ , snd
mkEHole (∗l u)    = _ , ∗l u
mkEHole (∗r t)    = _ , ∗r t
\end{code}
}
%
%% -- Inductive definition of strong normalization.
%
%
%% -- Parameterized evaluation contexts
%% -- Parameterized neutral terms.
%% -- Parametrized weak head reduction
%% Should we try to avoid this parametrization, for simplicity?
%% Andrea: Tried to but the termination checker didn't like it.
%
A generalization of $\Ehole \_ \_ \_$ is $\PCxt\;\vP$ which additionally
requires that all terms contained in the evaluation context (that is
one or zero terms) satisfy predicate $\vP$.  This allows us the
formulation of $\vP$-neutrals as terms of the form $\vect E[x]$ for
some $\vect E[\_] = E_1[\dots E_n[\_]]$
and a variable $x$ where all immediate subterms satisfy $\vP$.

\begin{code}
data PCxt  {Γ} (P : ∀{c} → Tm Γ c → Set) :
           ∀ {a b} → Tm Γ b → ECxt Γ a b → Tm Γ a → Set where
  appl  :  ∀ {a b t u}    (𝒖 : P u)  → PCxt P (app t u)  (appl u)  (t ∶ (a →̂ b))
  fst   :  ∀ {a b t}                 → PCxt P (fst t)    fst       (t ∶ (a ×̂ b))
  snd   :  ∀ {a b t}                 → PCxt P (snd t)    snd       (t ∶ (a ×̂ b))
  ∗l_   :  ∀ {a∞ b∞ t u}  (𝒖 : P u)  → PCxt P (t ∗ (u ∶ ▸̂ a∞) ∶ ▸̂ b∞) (∗l u) t
  ∗r_   :  ∀ {a∞ b∞ t u}  (𝒕 : P (next {a∞ = a∞ ⇒ b∞} t))
                                     → PCxt P ((next t) ∗ (u ∶ ▸̂ a∞) ∶ ▸̂ b∞) (∗r t) u

data PNe   {Γ} (P : ∀{c} → Tm Γ c → Set) {b} : Tm Γ b → Set where
  var   :  ∀  x                                   → PNe P (var x)
  elim  :  ∀  {a} {t : Tm Γ a} {E Et}
           →  (𝒏 : PNe P t) (𝑬𝒕 : PCxt P Et E t)  → PNe P Et
\end{code}

\emph{Weak head reduction} (whr) is a reduction of the form $\vect E[t] \red \vect
E[t']$ where $t \contr t'$.  It is well-known that weak head expansion (whe)
does not preserve sn, e.g., $(\lambda x.\,y) \Omega$ is not sn even
though it contracts to $y$.  In this case, $\Omega$ is a \emph{vanishing
term} lost by reduction.  If we require that all vanishing terms in a
reduction are sn, weak head expansion preserves sn.  In the following,
we define $\vP$-whr where all vanishing terms must satisfy $\vP$.

\begin{code}
data _/_⇒_  {Γ} (P : ∀{c} → Tm Γ c → Set) :
            ∀ {a} → Tm Γ a → Tm Γ a → Set where

  β     :  ∀ {a b}{t : Tm (a ∷ Γ) b}{u}
           → (𝒖 : P u)
           → P / (app (abs t) u) ⇒ subst0 u t

  βfst  :  ∀ {a b}{t : Tm Γ a}{u : Tm Γ b}
           → (𝒖 : P u)
           → P / fst (pair t u) ⇒ t

  βsnd  :  ∀ {a b}{t : Tm Γ a}{u : Tm Γ b}
           → (𝒕 : P t)
           → P / snd (pair t u) ⇒ u

  β▸    :  ∀ {a∞ b∞}{t : Tm Γ (force (a∞ ⇒ b∞))}{u : Tm Γ (force a∞)}
           → P / (next t ∗ next {a∞ = a∞} u) ⇒ (next {a∞ = b∞} (app t u))

  cong  :  ∀ {a b t t' Et Et'}{E : ECxt Γ a b}
           → (𝑬𝒕   : Et ≅ E [ t ])
           → (𝑬𝒕'  : Et' ≅ E [ t' ])
           → (t⇒   : P / t ⇒ t')
           → P / Et ⇒ Et'
\end{code}

%%%-- Weak head reduction is deterministic.
%%% Actually never used, still nice to mention?
\AgdaHide{
\begin{code}
detP⇒  :  ∀ {a Γ} {P : ∀ {c} → Tm Γ c → Set} {t t₁ t₂ : Tm Γ a}
          → (t⇒₁ : P / t ⇒ t₁) (t⇒₂ : P / t ⇒ t₂) → t₁ ≡ t₂
\end{code}
\begin{code}
detP⇒ (β _) (β _)                                              = ≡.refl
detP⇒ (β _) (cong (appl u) (appl .u) (cong () _ _))
detP⇒ β▸ β▸ = ≡.refl
detP⇒ β▸ (cong (∗l ._) (∗l ._) (cong () _ _))
detP⇒ β▸ (cong (∗r t) (∗r .t) (cong () _ _ ))
detP⇒ (βfst _) (βfst _)                                        = ≡.refl
detP⇒ (βfst _) (cong fst fst (cong () _ _))
detP⇒ (βsnd _) (βsnd _)                                        = ≡.refl
detP⇒ (βsnd 𝒕) (cong snd snd (cong () _ _))
detP⇒ (cong (appl u) (appl .u) (cong () _ _)) (β _)
detP⇒ (cong (∗l ._) (∗l ._) (cong () _ _)) β▸
detP⇒ (cong (∗r t₁) (∗r .t₁) (cong () _ _)) β▸
detP⇒ (cong fst fst (cong () _ _ )) (βfst _)
detP⇒ (cong snd snd (cong () _ _ )) (βsnd _)
detP⇒ (cong (appl u) (appl .u) x) (cong (appl .u) (appl .u) y) = ≡.cong (λ t → app t u) (detP⇒ x y)
detP⇒ (cong fst fst x) (cong fst fst y)                        = ≡.cong fst             (detP⇒ x y)
detP⇒ (cong snd snd x) (cong snd snd y)                        = ≡.cong snd             (detP⇒ x y)
detP⇒ (cong (∗l u) (∗l .u) x) (cong (∗l .u) (∗l .u) y)         = ≡.cong (λ t → t ∗ u)   (detP⇒ x y)
detP⇒ (cong (∗r t) (∗r .t) x) (cong (∗r .t) (∗r .t) y)         = ≡.cong (_∗_ (next t))     (detP⇒ x y)
detP⇒ (cong (∗l u) (∗l .u) (cong () _ _)) (cong (∗r t) (∗r .t) _)
detP⇒ (cong (∗r t) (∗r .t) _) (cong (∗l u) (∗l .u) (cong () _ _))
\end{code}
}

\AgdaHide{
\begin{code}
-- Neutrals are closed under application.

pneApp : ∀{Γ a b}{P : ∀{c} → Tm Γ c → Set}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} →
  PNe P t → P u → PNe P (app t u)
pneApp 𝒏 𝒖 = elim 𝒏 (appl 𝒖)
\end{code}
}

\AgdaHide{
%%% -- Functoriality of the notions wrt. P.
\begin{code}
mapPCxt  : ∀ {Γ} {P Q : ∀{c} → Tm Γ c → Set} (P⊆Q : ∀ {c}{t : Tm Γ c} → P t → Q t)
         {a b} {E : ECxt Γ a b} {Et t} → PCxt P Et E t → PCxt Q Et E t
mapPNe   : ∀ {Γ} {P Q : ∀{c} → Tm Γ c → Set} (P⊆Q : ∀ {c}{t : Tm Γ c} → P t → Q t)
         {a} {t : Tm Γ a} → PNe P t → PNe Q t
mapP⇒    : ∀ {Γ} {P Q : ∀{c} → Tm Γ c → Set} (P⊆Q : ∀ {c}{t : Tm Γ c} → P t → Q t)
         {a} {t t' : Tm Γ a} → P / t ⇒ t' → Q / t ⇒ t'
\end{code}
}

\AgdaHide{
\begin{code}
mapPCxt P⊆Q (appl u∈P) = appl (P⊆Q u∈P)
mapPCxt P⊆Q fst = fst
mapPCxt P⊆Q snd = snd
mapPCxt P⊆Q (∗l u∈P) = ∗l P⊆Q u∈P
mapPCxt P⊆Q (∗r t∈P) = ∗r P⊆Q t∈P

mapPNe P⊆Q (var x) = var x
mapPNe P⊆Q (elim t∈Ne E∈SNh) = elim (mapPNe P⊆Q t∈Ne) (mapPCxt P⊆Q E∈SNh)

mapP⇒ P⊆Q (β t∈P) = β (P⊆Q t∈P)
mapP⇒ P⊆Q β▸ = β▸
mapP⇒ P⊆Q (βfst t∈P) = βfst (P⊆Q t∈P)
mapP⇒ P⊆Q (βsnd t∈P) = βsnd (P⊆Q t∈P)
mapP⇒ P⊆Q (cong Et Et' t→t') = cong Et Et' (mapP⇒ P⊆Q t→t')
\end{code}
}
