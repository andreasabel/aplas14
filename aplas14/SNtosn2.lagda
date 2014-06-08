\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}
module SNtosn2 where

open import Data.Sum
open import Library
open import InfiniteTypes
open import Terms
open import Substitution
open import TermShape
open import sn
open import SN
open import NReduction
open import NReductionProps as NR
open import Reduction
open import SNtosn
open import SNtosnR
\end{code}
}

%%% Final Proof.
\AgdaHide{
\begin{code}
mutual
\end{code}
}

To complete our strong normalization proof we need to show that
\AgdaDatatype{SN} is included in the characterization of strong
normalization as a well-founded predicate \AgdaDatatype{sn}.

\begin{code}
  fromSN    :  ∀ {i} {Γ} {n : ℕ} {a} {t : Tm Γ a} →
               SN {i} n t → sn n t
\end{code}

The cases for canonical and neutral forms are straightforward, since
no reduction can happen at the top of the expression and we cover the
others through the induction hypotheses.
\begin{code}
  fromSNe   :  ∀ {i Γ n a} {t : Tm Γ a} →
               SNe {i} n t → sn n t

  fromSN (ne 𝒏)        = fromSNe 𝒏
  fromSN (abs 𝒕)       = abssn (fromSN 𝒕)
  fromSN (pair 𝒕 𝒖)    = pairsn (fromSN 𝒕) (fromSN 𝒖)
  fromSN next0         = next0sn
  fromSN (next 𝒕)      = nextsn (fromSN 𝒕)
  fromSN (exp t⇒ 𝒕₁)   = acc (expsn t⇒ 𝒕₁ (fromSN 𝒕₁))
\end{code}
\AgdaHide{
\begin{code}
  fromSNe (elim 𝒏 𝑬)  = elimsn (fromSNe 𝒏) (mapPCxt fromSN 𝑬) 𝒏
  fromSNe (var x)     = varsn x
\end{code}
}

The expansion case is more challenging instead, we can not in fact
prove \AgdaFunction{expsn} by induction directly.

\begin{code}
  expsn     :  ∀ {i j Γ n a} {t th to : Tm Γ a} →
               i size t ⟨ n ⟩⇒ th → SN {j} n th → sn n th →
               t ⟨ n ⟩⇒β to → sn n to
\end{code}

We can see the problem by looking at one of the congruence cases, in
particular reduction on the left of an application.  There we would
have $t \, u \in sn$, $t →h t_1$ and $t →\beta t_2$, and need to prove $t_2
\, u \in sn$.  By induction we could obtain $t_2 \in sn$ but then there
would be no easy way to obtain $t_2 \, u \in sn$, since strong
normalization is not closed under application.

The solution is to instead generalize the statement to work under a
sequence of head reduction evaluation contexts.  We represent such
sequences with the type \AgdaDatatype{ECxt*}, and denote their
application to a term with the operator \AgdaFunction{\_[\_]*}.


\begin{code}
  expsnCxt  :  ∀ {i j Γ n a b} {t th to : Tm Γ a} →
               (Es : ECxt* Γ a b) → i size t ⟨ n ⟩⇒ th →
               SN {j} n (Es [ th ]*) → sn n (Es [ th ]*) →
               t ⟨ n ⟩⇒β to → sn n (Es [ to ]*)
  expsn t⇒ 𝒕 𝑡 t⇒β = expsnCxt [] t⇒ 𝒕 𝑡 t⇒β
\end{code}

In this way the congruence cases are solved just by induction with a larger context.
\begin{code}
  expsnCxt E (cong (appl u) (appl .u) th⇒) 𝒕h 𝑡h (cong (appl .u) (appl .u) t⇒)
    = expsnCxt (appl u ∷ E) th⇒ 𝒕h 𝑡h t⇒
\end{code}

This generalization however affects the lemmata that handle the
reduction cases, which also need to work under a sequence of
evaluation contexts. Fortunately the addition of a premise $E [ z ] \in
sn$, about an unrelated term $z$, allows to conveniently handle all the
reductions that target the context.

\input{SNtosnR}

\AgdaHide{
\begin{code}
  expsnCxt E (β 𝒖)    𝒕h 𝑡h β    = 𝑡h
  expsnCxt E β▸       𝒕h 𝑡h β▸   = 𝑡h
  expsnCxt E (βfst 𝒖) 𝒕h 𝑡h βfst = 𝑡h
  expsnCxt E (βsnd 𝒕) 𝒕h 𝑡h βsnd = 𝑡h

  expsnCxt E (β         𝒖) 𝒕h 𝑡h (cong (appl  u) (appl .u) (cong abs abs t⇒))
    = βsn E 𝑡h (sn⇒β (antiSubst (subexpsn E 𝑡h)) t⇒)
              (mapNβSN (cong*2 E (NR.subst⇒β (sgs u) t⇒)) 𝒕h)
              (fromSN 𝒖)
  expsnCxt E (β {t = t} 𝒖) 𝒕h 𝑡h (cong (appr ._) (appr ._)               t⇒)
    = βsn E 𝑡h (antiSubst (subexpsn E 𝑡h))
              (mapβ*SN (cong*4 E (subst⇒β* (λ { {._} zero → nβ⇒β t⇒ ∷ [] ; (suc x) → [] }) t)) 𝒕h)
              (sn⇒β (fromSN 𝒖) t⇒)

  expsnCxt E β▸       𝒕h 𝑡h (cong (∗l ._)   (∗l ._) (cong next next t⇒))
     = β▸sn E 𝑡h (sn⇒β (subsn (λ x → cong*2 E (cong next next (cong (appl _) (appl _) x))) 𝑡h) t⇒)
            (subsn (λ x → cong*2 E (cong next next (cong (appr _) (appr _) x))) 𝑡h)
            (sn⇒β 𝑡h (cong*2 E (cong next next (cong (appl _) (appl _) t⇒))))
  expsnCxt E β▸       𝒕h 𝑡h (cong (∗r ._)   (∗r ._) (cong (next {a∞ = a∞}) next t⇒))
     = β▸sn E 𝑡h (subsn (λ x → cong*2 E (cong next next (cong (appl _) (appl _) x))) 𝑡h)
            (sn⇒β (subsn (λ x → cong*2 E (cong next next (cong (appr _) (appr _) x))) 𝑡h) t⇒)
            (sn⇒β 𝑡h (cong*2 E (cong next next (cong (appr _) (appr _) t⇒))))
  expsnCxt E (βfst 𝒖) 𝒕h 𝑡h (cong fst fst (cong (pairl _) (pairl ._) t⇒)) = βfstsn E 𝑡h (sn⇒β (subexpsn E 𝑡h) t⇒) (fromSN 𝒖) (sn⇒β 𝑡h (cong*2 E t⇒))
  expsnCxt E (βfst 𝒖) 𝒕h 𝑡h (cong fst fst (cong (pairr _) (pairr ._) t⇒)) = βfstsn E 𝑡h (subexpsn E 𝑡h) (sn⇒β (fromSN 𝒖) t⇒) 𝑡h

  expsnCxt E (βsnd 𝒖) 𝒕h 𝑡h (cong snd snd (cong (pairr _) (pairr ._) t⇒)) = βsndsn E 𝑡h (sn⇒β (subexpsn E 𝑡h) t⇒) (fromSN 𝒖) (sn⇒β 𝑡h (cong*2 E t⇒))
  expsnCxt E (βsnd 𝒖) 𝒕h 𝑡h (cong snd snd (cong (pairl _) (pairl ._) t⇒)) = βsndsn E 𝑡h (subexpsn E 𝑡h) (sn⇒β (fromSN 𝒖) t⇒) 𝑡h

  expsnCxt E (cong (appl u) (appl .u) (cong () 𝑬𝒕' th⇒)) 𝒕h 𝑡h β
  expsnCxt E (cong (∗l ._)  (∗l ._)   (cong () 𝑬𝒕' th⇒)) 𝒕h 𝑡h β▸
  expsnCxt E (cong (∗r t)   (∗r .t)   (cong () 𝑬𝒕' th⇒)) 𝒕h 𝑡h β▸
  expsnCxt E (cong fst      fst       (cong () 𝑬𝒕' th⇒)) 𝒕h 𝑡h βfst
  expsnCxt E (cong snd      snd       (cong () 𝑬𝒕' th⇒)) 𝒕h 𝑡h βsnd

--  expsnCxt E (cong (appl u) (appl .u) th⇒) 𝒕h 𝑡h (cong (appl .u)    (appl .u)    t⇒) = expsnCxt (appl u ∷ E) th⇒ 𝒕h 𝑡h t⇒
  expsnCxt E (cong fst      fst       th⇒) 𝒕h 𝑡h (cong fst          fst          t⇒) = expsnCxt (fst ∷ E)    th⇒ 𝒕h 𝑡h t⇒
  expsnCxt E (cong snd      snd       th⇒) 𝒕h 𝑡h (cong snd          snd          t⇒) = expsnCxt (snd ∷ E)    th⇒ 𝒕h 𝑡h t⇒
  expsnCxt E (cong (∗l u)   (∗l .u)   th⇒) 𝒕h 𝑡h (cong (∗l .u)      (∗l .u)      t⇒) = expsnCxt (∗l u ∷ E)   th⇒ 𝒕h 𝑡h t⇒
  expsnCxt E (cong (∗r t₁)  (∗r .t₁)  th⇒) 𝒕h 𝑡h (cong (∗r .(next t₁)) (∗r .(next t₁)) t⇒) = expsnCxt (∗r t₁ ∷ E)  th⇒ 𝒕h 𝑡h t⇒

  expsnCxt E (cong (appl u) (appl .u) th⇒) 𝒕h (acc 𝑡h) (cong (appr t) (appr .t)           t⇒)
            = acc (expsnCxt [] (E [ cong (appl _) (appl _) th⇒ ]⇒*) (mapNβSN t⇒' 𝒕h) (𝑡h t⇒'))
               where t⇒' = E [ cong (appr _) (appr _)           t⇒  ]⇒β*

  expsnCxt E (cong (∗l u)   (∗l .u)   th⇒) 𝒕h (acc 𝑡h) (cong (∗r t)   (∗r .t)             t⇒)
            = acc (expsnCxt [] (E [ cong (∗l _)   (∗l _)   th⇒ ]⇒*) (mapNβSN t⇒' 𝒕h) (𝑡h t⇒'))
               where t⇒' = E [ cong (∗r _)   (∗r _)             t⇒  ]⇒β*

  expsnCxt E (cong (∗r t₁)  (∗r .t₁)  th⇒) 𝒕h (acc 𝑡h) (cong (∗l t)   (∗l .t) (cong next next t⇒))
            = acc (expsnCxt [] (E [ cong (∗r _)   (∗r _)   th⇒ ]⇒*) (mapNβSN t⇒' 𝒕h) (𝑡h t⇒'))
               where t⇒' = E [ cong (∗l _)   (∗l _) (cong next next t⇒) ]⇒β*
\end{code}
}

\begin{code}
  βsn :  ∀ {i n a b c Γ} {u : Tm Γ a} {t : Tm (a ∷ Γ) b}{z}
         (Es : ECxt* Γ b c) → sn n (Es [ z ]*) →
         sn n t → SN {i} n (Es [ subst0 u t ]*) → sn n u →
         sn n (Es [ app (abs t) u ]*)
\end{code}
\AgdaHide{
\begin{code}
  βsn Es x t t[u] u = acc (λ t⇒ → help {Es = Es} x t t[u] u (mkEhole* Es) t⇒) where
    help : ∀ {i n a b c Γ} {u : Tm Γ a} {t : Tm (a ∷ Γ) b} {t' : Tm Γ c} {x}  {z}{Es : ECxt* Γ b c} → sn n (Es [ x ]*) → sn n t →
         SN {i} n (Es [ subst (u ∷s var) t ]*) →
         sn n u → Ehole* z Es (app (abs t) u) → z ⟨ n ⟩⇒β t' → sn n t'
    help {Es = Es} x t t[u]∈sn u∈sn eq t⇒ with split Es eq β t⇒
    help x t₂ t[u]∈sn u∈sn eq t⇒ | inj₁ (._ , a₁ , β) rewrite hole*→≡ a₁ = fromSN t[u]∈sn
    help {Es = Es} x (acc t₃) t[u]∈sn u∈sn eq t⇒ | inj₁ (._ , a₁ , cong (appl u₁) (appl .u₁) (cong abs abs b₁)) rewrite hole*→≡ a₁
      = βsn Es x (t₃ b₁) (mapNβSN (cong*2 Es (NR.subst⇒β (sgs u₁) b₁)) t[u]∈sn) u∈sn
    help {t = t} {Es = Es} x t₃ t[u]∈sn (acc u∈sn) eq t⇒ | inj₁ (._ , a₁ , cong (appr ._) (appr ._) b₁) rewrite hole*→≡ a₁
      = βsn Es x t₃ (mapβ*SN (cong*4 Es
                                          (subst⇒β* (λ { {._} zero → nβ⇒β b₁ ∷ [] ; (suc n) → [] }) t)) t[u]∈sn) (u∈sn b₁)
    help {x = x} (acc f) t₂ t[u]∈sn u∈sn eq t⇒ | inj₂ (Es' , a , g) rewrite hole*→≡ a
         = βsn Es' (f (g x)) t₂ (mapNβSN (g _) t[u]∈sn) u∈sn
\end{code}
}
