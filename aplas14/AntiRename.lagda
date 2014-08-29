\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}

module AntiRename where

open import Relation.Unary using (_∈_; _⊆_)

open import Library
open import InfiniteTypes
open import Terms
open import Substitution
open import IndRen
open import SN
\end{code}
}

%%% Does it make sense to talk about IndRen if we don't show the proofs?
%%% It's mostly a technical trick to get Agda's pattern matching to do "inversion" for us.
\begin{code}
fromRenameSN   :  ∀{n a Γ Δ} (ρ : Δ ≤ Γ) {t : Tm Γ a} →
                  SN n (rename ρ t) → SN n t

\end{code}

\AgdaHide{
\begin{code}
fromRenameSN'   :  ∀{n a Γ Δ} {ρ : Δ ≤ Γ} {t : Tm Γ a} {t'} → IndRen ρ t t' →
                   SN n t' → SN n t
fromRenameSN ρ = fromRenameSN' (prop→Ind ρ ≡.refl)
fromRenameSNe  :  ∀{n a Γ Δ} {ρ : Δ ≤ Γ} {t : Tm Γ a}{t'} → IndRen ρ t t' →
                  SNe n t' → SNe n t

fromRename⇒0 : ∀{n a Γ Δ} {ρ : Δ ≤ Γ} {t : Tm Γ a} {t' : Tm Δ a}{tρ} → IndRen ρ t tρ
              → tρ ⟨ n ⟩⇒ t' → Σ _ \ s → IndRen ρ s t'
fromRename⇒1 : ∀{n a Γ Δ} {ρ : Δ ≤ Γ} {t : Tm Γ a} {t' : Tm Δ a}{tρ} → (is : IndRen ρ t tρ)
              → (t⇒ : tρ ⟨ n ⟩⇒ t') → t ⟨ n ⟩⇒ proj₁ (fromRename⇒0 is t⇒)
fromRenameSNe (var x x₁)     (var y)           = var x
fromRenameSNe (app is is₁)   (elim 𝒏 (appl 𝒖)) = elim (fromRenameSNe is 𝒏) (appl (fromRenameSN' is₁ 𝒖))
fromRenameSNe (fst is)       (elim 𝒏 fst)      = elim (fromRenameSNe is 𝒏) fst
fromRenameSNe (snd is)       (elim 𝒏 snd)      = elim (fromRenameSNe is 𝒏) snd
fromRenameSNe (is ∗ is₁)     (elim 𝒏 (∗l 𝒖))   = elim (fromRenameSNe is 𝒏) (∗l (fromRenameSN' is₁ 𝒖))
fromRenameSNe ((next is) ∗ is₁) (elim 𝒏 (∗r 𝒕))   = elim (fromRenameSNe is₁ 𝒏) (∗r fromRenameSN' (next is) 𝒕)

-- variable case:
fromRenameSN' (var x _)    (ne (var y)) = ne (var x)
-- constructor cases:
fromRenameSN' (abs t)      (abs 𝒕)      = abs (fromRenameSN' t 𝒕)
fromRenameSN' (pair t₁ t₂) (pair 𝒕₁ 𝒕₂) = pair (fromRenameSN' t₁ 𝒕₁) (fromRenameSN' t₂ 𝒕₂)
fromRenameSN' (next _)        next0           = next0
fromRenameSN' (next t)        (next 𝒕)        = next (fromRenameSN' t 𝒕)
-- neutral cases:
fromRenameSN' n            (ne 𝒏)       = ne (fromRenameSNe n 𝒏)
-- redex cases:
fromRenameSN' is           (exp t⇒ 𝒕)   = exp (fromRename⇒1 is t⇒) (fromRenameSN' (proj₂ (fromRename⇒0 is t⇒)) 𝒕)

fromRename⇒0 {ρ = ρ} (app {u = u} (abs {t = t} is) is₁)  (β 𝒖)  = _ , prop→Ind ρ (≡.trans (≡.sym (sgs-lifts-term {σ = ρ} {u = u} {t = t}))
                                                                    (≡.cong₂ (λ t₁ u₁ → subst (sgs u₁) t₁) (Ind→prop _ is) (Ind→prop _ is₁)))
fromRename⇒0 ((next is) ∗ (next is₁))  β▸    = next (app _ _) , (next (app is is₁))
fromRename⇒0 (fst (pair is is₁)) (βfst 𝒖) = _ , is
fromRename⇒0 (snd (pair is is₁)) (βsnd 𝒕) = _ , is₁
fromRename⇒0 (app is is₁)        (cong (appl u) (appl .u) tρ→t') = let s , iss = fromRename⇒0 is tρ→t' in app s _ , app iss is₁
fromRename⇒0 (fst is)            (cong fst fst tρ→t') = let s , iss = fromRename⇒0 is tρ→t' in fst s , fst iss
fromRename⇒0 (snd is)            (cong snd snd tρ→t') = let s , iss = fromRename⇒0 is tρ→t' in snd s , snd iss
fromRename⇒0 (is ∗ is₁)          (cong (∗l u) (∗l .u) tρ→t')   = let s , iss = fromRename⇒0 is tρ→t' in s ∗ _ , iss ∗ is₁
fromRename⇒0 (is ∗ is₁)          (cong (∗r t₂) (∗r .t₂) tρ→t') = let s , iss = fromRename⇒0 is₁ tρ→t' in _ ∗ s , is ∗ iss

fromRename⇒1 (app (abs is) is₁) (β 𝒖) = β (fromRenameSN' is₁ 𝒖)
fromRename⇒1 ((next is) ∗ (next is₁))  β▸   = β▸
fromRename⇒1 (fst (pair is is₁)) (βfst 𝒖) = βfst (fromRenameSN' is₁ 𝒖)
fromRename⇒1 (snd (pair is is₁)) (βsnd 𝒕) = βsnd (fromRenameSN' is 𝒕)
fromRename⇒1 (app is is₁)        (cong (appl u) (appl .u) tρ→t') = cong (appl _) (appl _) (fromRename⇒1 is tρ→t')
fromRename⇒1 (fst is)            (cong fst fst tρ→t') = cong fst fst (fromRename⇒1 is tρ→t')
fromRename⇒1 (snd is)            (cong snd snd tρ→t') = cong snd snd (fromRename⇒1 is tρ→t')
fromRename⇒1 (is ∗ is₁)          (cong (∗l u) (∗l .u) tρ→t')   = cong (∗l _) (∗l _) (fromRename⇒1 is tρ→t')
fromRename⇒1 ((next is) ∗ is₁)      (cong (∗r t₂) (∗r .t₂) tρ→t') = cong (∗r _) (∗r _) (fromRename⇒1 is₁ tρ→t')
\end{code}
}

A consequence of \AgdaFunction{fromRenameSN} is that $t \in \SN\;\vn$
iff $t\;x \in \SN\;\vn$ for some variable $x$.
(Consider $t = \lambda y.\, t'$ and $t\;x \nwhr n \subst y x {t'}$.)
This property is
essential for the construction of the function space on sn sets
(see next section).

\begin{code}
absVarSN   :   ∀{Γ a b n}{t : Tm (a ∷ Γ) (a →̂ b)} →
               app t (var zero) ∈ SN n → t ∈ SN n
\end{code}

\AgdaHide{
\begin{code}
absVarSNe  :   ∀{Γ a b n}{t : Tm (a ∷ Γ) (a →̂ b)} →
               app t (var zero) ∈ SNe n → t ∈ SNe n
absVarSNe (elim 𝒏 (appl 𝒖)) = 𝒏

absVarSN (ne 𝒖)                                                   = ne (absVarSNe 𝒖)
absVarSN (exp (β {t = t} 𝒖) 𝒕′)                                   = abs (fromRenameSN' (prop→Ind contract (subst-ext contract-sgs t)) 𝒕′)
absVarSN (exp (cong (appl ._) (appl ._) t⇒) 𝒕′) = exp t⇒ (absVarSN 𝒕′)
\end{code}
}

