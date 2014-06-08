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
unRenameSNe  :  ∀{n a Γ Δ} {ρ : Δ ≤ Γ} {t : Tm Γ a}{t'} → IndRen ρ t t' →
                SNe n t' → SNe n t

unRenameSN   :  ∀{n a Γ Δ} {ρ : Δ ≤ Γ} {t : Tm Γ a} {t'} → IndRen ρ t t' →
                SN n t' → SN n t
\end{code}

\AgdaHide{
\begin{code}
unRename⇒0 : ∀{n a Γ Δ} {ρ : Δ ≤ Γ} {t : Tm Γ a} {t' : Tm Δ a}{tρ} → IndRen ρ t tρ
            → tρ ⟨ n ⟩⇒ t' → Σ _ \ s → IndRen ρ s t'
unRename⇒1 : ∀{n a Γ Δ} {ρ : Δ ≤ Γ} {t : Tm Γ a} {t' : Tm Δ a}{tρ} → (is : IndRen ρ t tρ)
            → (t⇒ : tρ ⟨ n ⟩⇒ t') → t ⟨ n ⟩⇒ proj₁ (unRename⇒0 is t⇒)
unRenameSNe (var x x₁)     (var y)           = var x
unRenameSNe (app is is₁)   (elim 𝒏 (appl 𝒖)) = elim (unRenameSNe is 𝒏) (appl (unRenameSN is₁ 𝒖))
unRenameSNe (fst is)       (elim 𝒏 fst)      = elim (unRenameSNe is 𝒏) fst
unRenameSNe (snd is)       (elim 𝒏 snd)      = elim (unRenameSNe is 𝒏) snd
unRenameSNe (is ∗ is₁)     (elim 𝒏 (∗l 𝒖))   = elim (unRenameSNe is 𝒏) (∗l (unRenameSN is₁ 𝒖))
unRenameSNe ((next is) ∗ is₁) (elim 𝒏 (∗r 𝒕))   = elim (unRenameSNe is₁ 𝒏) (∗r unRenameSN (next is) 𝒕)

-- variable case:
unRenameSN (var x _)    (ne (var y)) = ne (var x)
-- constructor cases:
unRenameSN (abs t)      (abs 𝒕)      = abs (unRenameSN t 𝒕)
unRenameSN (pair t₁ t₂) (pair 𝒕₁ 𝒕₂) = pair (unRenameSN t₁ 𝒕₁) (unRenameSN t₂ 𝒕₂)
unRenameSN (next _)        next0           = next0
unRenameSN (next t)        (next 𝒕)        = next (unRenameSN t 𝒕)
-- neutral cases:
unRenameSN n            (ne 𝒏)       = ne (unRenameSNe n 𝒏)
-- redex cases:
unRenameSN is           (exp t⇒ 𝒕)   = exp (unRename⇒1 is t⇒) (unRenameSN (proj₂ (unRename⇒0 is t⇒)) 𝒕)

unRename⇒0 {ρ = ρ} (app {u = u} (abs {t = t} is) is₁)  (β 𝒖)  = _ , prop→Ind ρ (≡.trans (≡.sym (sgs-lifts-term {σ = ρ} {u = u} {t = t}))
                                                                    (≡.cong₂ (λ t₁ u₁ → subst (sgs u₁) t₁) (Ind→prop _ is) (Ind→prop _ is₁)))
unRename⇒0 ((next is) ∗ (next is₁))  β▸    = next (app _ _) , (next (app is is₁))
unRename⇒0 (fst (pair is is₁)) (βfst 𝒖) = _ , is
unRename⇒0 (snd (pair is is₁)) (βsnd 𝒕) = _ , is₁
unRename⇒0 (app is is₁)        (cong (appl u) (appl .u) tρ→t') = let s , iss = unRename⇒0 is tρ→t' in app s _ , app iss is₁
unRename⇒0 (fst is)            (cong fst fst tρ→t') = let s , iss = unRename⇒0 is tρ→t' in fst s , fst iss
unRename⇒0 (snd is)            (cong snd snd tρ→t') = let s , iss = unRename⇒0 is tρ→t' in snd s , snd iss
unRename⇒0 (is ∗ is₁)          (cong (∗l u) (∗l .u) tρ→t')   = let s , iss = unRename⇒0 is tρ→t' in s ∗ _ , iss ∗ is₁
unRename⇒0 (is ∗ is₁)          (cong (∗r t₂) (∗r .t₂) tρ→t') = let s , iss = unRename⇒0 is₁ tρ→t' in _ ∗ s , is ∗ iss

unRename⇒1 (app (abs is) is₁) (β 𝒖) = β (unRenameSN is₁ 𝒖)
unRename⇒1 ((next is) ∗ (next is₁))  β▸   = β▸
unRename⇒1 (fst (pair is is₁)) (βfst 𝒖) = βfst (unRenameSN is₁ 𝒖)
unRename⇒1 (snd (pair is is₁)) (βsnd 𝒕) = βsnd (unRenameSN is 𝒕)
unRename⇒1 (app is is₁)        (cong (appl u) (appl .u) tρ→t') = cong (appl _) (appl _) (unRename⇒1 is tρ→t')
unRename⇒1 (fst is)            (cong fst fst tρ→t') = cong fst fst (unRename⇒1 is tρ→t')
unRename⇒1 (snd is)            (cong snd snd tρ→t') = cong snd snd (unRename⇒1 is tρ→t')
unRename⇒1 (is ∗ is₁)          (cong (∗l u) (∗l .u) tρ→t')   = cong (∗l _) (∗l _) (unRename⇒1 is tρ→t')
unRename⇒1 ((next is) ∗ is₁)      (cong (∗r t₂) (∗r .t₂) tρ→t') = cong (∗r _) (∗r _) (unRename⇒1 is₁ tρ→t')
\end{code}
}

\begin{code}
absVarSNe  :   ∀{Γ a b n}{t : Tm (a ∷ Γ) (a →̂ b)} →
               app t (var zero) ∈ SNe n → t ∈ SNe n
absVarSN   :   ∀{Γ a b n}{t : Tm (a ∷ Γ) (a →̂ b)} →
               app t (var zero) ∈ SN n → t ∈ SN n
\end{code}

\AgdaHide{
\begin{code}
absVarSNe (elim 𝒏 (appl 𝒖)) = 𝒏

absVarSN (ne 𝒖)                                                   = ne (absVarSNe 𝒖)
absVarSN (exp (β {t = t} 𝒖) 𝒕′)                                   = abs (unRenameSN (prop→Ind contract (subst-ext contract-sgs t)) 𝒕′)
absVarSN (exp (cong (appl ._) (appl ._) t⇒) 𝒕′) = exp t⇒ (absVarSN 𝒕′)
\end{code}
}

