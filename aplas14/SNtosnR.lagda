\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}
{-# OPTIONS --no-termination-check #-}
--{-# OPTIONS --allow-unsolved-metas #-}

--{-# OPTIONS --show-implicit #-}
module SNtosnR where

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
\end{code}
}


%%% Redexes
\begin{code}
β▸sn :  ∀ {n Γ b} {a∞ b∞} {z} {t : Tm Γ (force (a∞ ⇒ b∞))} {u : Tm Γ (force a∞)}
        (E : ECxt* Γ (▸̂ b∞) b) → sn (suc n) (E [ z ]*) →
        sn n t → sn n u → sn (suc n) (E [ next (app t u) ]*) →
        sn (suc n) (E [ next t ∗ next {a∞ = a∞} u ]*)
\end{code}
\AgdaHide{
\begin{code}
β▸sn E z t u r = acc (λ x → help E z t u r (mkEHole* E) x) where
  help : ∀ {Γ b a∞ b∞} {z : Tm Γ (▸̂ b∞)} {q}
       {t : Tm Γ (force (a∞ ⇒ b∞))} {u : Tm Γ (force a∞)} {n} {t' : Tm Γ b}
       (E : ECxt* Γ (▸̂ b∞) b) →
     sn (suc n) (E [ z ]*) →
     sn n t →
     sn n u →
     sn (suc n) (E [ next (app t u) ]*) →
     EHole* q E ((next t) ∗ (next {a∞ = a∞} u))  →  q ⟨ suc n ⟩⇒β t' → sn (suc n) t'
  help E z t u r eq t⇒ with split E eq β▸ t⇒
  help E₁ z₂ t₂ u₂ r₁ eq t⇒ | inj₁ (._ , a₁ , β▸) rewrite hole*→≡ a₁ = r₁
  help E₁ z₂ (acc t₃) u₂ r₁ eq t⇒ | inj₁ (._ , a₁ , cong (∗l ._) (∗l ._) (cong next next t⇒')) rewrite hole*→≡ a₁
    = β▸sn E₁ z₂ (t₃ t⇒') u₂ (sn⇒β r₁ (cong*2 E₁ (cong next next (cong (appl _) (appl _) t⇒'))))
  help E₁ z₂ t₃ (acc u₂) r₁ eq t⇒ | inj₁ (._ , a₁ , cong (∗r ._) (∗r ._) (cong next next t⇒')) rewrite hole*→≡ a₁
    = β▸sn E₁ z₂ t₃ (u₂ t⇒') (sn⇒β r₁ (cong*2 E₁ (cong next next (cong (appr _) (appr _) t⇒'))))
  help E₁ (acc z₂) t₂ u₂ r₁ eq t⇒ | inj₂ (Es' , a , g) rewrite hole*→≡ a = β▸sn Es' (z₂ (g _)) t₂ u₂ (sn⇒β r₁ (g _))
\end{code}
}
\begin{code}
βfstsn :  ∀ {n Γ b} {a c} {z} {t : Tm Γ b} {u : Tm Γ a}
          (E : ECxt* Γ b c) → sn n (E [ z ]*) →
          sn n t → sn n u → sn n (E [ t ]*) →
          sn n (E [ fst (pair t u) ]*)
\end{code}
\AgdaHide{
\begin{code}
βfstsn E z t u r = acc (λ x → help E z t u r (mkEHole* E) x) where
  help : ∀ {Γ b a c} {z t : Tm Γ b} {u : Tm Γ a} {n} {t' : Tm Γ c}{q}
         (E : ECxt* Γ b c) →
       sn n (E [ z ]*) →
       sn n t →
       sn n u →
       sn n (E [ t ]*) →
       EHole* q E (fst (pair t u)) →
         q ⟨ n ⟩⇒β t' → sn n t'
  help E z t u r eq t⇒ with split E eq βfst t⇒
  help E₁ z₂ t₂ u₂ r eq t⇒ | inj₁ (t₁ , a₁ , βfst) rewrite hole*→≡ a₁ = r
  help E₁ z₂ (acc t₃) u₂ r₁ eq t⇒ | inj₁ (._ , a₂ , cong fst fst (cong (pairl u₁) (pairl .u₁) t⇒'))
    rewrite hole*→≡ a₂ = βfstsn E₁ z₂ (t₃ t⇒') u₂ (sn⇒β r₁ (cong*2 E₁ t⇒'))
  help E₁ z₂ t₃ (acc u₂) r₁ eq t⇒ | inj₁ (._ , a₂ , cong fst fst (cong (pairr t₁) (pairr .t₁) t⇒'))
    rewrite hole*→≡ a₂ = βfstsn E₁ z₂ t₃ (u₂ t⇒') r₁
  help E₁ (acc z₂) t₂ u₂ r eq t⇒ | inj₂ (Es' , a , g) rewrite hole*→≡ a = βfstsn Es' (z₂ (g _)) t₂ u₂ (sn⇒β r (g _))
\end{code}
}
\begin{code}
βsndsn :  ∀ {n Γ b} {a c} {z} {t : Tm Γ b} {u : Tm Γ a}
          (E : ECxt* Γ b c) → sn n (E [ z ]*) →
          sn n t → sn n u → sn n (E [ t ]*) →
          sn n (E [ snd (pair u t) ]*)
\end{code}
\AgdaHide{
\begin{code}
βsndsn E z t u r = acc (λ x → help E z t u r (mkEHole* E) x) where
  help : ∀ {Γ b a c} {z t : Tm Γ b} {u : Tm Γ a} {n} {t' : Tm Γ c}{q}
         (E : ECxt* Γ b c) →
       sn n (E [ z ]*) →
       sn n t →
       sn n u →
       sn n (E [ t ]*) →
       EHole* q E (snd (pair u t)) →
         q ⟨ n ⟩⇒β t' → sn n t'
  help E z t u r eq t⇒ with split E eq βsnd t⇒
  help E₁ z₂ t₂ u₂ r eq t⇒ | inj₁ (t₁ , a₁ , βsnd) rewrite hole*→≡ a₁ = r
  help E₁ z₂ (acc t₃) u₂ r₁ eq t⇒ | inj₁ (._ , a₂ , cong snd snd (cong (pairr u₁) (pairr .u₁) t⇒'))
    rewrite hole*→≡ a₂ = βsndsn E₁ z₂ (t₃ t⇒') u₂ (sn⇒β r₁ (cong*2 E₁ t⇒'))
  help E₁ z₂ t₃ (acc u₂) r₁ eq t⇒ | inj₁ (._ , a₂ , cong snd snd (cong (pairl t₁) (pairl .t₁) t⇒'))
    rewrite hole*→≡ a₂ = βsndsn E₁ z₂ t₃ (u₂ t⇒') r₁
  help E₁ (acc z₂) t₂ u₂ r eq t⇒ | inj₂ (Es' , a , g) rewrite hole*→≡ a = βsndsn Es' (z₂ (g _)) t₂ u₂ (sn⇒β r (g _))
\end{code}
}

