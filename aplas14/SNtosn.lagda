\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}
module SNtosn where

open import Data.Sum
open import Library
open import InfiniteTypes
open import Terms
open import Substitution
open import TermShape
open import sn-definition
open import SN
open import NReduction
open import NReductionProps as NR
open import Reduction
\end{code}
}
\AgdaHide{
\begin{code}
sn⇒β :  ∀ {Γ} {n : ℕ} {a} {t t' : Tm Γ a} → sn n t → t ⟨ n ⟩⇒β t' → sn n t'
sn⇒β (acc h) r = h r
\end{code}
}
\AgdaHide{
\begin{code}
varsn   :  ∀ {Γ} {n : ℕ} {a} (x : Var Γ a) → sn n (var x)
abssn   :  ∀ {Γ} {n : ℕ} {a b} {t : Tm (a ∷ Γ) b} → sn n t → sn n (abs t)
next0sn :  ∀ {Γ} {a∞} {t : Tm Γ _} → sn 0 (next t ∶ ▸̂ a∞)
nextsn  :  ∀ {Γ} {n : ℕ} {a∞} {t : Tm Γ _} → sn n t → sn (suc n) (next t ∶ ▸̂ a∞)
fstsn   :  ∀ {Γ} {n : ℕ} {a b} {t : Tm Γ (a ×̂  b)} → sn n t → sn n (fst t)
sndsn   :  ∀ {Γ} {n : ℕ} {a b} {t : Tm Γ (a ×̂  b)} → sn n t → sn n (snd t)
pairsn  :  ∀ {Γ a b n}{t : Tm Γ a}{u : Tm Γ b}
           → (𝒕 : sn n t) (𝒖 : sn n u)
           → sn n (pair t u)
\end{code}
}
\AgdaHide{
\begin{code}
Fstsn   :  ∀ {Γ} {n : ℕ} {a b} {t : Tm Γ a}{u : Tm Γ b} → sn n (pair t u) → sn n t
Sndsn   :  ∀ {Γ} {n : ℕ} {a b} {t : Tm Γ a}{u : Tm Γ b} → sn n (pair t u) → sn n u

varsn x = acc λ { (cong () _ _) }

abssn (acc f) = acc (λ { {._} (cong abs abs x)  → abssn (f x) })

next0sn = acc ((λ { (cong () _ _) }))
nextsn (acc f) = acc (λ { {._} (cong next next x)  → nextsn (f x) })

subsn : ∀ {Γ Δ} {n n' : ℕ} {a b} {f : Tm Γ a -> Tm Δ b} →
        (g : ∀ {t t' : Tm Γ a} → t ⟨ n ⟩⇒β t' → f t ⟨ n' ⟩⇒β f t') →
        ∀ {t} → sn n' (f t) → sn n t
subsn g (acc ft) = acc (\ t⇒ -> subsn g (ft (g t⇒)))

Fstsn p = subsn (\ x -> cong (pairl _) (pairl _) x) p

Sndsn = subsn (\ x -> (cong (pairr _) (pairr _) x))

fstsn t = acc (helper t) where
  helper : ∀ {Γ n a b} {t : Tm Γ (a ×̂ b)} {t' : Tm Γ a}
           → sn n t → fst t ⟨ n ⟩⇒β t' → sn n t'
  helper t       βfst               = Fstsn t
  helper (acc f) (cong fst fst t⇒β) = fstsn (f t⇒β)

sndsn t = acc (helper t) where
  helper : ∀ {Γ n a b} {t : Tm Γ (a ×̂ b)} {t' : Tm Γ b}
           → sn n t → snd t ⟨ n ⟩⇒β t' → sn n t'
  helper t       βsnd               = Sndsn t
  helper (acc f) (cong snd snd t⇒β) = sndsn (f t⇒β)

pairsn t u = acc (λ x → helper t u x) where
  helper : ∀ {Γ a b n} {t : Tm Γ a} {u : Tm Γ b}
           {t' : Tm Γ (a ×̂ b)} →
         sn n t → sn n u → pair t u ⟨ n ⟩⇒β t' → sn n t'
  helper (acc f) u₂ (cong (pairl u₁) (pairl .u₁) t⇒) = pairsn (f t⇒) u₂
  helper t₂ (acc f) (cong (pairr t₁) (pairr .t₁) t⇒) = pairsn t₂ (f t⇒)
\end{code}
}
\AgdaHide{
\begin{code}
appsn   :  ∀{n Γ a b}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} →
           sn n t → sn n u → SNe n t →
           sn n (app t u)
∗sn     :  ∀ {n Γ} {a∞}{b∞} {t : Tm Γ (▸̂ (a∞ ⇒ b∞))} {u : Tm Γ (▸̂ a∞)} →
           sn n t → sn n u → SNe n t ⊎ SNe n u →
           sn n (t ∗ u)
elimsn  :  ∀ {n Γ a b}{E : ECxt Γ a b}{t : Tm Γ a}{Et : Tm Γ b} →
           sn n t → PCxt (sn n) Et E t → SNe n t →
           sn n Et
\end{code}
}
\AgdaHide{
\begin{code}
appsn' : ∀{n Γ a b}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} → sn n t → sn n u → SNe n t →
                 ∀ {t' : Tm Γ b} → app t u ⟨ n ⟩⇒β t' → sn n t'

elimsn'  :  ∀ {n Γ a b}{E : ECxt Γ a b}{t : Tm Γ a}{Et : Tm Γ b} → sn n t → PCxt (sn n) Et E t → SNe n t →
           ∀ {Et' : Tm Γ b} → Et ⟨ n ⟩⇒β Et' → sn n Et'
∗sn' : ∀ {n Γ} {a∞}{b∞} {t : Tm Γ (▸̂ (a∞ ⇒ b∞))}
         {u : Tm Γ (▸̂ a∞)} {Et' : Tm Γ (▸̂ b∞)} → sn n t → sn n u → SNe n t ⊎ SNe n u → (t ∗ u) ⟨ n ⟩⇒β Et' → sn n Et'

∗sn t u e = acc (∗sn' t u e)
appsn t u 𝒏 = acc (appsn' t u 𝒏)
elimsn 𝒕 E e = acc (elimsn' 𝒕 E e)
appsn' t       u       (elim 𝒏 ()) β
appsn' (acc t) 𝒖       𝒏           (cong (appl u) (appl .u) t⇒) = acc (appsn' (t t⇒) 𝒖      (mapNβSNe t⇒ 𝒏))
appsn' 𝒕       (acc u) 𝒏           (cong (appr t) (appr .t) t⇒) = acc (appsn' 𝒕      (u t⇒) 𝒏)

∗sn' t       u       (inj₁ (elim e ())) β▸
∗sn' t       u       (inj₂ (elim e ())) β▸
∗sn' (acc t) 𝒖       e                  (cong (∗l u) (∗l .u) t⇒) = acc (∗sn' (t t⇒) 𝒖      (Data.Sum.map (mapNβSNe t⇒) id e))
∗sn' 𝒕       (acc u) e                  (cong (∗r t) (∗r .t) t⇒) = acc (∗sn' 𝒕      (u t⇒) (Data.Sum.map id (mapNβSNe t⇒) e))

elimsn' 𝒕 fst      (elim 𝒏 ()) βfst
elimsn' 𝒕 fst      𝒏           (cong fst fst Et⇒Et') = fstsn (sn⇒β 𝒕 Et⇒Et')
elimsn' 𝒕 snd      (elim 𝒏 ()) βsnd
elimsn' 𝒕 snd      𝒏           (cong snd snd Et⇒Et') = sndsn (sn⇒β 𝒕 Et⇒Et')
elimsn' 𝒕 (appl 𝒖) 𝒏           t⇒                    = appsn' 𝒕 𝒖 𝒏 t⇒
elimsn' 𝒕 (∗l 𝒖)   𝒏           t⇒                    = ∗sn' 𝒕 𝒖 (inj₁ 𝒏) t⇒
elimsn' 𝒕 (∗r 𝒕₁)  𝒏           t⇒                    = ∗sn' 𝒕₁ 𝒕 (inj₂ 𝒏) t⇒
\end{code}
}


\AgdaHide{
\begin{code}
substβsn : ∀ {i m vt a Γ n} {Δ} {σ ρ : RenSub {m} vt Γ Δ} → (∀ {b} (x : Var Γ b) → vt2tm _ (σ x) ⟨ n ⟩⇒β* vt2tm _ (ρ x))
             → (t : Tm Γ a) → SN {i} n (subst σ t) → SN {i} n (subst ρ t)
substβsn f t x₁ = mapβ*SN (subst⇒β* (λ x → nβ*⇒β* (f x)) t) x₁


antiSubst : ∀ {n Γ a b} {t : Tm (a ∷ Γ) b}{u : Tm Γ a} → sn n (subst (sgs u) t) → sn n t
antiSubst {t = t} = subsn (λ x → NR.subst⇒β (sgs _) x)

subexpsn : ∀ {n Γ a b} (E : ECxt* Γ a b) {t : Tm Γ a} → sn n (E [ t ]*) -> sn n t
subexpsn E = subsn \ x -> cong*2 E x
\end{code}
}

