\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}
{-# OPTIONS --no-termination-check #-}
--{-# OPTIONS --allow-unsolved-metas #-}

--{-# OPTIONS --show-implicit #-}
module SNtosn where

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
\end{code}
}
\AgdaHide{
\begin{code}
sn⇒β :  ∀ {Γ} {n : ℕ} {a} {t t' : Tm Γ a} → sn n t → t ⟨ n ⟩⇒β t' → sn n t'
sn⇒β (acc h) r = h r
\end{code}
}
\begin{code}
varsn   :  ∀ {Γ} {n : ℕ} {a} (x : Var Γ a) → sn n (var x)
abssn   :  ∀ {Γ} {n : ℕ} {a b} {t : Tm (a ∷ Γ) b} → sn n t → sn n (abs t)
nextsn  :  ∀ {Γ} {n : ℕ} {a∞} {t : Tm Γ _} → sn n t → sn (suc n) (next t ∶ ▸̂ a∞)
Fstsn   :  ∀ {Γ} {n : ℕ} {a b} {t : Tm Γ a}{u : Tm Γ b} → sn n (pair t u) → sn n t
Sndsn   :  ∀ {Γ} {n : ℕ} {a b} {t : Tm Γ a}{u : Tm Γ b} → sn n (pair t u) → sn n u
fstsn   :  ∀ {Γ} {n : ℕ} {a b} {t : Tm Γ (a ×̂  b)} → sn n t → sn n (fst t)
sndsn   :  ∀ {Γ} {n : ℕ} {a b} {t : Tm Γ (a ×̂  b)} → sn n t → sn n (snd t)
pairsn  :  ∀ {Γ a b n}{t : Tm Γ a}{u : Tm Γ b}
           → (𝒕 : sn n t) (𝒖 : sn n u)
           → sn n (pair t u)
\end{code}
\AgdaHide{
\begin{code}
varsn x = acc λ { (cong () _ _) }

abssn (acc f) = acc (λ { {._} (cong abs abs x)  → abssn (f x) })

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

\begin{code}
appsn   :  ∀{n Γ a b}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} →
           sn n t → sn n u → SNe n t →
           sn n (app t u)
∗sn     :  ∀ {n Γ} {a : Ty}{b∞} {t : Tm Γ (▸̂ (delay a ⇒ b∞))} {u : Tm Γ (▸ a)} →
           sn n t → sn n u → SNe n t ⊎ SNe n u →
           sn n (t ∗ u)
elimsn  :  ∀ {n Γ a b}{E : ECxt Γ a b}{t : Tm Γ a}{Et : Tm Γ b} →
           sn n t → PCxt (sn n) Et E t → SNe n t →
           sn n Et

\end{code}

\AgdaHide{
\begin{code}
appsn' : ∀{n Γ a b}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} → sn n t → sn n u → SNe n t →
                 ∀ {t' : Tm Γ b} → app t u ⟨ n ⟩⇒β t' → sn n t'

elimsn'  :  ∀ {n Γ a b}{E : ECxt Γ a b}{t : Tm Γ a}{Et : Tm Γ b} → sn n t → PCxt (sn n) Et E t → SNe n t →
           ∀ {Et' : Tm Γ b} → Et ⟨ n ⟩⇒β Et' → sn n Et'
∗sn' : ∀ {n Γ} {a : Ty}{b∞} {t : Tm Γ (▸̂ ((delay a) ⇒ b∞))}
         {u : Tm Γ (▸ a)} {Et' : Tm Γ (▸̂ b∞)} → sn n t → sn n u → SNe n t ⊎ SNe n u → (t ∗ u) ⟨ n ⟩⇒β Et' → sn n Et'

∗sn t u e = acc (∗sn' t u e)
appsn t u 𝒏 = acc (appsn' t u 𝒏)
elimsn 𝒕 E e = acc (elimsn' 𝒕 E e)
appsn' t       u       (elim 𝒏 ()) β
appsn' (acc t) 𝒖       𝒏           (cong (appl u) (appl .u) t⇒) = acc (appsn' (t t⇒) 𝒖      (mapNβSNe t⇒ 𝒏))
appsn' 𝒕       (acc u) 𝒏           (cong (appr t) (appr .t) t⇒) = acc (appsn' 𝒕      (u t⇒) 𝒏)

∗sn' t       u       (inj₁ (elim e ())) β▸
∗sn' t       u       (inj₂ (elim e ())) β▸
∗sn' (acc t) 𝒖       e                  (cong (u ∗l) (.u ∗l) t⇒) = acc (∗sn' (t t⇒) 𝒖      (Data.Sum.map (mapNβSNe t⇒) id e))
∗sn' 𝒕       (acc u) e                  (cong (∗r t) (∗r .t) t⇒) = acc (∗sn' 𝒕      (u t⇒) (Data.Sum.map id (mapNβSNe t⇒) e))

elimsn' 𝒕 fst      (elim 𝒏 ()) βfst
elimsn' 𝒕 fst      𝒏           (cong fst fst Et⇒Et') = fstsn (sn⇒β 𝒕 Et⇒Et')
elimsn' 𝒕 snd      (elim 𝒏 ()) βsnd
elimsn' 𝒕 snd      𝒏           (cong snd snd Et⇒Et') = sndsn (sn⇒β 𝒕 Et⇒Et')
elimsn' 𝒕 (appl 𝒖) 𝒏           t⇒                    = appsn' 𝒕 𝒖 𝒏 t⇒
elimsn' 𝒕 (𝒖 ∗l)   𝒏           t⇒                    = ∗sn' 𝒕 𝒖 (inj₁ 𝒏) t⇒
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

%%% Redexes
\begin{code}
β▸sn :  ∀ {n Γ b} {a b∞} {z} {t : Tm Γ (a →̂ (force b∞))} {u : Tm Γ a}
        (E : ECxt* Γ (▸̂ b∞) b) → sn (suc n) (E [ z ]*) →
        sn n t → sn n u → sn (suc n) (E [ next (app t u) ]*) →
        sn (suc n) (E [ next t ∗ next u ]*)
\end{code}
\AgdaHide{
\begin{code}
β▸sn E z t u r = acc (λ x → help E z t u r (mkEhole* E) x) where
  help : ∀ {Γ b a b∞} {z : Tm Γ (▸̂ b∞)} {q}
       {t : Tm Γ (a →̂ (force b∞))} {u : Tm Γ a} {n} {t' : Tm Γ b}
       (E : ECxt* Γ (▸̂ b∞) b) →
     sn (suc n) (E [ z ]*) →
     sn n t →
     sn n u →
     sn (suc n) (E [ next (app t u) ]*) →
     Ehole* q E ((next t) ∗ (next u))  →  q ⟨ suc n ⟩⇒β t' → sn (suc n) t'
  help E z t u r eq t⇒ with split E eq β▸ t⇒
  help E₁ z₂ t₂ u₂ r₁ eq t⇒ | inj₁ (._ , a₁ , β▸) rewrite hole*→≡ a₁ = r₁
  help E₁ z₂ (acc t₃) u₂ r₁ eq t⇒ | inj₁ (._ , a₁ , cong (._ ∗l) (._ ∗l) (cong next next t⇒')) rewrite hole*→≡ a₁
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
βfstsn E z t u r = acc (λ x → help E z t u r (mkEhole* E) x) where
  help : ∀ {Γ b a c} {z t : Tm Γ b} {u : Tm Γ a} {n} {t' : Tm Γ c}{q}
         (E : ECxt* Γ b c) →
       sn n (E [ z ]*) →
       sn n t →
       sn n u →
       sn n (E [ t ]*) →
       Ehole* q E (fst (pair t u)) →
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
βsndsn E z t u r = acc (λ x → help E z t u r (mkEhole* E) x) where
  help : ∀ {Γ b a c} {z t : Tm Γ b} {u : Tm Γ a} {n} {t' : Tm Γ c}{q}
         (E : ECxt* Γ b c) →
       sn n (E [ z ]*) →
       sn n t →
       sn n u →
       sn n (E [ t ]*) →
       Ehole* q E (snd (pair u t)) →
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

\begin{code}
βsn :  ∀ {i n a b c Γ} {u : Tm Γ a} {t : Tm (a ∷ Γ) b}{z}
       (Es : ECxt* Γ b c) → sn n (Es [ z ]*) →
       sn n t → SN {i} n (Es [ subst (sgs u) t ]*) → sn n u →
       sn n (Es [ app (abs t) u ]*)
\end{code}

%%% Final Proof.
\begin{code}
expsn     :  ∀ {i j Γ n a} {t th : Tm Γ a}  →
             i size t ⟨ n ⟩⇒ th → SN {j} n th → sn n th →
             sn n t

expsnCxt  :  ∀ {i j Γ n a b} {t th to : Tm Γ a} →
             (Es : ECxt* Γ a b) → i size t ⟨ n ⟩⇒ th →
             SN {j} n (Es [ th ]*) → sn n (Es [ th ]*) →
             t ⟨ n ⟩⇒β to → sn n (Es [ to ]*)

fromSN    :  ∀ {i} {Γ} {n : ℕ} {a} {t : Tm Γ a} →
             SN {i} n t → sn n t
fromSNe   :  ∀ {i Γ n a} {t : Tm Γ a} →
             SNe {i} n t → sn n t
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

expsnCxt E β▸       𝒕h 𝑡h (cong (._ ∗l)   (._ ∗l) (cong next next t⇒))
   = β▸sn E 𝑡h (sn⇒β (subsn (λ x → cong*2 E (cong next next (cong (appl _) (appl _) x))) 𝑡h) t⇒)
                     (subsn (λ x → cong*2 E (cong next next (cong (appr _) (appr _) x))) 𝑡h)
               (sn⇒β 𝑡h (cong*2 E (cong next next (cong (appl _) (appl _) t⇒))))
expsnCxt E β▸       𝒕h 𝑡h (cong (∗r ._)   (∗r ._) (cong next next t⇒)) = β▸sn E 𝑡h
          (subsn (λ x → cong*2 E (cong next next (cong (appl _) (appl _) x))) 𝑡h)
    (sn⇒β (subsn (λ x → cong*2 E (cong next next (cong (appr _) (appr _) x))) 𝑡h) t⇒)
    (sn⇒β 𝑡h (cong*2 E (cong next next (cong (appr _) (appr _) t⇒))))

expsnCxt E (βfst 𝒖) 𝒕h 𝑡h (cong fst fst (cong (pairl _) (pairl ._) t⇒)) = βfstsn E 𝑡h (sn⇒β (subexpsn E 𝑡h) t⇒) (fromSN 𝒖) (sn⇒β 𝑡h (cong*2 E t⇒))
expsnCxt E (βfst 𝒖) 𝒕h 𝑡h (cong fst fst (cong (pairr _) (pairr ._) t⇒)) = βfstsn E 𝑡h (subexpsn E 𝑡h) (sn⇒β (fromSN 𝒖) t⇒) 𝑡h

expsnCxt E (βsnd 𝒖) 𝒕h 𝑡h (cong snd snd (cong (pairr _) (pairr ._) t⇒)) = βsndsn E 𝑡h (sn⇒β (subexpsn E 𝑡h) t⇒) (fromSN 𝒖) (sn⇒β 𝑡h (cong*2 E t⇒))
expsnCxt E (βsnd 𝒖) 𝒕h 𝑡h (cong snd snd (cong (pairl _) (pairl ._) t⇒)) = βsndsn E 𝑡h (subexpsn E 𝑡h) (sn⇒β (fromSN 𝒖) t⇒) 𝑡h

expsnCxt E (cong (appl u) (appl .u) (cong () 𝑬𝒕' th⇒)) 𝒕h 𝑡h β
expsnCxt E (cong (._ ∗l)  (._ ∗l)   (cong () 𝑬𝒕' th⇒)) 𝒕h 𝑡h β▸
expsnCxt E (cong (∗r t)   (∗r .t)   (cong () 𝑬𝒕' th⇒)) 𝒕h 𝑡h β▸
expsnCxt E (cong fst      fst       (cong () 𝑬𝒕' th⇒)) 𝒕h 𝑡h βfst
expsnCxt E (cong snd      snd       (cong () 𝑬𝒕' th⇒)) 𝒕h 𝑡h βsnd

expsnCxt E (cong (appl u) (appl .u) th⇒) 𝒕h 𝑡h (cong (appl .u)    (appl .u)    t⇒) = expsnCxt (appl u ∷ E) th⇒ 𝒕h 𝑡h t⇒
expsnCxt E (cong fst      fst       th⇒) 𝒕h 𝑡h (cong fst          fst          t⇒) = expsnCxt (fst ∷ E)    th⇒ 𝒕h 𝑡h t⇒
expsnCxt E (cong snd      snd       th⇒) 𝒕h 𝑡h (cong snd          snd          t⇒) = expsnCxt (snd ∷ E)    th⇒ 𝒕h 𝑡h t⇒
expsnCxt E (cong (u ∗l)   (.u ∗l)   th⇒) 𝒕h 𝑡h (cong (.u ∗l)      (.u ∗l)      t⇒) = expsnCxt (u ∗l ∷ E)   th⇒ 𝒕h 𝑡h t⇒
expsnCxt E (cong (∗r t₁)  (∗r .t₁)  th⇒) 𝒕h 𝑡h (cong (∗r .(next t₁)) (∗r .(next t₁)) t⇒) = expsnCxt (∗r t₁ ∷ E)  th⇒ 𝒕h 𝑡h t⇒

expsnCxt E (cong (appl u) (appl .u) th⇒) 𝒕h (acc 𝑡h) (cong (appr t) (appr .t)           t⇒)
          = acc (expsnCxt [] (E [ cong (appl _) (appl _) th⇒ ]⇒*) (mapNβSN t⇒' 𝒕h) (𝑡h t⇒'))
             where t⇒' = E [ cong (appr _) (appr _)           t⇒  ]⇒β*

expsnCxt E (cong (u ∗l)   (.u ∗l)   th⇒) 𝒕h (acc 𝑡h) (cong (∗r t)   (∗r .t)             t⇒)
          = acc (expsnCxt [] (E [ cong (_ ∗l)   (_ ∗l)   th⇒ ]⇒*) (mapNβSN t⇒' 𝒕h) (𝑡h t⇒'))
             where t⇒' = E [ cong (∗r _)   (∗r _)             t⇒  ]⇒β*

expsnCxt E (cong (∗r t₁)  (∗r .t₁)  th⇒) 𝒕h (acc 𝑡h) (cong (t ∗l)   (.t ∗l) (cong next next t⇒))
          = acc (expsnCxt [] (E [ cong (∗r _)   (∗r _)   th⇒ ]⇒*) (mapNβSN t⇒' 𝒕h) (𝑡h t⇒'))
             where t⇒' = E [ cong (_ ∗l)   (_ ∗l) (cong next next t⇒) ]⇒β*


fromSN (ne 𝒏)       = fromSNe 𝒏
fromSN (abs t₁)     = abssn (fromSN t₁)
fromSN (pair t₁ t₂) = pairsn (fromSN t₁) (fromSN t₂)
fromSN next0           = acc ((λ { (cong () _ _) }))
fromSN (next t₁)       = nextsn (fromSN t₁)
fromSN (exp t⇒ t₁)  = acc (expsnCxt [] t⇒ t₁ (fromSN t₁))

fromSNe (elim 𝒏 E) = elimsn (fromSNe 𝒏) (mapPCxt fromSN E) 𝒏
fromSNe (var x)    = varsn x

expsn x y z = acc (expsnCxt [] x y z)
\end{code}
}
