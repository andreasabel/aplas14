\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns --sized-types #-}
module SN where

open import Relation.Unary using (_∈_; _⊆_)
open import Size
open import Library
open import InfiniteTypes
open import Terms
open import Substitution
open import TermShape public
open import ECxtList public
\end{code}
}

\begin{code}
mutual

  SNhole :  ∀ {i : Size} (n : ℕ) {Γ : Cxt} {a b : Ty} → 
            Tm Γ b → ECxt Γ a b → Tm Γ a → Set
  SNhole {i} n = PCxt (SN {i} n)

  SNe : ∀ {i : Size} (n : ℕ) {Γ} {b} → Tm Γ b → Set
  SNe {i} n = PNe (SN {i} n)

  data SN {i : Size}{Γ} : ℕ → ∀ {a} → Tm Γ a → Set where

    ne     :  ∀ {j : Size< i} {a n t}
              → (𝒏 : SNe {j} n t)
              → SN n {a} t

    abs    :  ∀ {j : Size< i} {a b n}{t : Tm (a ∷ Γ) b}
              → (𝒕 : SN {j} n t)
              → SN n (abs t)

    pair   :  ∀ {j₁ j₂ : Size< i} {a b n t u}
              → (𝒕 : SN {j₁} n t) (𝒖 : SN {j₂} n u)
              → SN n {a ×̂ b} (pair t u)

    next0  :  ∀ {a∞} {t : Tm Γ (force a∞)}
              → SN 0 {▸̂ a∞} (next t)

    next   :  ∀ {j : Size< i} {a∞ n} {t : Tm Γ (force a∞)}
              → (𝒕 : SN {j} n t)
              → SN (suc n) {▸̂ a∞} (next t)

    exp    :  ∀ {j₁ j₂ : Size< i} {a n t t′}
              → (t⇒ : j₁ size t ⟨ n ⟩⇒ t′) (𝒕′ : SN {j₂} n t′)
              → SN n {a} t

  _size_⟨_⟩⇒_ : ∀ (i : Size) {Γ}{a} → Tm Γ a → ℕ → Tm Γ a → Set
  i size t ⟨ n ⟩⇒ t′ = SN {i} n / t ⇒ t′

  _⟨_⟩⇒_ : ∀ {i : Size} {Γ} {a} → Tm Γ a → ℕ → Tm Γ a → Set
  _⟨_⟩⇒_ {i} t n t' = SN {i} n / t ⇒ t'
\end{code}

\AgdaHide{
\begin{code}
-- Strong head reduction is deterministic.

det⇒ : ∀ {n a Γ} {t t₁ t₂ : Tm Γ a}
       → (t⇒₁ : t ⟨ n ⟩⇒ t₁) (t⇒₂ : t ⟨ n ⟩⇒ t₂) → t₁ ≡ t₂
det⇒ (β _) (β _)                                              = ≡.refl
det⇒ (β _) (cong (appl u) (appl .u) (cong () _ _))
det⇒ β▸ β▸ = ≡.refl
det⇒ β▸ (cong (._ ∗l) (._ ∗l) (cong () _ _))
det⇒ β▸ (cong (∗r t) (∗r .t) (cong () _ _ ))
det⇒ (βfst _) (βfst _)                                        = ≡.refl
det⇒ (βfst _) (cong fst fst (cong () _ _))
det⇒ (βsnd _) (βsnd _)                                        = ≡.refl
det⇒ (βsnd 𝒕) (cong snd snd (cong () _ _))
det⇒ (cong (appl u) (appl .u) (cong () _ _)) (β _)
det⇒ (cong (._ ∗l) (._ ∗l) (cong () _ _)) β▸
det⇒ (cong (∗r t₁) (∗r .t₁) (cong () _ _)) β▸
det⇒ (cong fst fst (cong () _ _ )) (βfst _)
det⇒ (cong snd snd (cong () _ _ )) (βsnd _)
det⇒ (cong (appl u) (appl .u) x) (cong (appl .u) (appl .u) y) = ≡.cong (λ t → app t u) (det⇒ x y)
det⇒ (cong fst fst x) (cong fst fst y)                        = ≡.cong fst             (det⇒ x y)
det⇒ (cong snd snd x) (cong snd snd y)                        = ≡.cong snd             (det⇒ x y)
det⇒ (cong (u ∗l) (.u ∗l) x) (cong (.u ∗l) (.u ∗l) y)         = ≡.cong (λ t → t ∗ u)   (det⇒ x y)
det⇒ (cong (∗r t) (∗r .t) x) (cong (∗r .t) (∗r .t) y)         = ≡.cong (_∗_ (next t))     (det⇒ x y)
det⇒ (cong (u ∗l) (.u ∗l) (cong () _ _)) (cong (∗r t) (∗r .t) _)
det⇒ (cong (∗r t) (∗r .t) _) (cong (u ∗l) (.u ∗l) (cong () _ _))
\end{code}
}
%%% -- Strongly neutrals are closed under application.
\AgdaHide{
\begin{code}
sneApp : ∀{n Γ a b}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} →
  SNe n t → SN n u → SNe n (app t u)
sneApp 𝒏 𝒖 = elim 𝒏 (appl 𝒖)
\end{code}
}

\begin{code}
mapSNe  : ∀ {m n} → m ≤ℕ n → ∀ {Γ a}{t : Tm Γ a} → SNe n t -> SNe m t
map⇒    : ∀ {m n} → m ≤ℕ n → ∀ {Γ a}{t t' : Tm Γ a} → t ⟨ n ⟩⇒ t' → t ⟨ m ⟩⇒ t'
mapSN   : ∀ {m n} → m ≤ℕ n → ∀ {Γ a}{t : Tm Γ a} → SN n t -> SN m t
\end{code}

\AgdaHide{
\begin{code}
mapSNh : ∀ {m n} → m ≤ℕ n → ∀ {Γ a b}{E : ECxt Γ a b}{Et t} → SNhole n Et E t -> SNhole m Et E t

mapSNe m≤n (var x) = var x
mapSNe m≤n (elim t∈Ne E∈SNh) = elim (mapSNe m≤n t∈Ne) (mapSNh m≤n E∈SNh)

mapSN m≤n (ne u∈SNe) = ne (mapSNe m≤n u∈SNe)
mapSN m≤n (abs t∈SN) = abs (mapSN m≤n t∈SN)
mapSN m≤n (pair t∈SN u∈SN) = pair (mapSN m≤n t∈SN) (mapSN m≤n u∈SN)
mapSN {m = zero} _z≤n next0 = next0
mapSN {m = zero} _z≤n (next t∈SN) = next0
mapSN {m = suc m} () next0
mapSN {m = suc m}{n = suc n} sm≤sn (next t∈SN) = next (mapSN (pred≤ℕ sm≤sn) t∈SN)
mapSN m≤n (exp t→t' t∈SN) = exp (map⇒ m≤n t→t') (mapSN m≤n t∈SN)

map⇒ m≤n (β t∈SN) = β (mapSN m≤n t∈SN)
map⇒ m≤n (β▸ {a = a}) = β▸ {a = a}
map⇒ m≤n (βfst t∈SN) = βfst (mapSN m≤n t∈SN)
map⇒ m≤n (βsnd t∈SN) = βsnd (mapSN m≤n t∈SN)
map⇒ m≤n (cong Et Et' t→t') = cong Et Et' (map⇒ m≤n t→t')

mapSNh m≤n (appl u∈SN) = appl (mapSN m≤n u∈SN)
mapSNh m≤n fst = fst
mapSNh m≤n snd = snd
mapSNh m≤n (u∈SN ∗l) = mapSN m≤n u∈SN ∗l
mapSNh m≤n (∗r t∈SN) = ∗r mapSN m≤n t∈SN
\end{code}
}

\AgdaHide{
\begin{code}

-- Substituting strongly neutral terms

record RenSubSNe {i} (vt : VarTm i) (n : ℕ) (Γ Δ : Cxt) : Set where
  constructor _,_
  field theSubst : RenSub vt Γ Δ
        isSNe    : ∀ {a} (x : Var Γ a) → SNe n (vt2tm _ (theSubst x))
open RenSubSNe

RenSN    = RenSubSNe `Var
SubstSNe = RenSubSNe `Tm

-- Substitutions are functorial in the evaluation depth n

mapSubSNe : ∀ {i vt Γ Δ m n} → m ≤ℕ n → RenSubSNe {i} vt n Γ Δ → RenSubSNe vt m Γ Δ
mapSubSNe m≤n (σ , σ∈SNe) = σ , (λ x → mapSNe m≤n (σ∈SNe x))

-- The singleton SNe substitution.
-- Replaces the first variable by another variable.

sgs-varSNe : ∀ {n Γ a} → Var Γ a → SubstSNe n (a ∷ Γ) Γ
theSubst (sgs-varSNe x)         = sgs (var x)
isSNe    (sgs-varSNe x) (zero)  = (var x)
isSNe    (sgs-varSNe x) (suc y) = var y


-- The SN-notions are closed under SNe substitution.

mutual
  substSNh : ∀ {i vt Γ Δ a b n} → (σ : RenSubSNe {i} vt n Γ Δ) → ∀ {E : ECxt Γ a b}{Et t} → (SNh : SNhole n Et E t)
                                → SNhole n (subst (theSubst σ) Et) (substEC (theSubst σ) E) (subst (theSubst σ) t)
  substSNh σ (appl u) = appl (substSN σ u)
  substSNh σ fst      = fst
  substSNh σ snd      = snd
  substSNh σ (u ∗l)   = substSN σ u ∗l
  substSNh σ (∗r t)   = ∗r substSN σ t

  subst⇒ : ∀ {i vt Γ Δ a n} (σ : RenSubSNe {i} vt n Γ Δ) {t t' : Tm Γ a} → t ⟨ n ⟩⇒ t' → subst (theSubst σ) t ⟨ n ⟩⇒ subst (theSubst σ) t'
  subst⇒ {n = n} (σ , σ∈Ne) (β {t = t} {u = u} x) = ≡.subst (λ t' → app (abs (subst (lifts σ) t)) (subst σ u) ⟨ n ⟩⇒ t')
                                                   (sgs-lifts-term {σ = σ} {u} {t})
                                                   (β {t = subst (lifts σ) t} (substSN (σ , σ∈Ne) x))

  subst⇒         σ (β▸ {a = a})        = β▸ {a = a}
  subst⇒         σ (βfst t∈SN)           = βfst (substSN σ t∈SN)
  subst⇒         σ (βsnd u∈SN)           = βsnd (substSN σ u∈SN)
  subst⇒ {n = n} σ (cong Eh Eh' t→t')    = cong (substEh (theSubst σ) Eh) (substEh (theSubst σ) Eh') (subst⇒ σ t→t')

  -- Lifting a SNe substitution.

  liftsSNe : ∀ {i vt Γ Δ a n} → RenSubSNe {i} vt n Γ Δ → RenSubSNe {i} vt n (a ∷ Γ) (a ∷ Δ)
  theSubst (liftsSNe σ)                   = lifts (theSubst σ)
  isSNe    (liftsSNe {vt = `Var} (σ , σ∈SNe)) (zero)    = var (zero)
  isSNe    (liftsSNe {vt = `Var} (σ , σ∈SNe)) (suc y) = var (suc (σ y))
  isSNe    (liftsSNe {vt = `Tm } (σ , σ∈SNe)) (zero)    = var (zero)
  isSNe    (liftsSNe {vt = `Tm } (σ , σ∈SNe)) (suc y) = substSNe {vt = `Var} (suc , (λ x → var (suc x))) (σ∈SNe y)

  substSNe : ∀ {i vt Γ Δ τ n} → (σ : RenSubSNe {i} vt n Γ Δ) → ∀ {t : Tm Γ τ} → SNe n t → SNe n (subst (theSubst σ) t)
  substSNe σ (var x)            = isSNe σ x
  substSNe σ (elim t∈SNe E∈SNh) = elim (substSNe σ t∈SNe) (substSNh σ E∈SNh)

  substSN : ∀ {i vt Γ Δ τ n} → (σ : RenSubSNe {i} vt n Γ Δ) → ∀ {t : Tm Γ τ} → SN n t → SN n (subst (theSubst σ) t)
  substSN σ (ne t∈SNe)         = ne (substSNe σ t∈SNe)
  substSN σ (abs t∈SN)         = abs (substSN (liftsSNe σ) t∈SN)
  substSN σ (pair t₁∈SN t₂∈SN) = pair (substSN σ t₁∈SN) (substSN σ t₂∈SN)
  substSN σ next0                 = next0
  substSN σ (next t∈SN)           = next (substSN (mapSubSNe n≤sn σ) t∈SN)
  substSN σ (exp t→t' t'∈SN)   = exp (subst⇒ σ t→t') (substSN σ t'∈SN)


-- SN is closed under renaming.

renSN :  ∀{n Γ Δ} (ρ : Γ ≤ Δ) → RenSN n Δ Γ
renSN ρ = (ρ , λ x → var (ρ x))
\end{code}
}

\begin{code}
renameSNe   :  ∀ {n a Γ Δ} (ρ : Γ ≤ Δ) {t : Tm Δ a} →
               SNe n t → SNe n (rename ρ t)
renameSN    :  ∀ {n a Γ Δ} (ρ : Γ ≤ Δ) {t : Tm Δ a} →
               SN n t → SN n (rename ρ t)
rename⇒      :  ∀ {n a Γ Δ} (ρ : Γ ≤ Δ) {t t' : Tm Δ a} →
               t ⟨ n ⟩⇒ t' → rename ρ t ⟨ n ⟩⇒ rename ρ t'
\end{code}
\input{Rename}

\begin{code}
varSN       :  ∀ {Γ a n x} → var x ∈ SN {Γ = Γ} n {a}
appVarSN    :  ∀ {Γ a b n}{t : Tm Γ (a →̂ b)}{x} →
               t ∈ SN n → app t (var x) ∈ SN n
fstSN       :  ∀ {n a b Γ}{t : Tm Γ (a ×̂ b)} → SN n t → SN n (fst t)
sndSN       :  ∀ {n a b Γ}{t : Tm Γ (a ×̂ b)} → SN n t → SN n (snd t)
bothProjSN  :  ∀ {n a b Γ}{t : Tm Γ (a ×̂ b)} →
               (𝒕₁ : SN n (fst t)) (𝒕₂ : SN n (snd t)) → SN n t
fromFstSN   :  ∀{i n a b Γ}{t : Tm Γ (a ×̂ b)} → SN {i} n (fst t) → SN {i} n t
fromSndSN   :  ∀{i n a b Γ}{t : Tm Γ (a ×̂ b)} → SN {i} n (snd t) → SN {i} n t
\end{code}

\AgdaHide{
\begin{code}
renameSNe ρ = substSNe (renSN ρ)

renameSN ρ = substSN (renSN ρ)

rename⇒ ρ = subst⇒ (renSN ρ)
-- Variables are SN.

varSN = ne (var _)

-- SN is closed under application to variables.

appVarSN (ne t∈SNe)       = ne (elim t∈SNe (appl varSN))
appVarSN (abs t∈SN)       = exp (β varSN) (substSN (sgs-varSNe _) t∈SN)
appVarSN (exp t→t' t'∈SN) = exp (cong (appl (var _)) (appl (var _)) t→t') (appVarSN t'∈SN)

-- Closure under projections

fstSN (ne 𝒏)       = ne (elim 𝒏 fst)
-- fstSN (ne 𝒏)       = ne (elim {j₁ = ∞} 𝒏 fst)
fstSN (pair 𝒕₁ 𝒕₂) = exp (βfst 𝒕₂) 𝒕₁
fstSN (exp t⇒ 𝒕)   = exp (cong fst fst t⇒) (fstSN 𝒕)

sndSN (ne 𝒏)       = ne (elim 𝒏 snd)
-- sndSN (ne 𝒏)       = ne (elim {j₁ = ∞} 𝒏 snd)
sndSN (pair 𝒕₁ 𝒕₂) = exp (βsnd 𝒕₁) 𝒕₂
sndSN (exp t⇒ 𝒕)   = exp (cong snd snd t⇒) (sndSN 𝒕)

-- Extensionality of SN for product type:
-- If fst t ∈ SN and snd t ∈ SN then t ∈ SN.

bothProjSN (ne (elim 𝒏 fst))    _                 = ne 𝒏
bothProjSN (exp (βfst 𝒕₂) 𝒕₁)    _                 = pair 𝒕₁ 𝒕₂
bothProjSN (exp (cong _ _ _) _) (ne (elim 𝒏 snd))  = ne 𝒏
bothProjSN (exp (cong _ _ _) _) (exp (βsnd 𝒕₁) 𝒕₂) = pair 𝒕₁ 𝒕₂
bothProjSN (exp (cong fst fst t⇒₁) 𝒕₁) (exp (cong snd snd t⇒₂) 𝒕₂)
  = exp t⇒₂ (≡.subst (SN _) (det⇒ t⇒₁ t⇒₂) (bothProjSN 𝒕₁ (≡.subst (SN _) (≡.sym (≡.cong snd (det⇒ t⇒₁ t⇒₂))) 𝒕₂)))


-- Subterm properties of SN

-- If fst t ∈ SN then t ∈ SN.

fromFstSN (ne (elim 𝒏 fst))         = ne 𝒏
fromFstSN (exp (βfst 𝒕₂) 𝒕₁)        = pair 𝒕₁ 𝒕₂
fromFstSN (exp (cong fst fst t⇒) 𝒕) = exp t⇒ (fromFstSN 𝒕)

-- If snd t ∈ SN then t ∈ SN.

fromSndSN (ne (elim 𝒏 snd))         = ne 𝒏
fromSndSN (exp (βsnd 𝒕₁) 𝒕₂)        = pair 𝒕₁ 𝒕₂
fromSndSN (exp (cong snd snd t⇒) 𝒕) = exp t⇒ (fromSndSN 𝒕)
\end{code}
}
