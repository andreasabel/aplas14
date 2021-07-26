\AgdaHide{
\begin{code}

module NReductionProps where
open import Data.Sum
open import Library
open import InfiniteTypes
open import Terms
open import Substitution
open import NReduction
open import SN
\end{code}
}

\AgdaHide{
\begin{code}
subst⇒β :  ∀ {n m vt a Γ} {t t' : Tm Γ a} {Δ}
           (σ : RenSub {m} vt Γ Δ) → t ⟨ n ⟩⇒β t' → subst σ t ⟨ n ⟩⇒β subst σ t'
\end{code}
}

\begin{code}
subst⇒β {n} σ (β {t = t} {u = u})            = ≡.subst (λ t' → app (abs (subst (lifts σ) t)) (subst σ u) ⟨ n ⟩⇒β t')
                                                   (sgs-lifts-term {σ = σ} {u} {t})
                                           β
subst⇒β σ β▸                             = β▸
subst⇒β σ βfst                           = βfst
subst⇒β σ βsnd                           = βsnd
subst⇒β σ (cong (appl u) (appl .u) t⇒)   = cong (appl _) (appl _) (subst⇒β σ t⇒)
subst⇒β σ (cong (appr t₁) (appr .t₁) t⇒) = cong (appr _) (appr _) (subst⇒β σ t⇒)
subst⇒β σ (cong fst fst t⇒)              = cong fst fst (subst⇒β σ t⇒)
subst⇒β σ (cong snd snd t⇒)              = cong snd snd (subst⇒β σ t⇒)
subst⇒β σ (cong (∗l u) (∗l .u) t⇒)       = cong (∗l _) (∗l _) (subst⇒β σ t⇒)
subst⇒β σ (cong (∗r t₁) (∗r .t₁) t⇒)     = cong (∗r _) (∗r _) (subst⇒β σ t⇒)
subst⇒β σ (cong abs abs t⇒)              = cong abs abs (subst⇒β (lifts σ) t⇒)
subst⇒β σ (cong next next t⇒)                = cong next next (subst⇒β σ t⇒)
subst⇒β σ (cong (pairr t) (pairr ._) t⇒) = cong (pairr (subst σ t)) (pairr _) (subst⇒β σ t⇒)
subst⇒β σ (cong (pairl u) (pairl ._) t⇒) = cong (pairl (subst σ u)) (pairl _) (subst⇒β σ t⇒)
\end{code}

\begin{code}
data _⟨_⟩⇒β*_ {Γ} {a} : Tm Γ a → ℕ → Tm Γ a → Set where
  []  : ∀ {n t} → t ⟨ n ⟩⇒β* t
  _∷_ : ∀ {n ti tm to} → ti ⟨ n ⟩⇒β tm → tm ⟨ n ⟩⇒β* to → ti ⟨ n ⟩⇒β* to

_++β_ : ∀ {n} {Γ} {a} {t₀ t₁ t₂ : Tm Γ a} → t₀ ⟨ n ⟩⇒β* t₁ → t₁ ⟨ n ⟩⇒β* t₂ → t₀ ⟨ n ⟩⇒β* t₂
[]       ++β ys = ys
(x ∷ xs) ++β ys = x ∷ (xs ++β ys)

cong* :  ∀ {n n' a Γ Δ} {b} {t tβ* : Tm Δ a} {C : NβCxt Δ Γ a b n n'}{C[t] C[tβ*]} →
         NβHole C[t] C t → NβHole C[tβ*] C tβ* → t ⟨ n ⟩⇒β* tβ* → C[t] ⟨ n' ⟩⇒β* C[tβ*]
\end{code}
\AgdaHide{
\begin{code}
cong* (appl u)   (appl .u)   []       = []
cong* (appr t₁)  (appr .t₁)  []       = []
cong* (pairl u)  (pairl .u)  []       = []
cong* (pairr t₁) (pairr .t₁) []       = []
cong* fst        fst         []       = []
cong* snd        snd         []       = []
cong* (∗l u)     (∗l .u)     []       = []
cong* (∗r t₁)    (∗r .t₁)    []       = []
cong* abs        abs         []       = []
cong* next        next           []       = []
cong* C1         C2          (x ∷ t⇒) = cong C1 (proj₂ ((mkHole _))) x ∷ cong* (proj₂ ((mkHole _))) C2 t⇒
\end{code}
}
\begin{code}
subst⇒β*₀ : ∀ {n m vt a Γ} {t t' : Tm Γ a} {Δ} (σ : RenSub {m} vt Γ Δ) → t ⟨ n ⟩⇒β* t' → subst σ t ⟨ n ⟩⇒β* subst σ t'
subst⇒β*₀ σ [] = []
subst⇒β*₀ σ (x ∷ xs) = (subst⇒β σ x) ∷ (subst⇒β*₀ σ xs)
\end{code}
\begin{code}
open import Reduction

nβ⇒β : ∀ {n a Γ} {t t' : Tm Γ a} → t ⟨ n ⟩⇒β t' → t ⇒β t'
nβ⇒β β = β
nβ⇒β β▸ = β▸
nβ⇒β βfst = βfst
nβ⇒β βsnd = βsnd
nβ⇒β (cong C1 C2 t⇒) = cong (help C1) (help C2) (nβ⇒β t⇒)
 where
    help' : ∀ {n a Γ} {n₁ Δ a₁}
           (C : NβCxt Δ Γ a₁ a n₁ n) → βECxt Γ Δ a₁ a
    help' (appl u) = appl u
    help' (appr t) = appr t
    help' (pairl u) = pairl u
    help' (pairr t) = pairr t
    help' fst = fst
    help' snd = snd
    help' (∗l u) = ∗l u
    help' (∗r t) = (∗r t)
    help' abs = abs
    help' next = next

    help : ∀ {n a Γ} {t : Tm Γ a} {n₁ Δ a₁} {t₁ : Tm Δ a₁}
           {C : NβCxt Δ Γ a₁ a n₁ n}
           (C1 : NβHole t C t₁) →
           βEHole t (help' C) t₁
    help (appl u) = appl u
    help (appr t) = appr t
    help (pairl u) = pairl u
    help (pairr t) = pairr t
    help fst = fst
    help snd = snd
    help (∗l u) = ∗l u
    help (∗r t) = (∗r t)
    help abs = abs
    help next = next


nβ*⇒β* : ∀ {n a Γ} {t t' : Tm Γ a} → t ⟨ n ⟩⇒β* t' → t ⇒β* t'
nβ*⇒β* [] = []
nβ*⇒β* (x ∷ xs) = nβ⇒β x ∷ nβ*⇒β* xs
\end{code}

\begin{code}
mapNβSNe  : ∀ {i n m a Γ} {t t' : Tm Γ a} → t ⟨ m ⟩⇒β t' → SNe {i} n t  → SNe {i} n t'
mapNβSN   : ∀ {i n m a Γ} {t t' : Tm Γ a} → t ⟨ m ⟩⇒β t' → SN {i} n t   → SN {i} n t'
\end{code}
\AgdaHide{
\begin{code}
mapNβSNe t⇒ 𝒕 = mapβSNe (nβ⇒β t⇒) 𝒕
mapNβSN t⇒ 𝒕 = mapβSN (nβ⇒β t⇒) 𝒕
\end{code}
}

\begin{code}
_[_]⇒β : ∀ {Γ} {n} {a b} (E : ECxt Γ a b) {t₁ t₂ : Tm Γ a} →  t₁ ⟨ n ⟩⇒β t₂ → E [ t₁ ] ⟨ n ⟩⇒β E [ t₂ ]
\end{code}
\AgdaHide{
\begin{code}
appl u [ t⇒ ]⇒β = cong (appl u) (appl u) t⇒
fst [ t⇒ ]⇒β = cong fst fst t⇒
snd [ t⇒ ]⇒β = cong snd snd t⇒
(∗l u) [ t⇒ ]⇒β = cong (∗l u) (∗l u) t⇒
(∗r t) [ t⇒ ]⇒β = cong (∗r (next t)) (∗r (next t)) t⇒
\end{code}
}
\begin{code}
_[_]⇒β* : ∀ {Γ} {n} {a b} (E : ECxt* Γ a b) {t₁ t₂ : Tm Γ a} → t₁ ⟨ n ⟩⇒β t₂ → E [ t₁ ]* ⟨ n ⟩⇒β E [ t₂ ]*
\end{code}
\AgdaHide{
\begin{code}
[]       [ t⇒ ]⇒β* = t⇒
(E ∷ Es) [ t⇒ ]⇒β* = Es [ E [ t⇒ ]⇒β ]⇒β*
\end{code}
}


\AgdaHide{
\begin{code}
mutual
  EC→NβEC : ∀ {Γ} {n a b} (E : ECxt Γ a b) → NβCxt Γ Γ a b n n
  EC→NβEC (appl u) = appl u
  EC→NβEC fst = fst
  EC→NβEC snd = snd
  EC→NβEC (∗l u) = ∗l u
  EC→NβEC (∗r t) = ∗r (next t)

  mkHole2 : ∀ {Γ} {n a b} (E : ECxt Γ a b) {t : Tm Γ a} → NβHole (E [ t ]) (EC→NβEC {n = n} E) t
  mkHole2 (appl u) = appl u
  mkHole2 fst = fst
  mkHole2 snd = snd
  mkHole2 (∗l u) = ∗l u
  mkHole2 (∗r t) = ∗r (next t)

mkHole3 : ∀ {Γ} {n a b c} (E : ECxt Γ a b) {Es : ECxt* Γ _ _} {t : Tm Γ c} → NβHole ((Es ∷r E) [ t ]*) (EC→NβEC {n = n} E) (Es [ t ]*)
mkHole3 E {Es} {t} rewrite ≡.sym (lemma {t = t} Es {E = E}) = mkHole2 E {Es [ t ]*}

≡subst⇒β : ∀ {n a Γ} {t t1 t' t'1 : Tm Γ a} → t ≡ t1 → t' ≡ t'1 → t ⟨ n ⟩⇒β t' → t1 ⟨ n ⟩⇒β t'1
≡subst⇒β ≡.refl ≡.refl x = x
\end{code}
}

\begin{code}
data _Redex {Γ} : ∀ {a} → Tm Γ a → Set where

  β     : ∀ {a b}{t : Tm (a ∷ Γ) b}{u}
          → (app (abs t) u) Redex

  β▸    : ∀ {a∞ b∞}{t : Tm Γ (force (a∞ ⇒ b∞))}{u : Tm Γ (force a∞)}
           → (next {a∞ = a∞ ⇒ b∞} t ∗ next u) Redex

  βfst  : ∀ {a b}{t : Tm Γ a}{u : Tm Γ b}
          → fst (pair t u) Redex

  βsnd  : ∀ {a b}{t : Tm Γ a}{u : Tm Γ b}
          → snd (pair t u) Redex
\end{code}
\begin{code}
split : ∀ {Γ} {n} {a b} (E : ECxt* Γ a b) {t₁ : Tm Γ a}{t₂ Et₁ : Tm Γ b} →
         EHole* Et₁ E t₁ → t₁ Redex →
         Et₁ ⟨ n ⟩⇒β t₂ → (∃ λ t₃ → (EHole* t₂ E t₃) × (t₁ ⟨ n ⟩⇒β t₃))
         ⊎ (∃ λ E₁ → EHole* t₂ E₁ t₁ × (∀ t → E [ t ]* ⟨ n ⟩⇒β E₁ [ t ]*))
\end{code}
\AgdaHide{
\begin{code}
split ._ [] r t⇒ = inj₁ (_ , [] , t⇒)
split .(appl u ∷ []) (appl u ∷ []) () β
split ._ (appl u ∷ (() ∷ eq)) r β
split ._ ((∗l ._) ∷ []) () β▸
split ._ ((∗l ._) ∷ (() ∷ eq)) r β▸
split .((∗r t) ∷ []) ((∗r t) ∷ []) () β▸
split ._ ((∗r t) ∷ (() ∷ eq)) r β▸
split ._ (fst ∷ (() ∷ eq)) r βfst
split .(fst ∷ []) (fst ∷ []) () βfst
split .(snd ∷ []) (snd ∷ []) () βsnd
split ._ (snd ∷ (() ∷ eq)) r βsnd
split ._ (appl u ∷ eq) r (cong (appl .u) (appl .u) t⇒) with split _ eq r t⇒
split ._ (appl u ∷ eq) r (cong (appl .u) (appl .u) t⇒) | inj₁ (x , eq0 , t⇒') = inj₁ (_ , ((appl u) ∷ eq0) , t⇒')
split ._ (_∷_ {Es = Es} (appl u) eq) r (cong (appl .u) (appl .u) t⇒) | inj₂ (Es' , eq0 , f) = inj₂ (_ , ((appl u ∷ eq0) ,
                                                        (λ t → cong (mkHole3 (appl u) {Es}) (mkHole3 (appl u) {Es'}) (f t))))
split ._ (_∷_ {Es = Es} (appl t) eq) r (cong (appr Est) (appr .Est) t⇒) = inj₂ (_ , ((appl _ ∷ eq) ,
      (λ t₁ → ≡subst⇒β (lemma Es) (lemma Es) (cong (appr (Es [ t₁ ]*)) (appr (Es [ t₁ ]*)) t⇒))))
split ._ (fst ∷ eq) r (cong fst fst t⇒) with split _ eq r t⇒
split ._ (fst ∷ eq) r (cong fst fst t⇒) | inj₁ (_ , eq0 , t⇒') = inj₁ (_ , (fst ∷ eq0) , t⇒')
split ._ (_∷_ {Es = Es} fst eq) r (cong fst fst t⇒) | inj₂ (Es' , eq0 , f)
      = inj₂ (_ , (fst ∷ eq0) , (λ t → cong (mkHole3 fst {Es}) (mkHole3 fst {Es'}) (f t)))
split ._ (snd ∷ eq) r (cong snd snd t⇒) with split _ eq r t⇒
split ._ (snd ∷ eq) r (cong snd snd t⇒) | inj₁ (_ , eq0 , t⇒') = inj₁ (_ , (snd ∷ eq0) , t⇒')
split ._ (_∷_ {Es = Es} snd eq) r (cong snd snd t⇒) | inj₂ (Es' , eq0 , f)
      = inj₂ (_ , (snd ∷ eq0) , (λ t → cong (mkHole3 snd {Es}) (mkHole3 snd {Es'}) (f t)))
split ._ (_∷_ {Es = Es} (∗l u) eq) r (cong (∗l .u) (∗l .u) t⇒) with split _ eq r t⇒
... | inj₁ (_ , eq0 , t⇒') = inj₁ (_ , ∗l u ∷ eq0 , t⇒')
... | inj₂ (Es' , eq0 , f)   = inj₂ (_ , (∗l u) ∷ eq0 , (λ t → cong (mkHole3 (∗l u) {Es}) (mkHole3 (∗l u) {Es'}) (f t)))
split ._ (_∷_ {Es = Es} (∗r t) eq) r (cong (∗l Est) (∗l .Est) (cong next next t⇒)) = inj₂ (_ , (∗r _ ∷ eq) ,
      (λ t₁ → ≡subst⇒β (lemma Es) (lemma Es) (cong (∗l (Es [ t₁ ]*)) (∗l (Es [ t₁ ]*)) (cong next next t⇒)))) --
split ._ (_∷_ {Es = Es} (∗l t) eq) r (cong (∗r Est) (∗r .Est) t⇒) = inj₂ (_ , (∗l _) ∷ eq , (λ t₁ → ≡subst⇒β (lemma Es) (lemma Es) (cong (∗r _) (∗r _) t⇒)))
split ._ (_∷_ {Es = Es} (∗r t) eq) r (cong (∗r .(next t)) (∗r .(next t)) t⇒) with split _ eq r t⇒
... | inj₁ (_ , eq0 , t⇒') = inj₁ (_ , ∗r t ∷ eq0 , t⇒')
... | inj₂ (Es' , eq0 , f)   = inj₂ (_ , ∗r t ∷ eq0 , (λ t1 → cong (mkHole3 (∗r t) {Es}) (mkHole3 (∗r t) {Es'}) (f t1)))

cong*2 : ∀ {Γ n a b t t'}(E : ECxt* Γ a b)
          → (t⇒ : t ⟨ n ⟩⇒β t')
          → E [ t ]* ⟨ n ⟩⇒β E [ t' ]*
cong*2 E t⇒ = E [ t⇒ ]⇒β*
\end{code}
}
