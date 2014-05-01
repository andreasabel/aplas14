{-# OPTIONS --copatterns --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
--{-# OPTIONS --show-implicit #-}

module NReduction where

open import Data.Sum
open import Library
open import SizedInfiniteTypes
open import Terms
open import Substitution
open import SN

data NβECxt (Γ : Cxt) : (Δ : Cxt) (a b : Ty) → (n n' : ℕ) → Set where
  appl  : ∀ {n a b} (u : Tm Γ a)                        → NβECxt Γ Γ (a →̂ b) b n n 
  appr  : ∀ {n a b} (t : Tm Γ (a →̂  b))                 → NβECxt Γ Γ a b n n 
  pairl : ∀ {n a b} (u : Tm Γ b)                        → NβECxt Γ Γ a (a ×̂ b) n n 
  pairr : ∀ {n a b} (t : Tm Γ a)                        → NβECxt Γ Γ b (a ×̂ b) n n 
  fst   : ∀ {n a b}                                     → NβECxt Γ Γ (a ×̂ b) a n n 
  snd   : ∀ {n a b}                                     → NβECxt Γ Γ (a ×̂ b) b n n 
  _∗l   : ∀ {n a b∞} (u : Tm Γ (▸ a))                   → NβECxt Γ Γ (▸̂ (delay a ⇒ b∞)) (▸̂ b∞) n n 
  ∗r_   : ∀ {n}{a : Ty}{b∞} (t : Tm Γ (▸̂ (delay a ⇒ b∞))) → NβECxt Γ Γ (▸ a) (▸̂ b∞) n n 
  abs   : ∀ {n a b}                                     → NβECxt Γ (a ∷ Γ) b (a →̂  b) n n 
  ▹_    : ∀ {n a∞}                                      → NβECxt Γ Γ (force a∞) (▸̂  a∞) n (suc n) 

data NβEhole {n : ℕ} {Γ : Cxt} : {n' : ℕ} → {Δ : Cxt} {b a : Ty} → Tm Γ b → NβECxt Γ Δ a b n n' → Tm Δ a → Set where
  appl  : ∀ {a b t} (u : Tm Γ a)                          → NβEhole (app t u) (appl u) (t ∶ (a →̂ b)) 
  appr  : ∀ {a b u} (t : Tm Γ (a →̂  b))                   → NβEhole (app t u) (appr t) u
  pairl : ∀ {a b}{t} (u : Tm Γ b)                         → NβEhole (pair t u) (pairl u) (t ∶ a)
  pairr : ∀ {a b}{u} (t : Tm Γ a)                         → NβEhole (pair t u) (pairr t) (u ∶ b)
  fst   : ∀ {a b t}                                       → NβEhole {a = a ×̂ b} (fst t) fst t
  snd   : ∀ {a b t}                                       → NβEhole {a = a ×̂ b} (snd t) snd t
  _∗l   : ∀ {a b∞ t} (u : Tm Γ (▸ a))                     → NβEhole {a = (▸̂ (delay a ⇒ b∞))} (t ∗ u) (u ∗l) t
  ∗r_   : ∀ {a : Ty}{b∞}{u} (t : Tm Γ (▸̂ (delay a ⇒ b∞))) → NβEhole ((t ∗ (u ∶ ▸ a)) ∶ ▸̂ b∞) (∗r t) u
  abs   : ∀ {a b} {t : Tm (a ∷ Γ) b}                      → NβEhole (abs t) abs t
  ▹_    : ∀ {a∞} {t : Tm Γ (force a∞)}                    → NβEhole (▹_ {a∞ = a∞} t) ▹_ t


mkHole : ∀ {n n' Γ Δ} {a b} (E : NβECxt Γ Δ a b n n') {t} → Σ _ \ E[t] → NβEhole E[t] E t
mkHole (appl u)  = _ , appl u
mkHole (appr t)  = _ , appr t
mkHole (pairl u) = _ , pairl u
mkHole (pairr t) = _ , pairr t
mkHole fst       = _ , fst
mkHole snd       = _ , snd
mkHole (u ∗l)    = _ , u ∗l
mkHole (∗r t)    = _ , ∗r t
mkHole abs       = _ , abs
mkHole ▹_        = _ , ▹_
{-
NβE = \ Γ₀ a₀ n₁ Γ₁ a₁ n₀ → NβECxt Γ₁ Γ₀ a₀ a₁ n₀ n₁

_[_] : ∀ {n n' Γ Δ} {a b} (E : NβE Δ a n Γ b n') (t : Tm Δ a) → Tm Γ b
E [ t ] = proj₁ (mkHole E {t})


data NβE* : Cxt → Ty → ℕ → Cxt → Ty → ℕ → Set where
  [] : ∀ {Γ a n} → NβE* Γ a n Γ a n
  _∷_ : ∀ {Γ₀ a₀ n₀ Γ₁ a₁ n₁ Γ₂ a₂ n₂} → NβE Γ₀ a₀ n₀  Γ₁ a₁ n₁ → NβE* Γ₁ a₁ n₁ Γ₂ a₂ n₂ → 
          NβE* Γ₀ a₀ n₀  Γ₂ a₂ n₂

_[_]* : ∀ {n n' Γ Δ} {a b} (E : NβE* Δ a n Γ b n') (t : Tm Δ a) → Tm Γ b
[] [ t ]* = t
(E ∷ Es) [ t ]* = Es [ E [ t ] ]*
-}

data _⟨_⟩⇒β_ {Γ} : ∀ {a} → Tm Γ a → ℕ → Tm Γ a → Set where

  β     : ∀ {n a b}{t : Tm (a ∷ Γ) b}{u}
          → (app (abs t) u) ⟨ n ⟩⇒β subst0 u t

  β▹    : ∀ {n a b∞}{t : Tm Γ (a →̂  force b∞)}{u : Tm Γ a}
           → (▹ t ∗ ▹ u) ⟨ n ⟩⇒β (▹_ {a∞ = b∞} (app t u))

  βfst  : ∀ {n a b}{t : Tm Γ a}{u : Tm Γ b}
          → fst (pair t u) ⟨ n ⟩⇒β t

  βsnd  : ∀ {n a b}{t : Tm Γ a}{u : Tm Γ b}
          → snd (pair t u) ⟨ n ⟩⇒β u

  cong  : ∀ {n n' Δ a b t t' Et Et'}{E : NβECxt Γ Δ a b n n'}
          → (𝑬𝒕 : NβEhole Et E t)
          → (𝑬𝒕' : NβEhole Et' E t')
          → (t⇒β : t ⟨ n ⟩⇒β t')
          → Et ⟨ n' ⟩⇒β Et'
--  cong▹ : ∀ {n a∞} {t t' : Tm Γ (force a∞)} →  (t⇒β : t ⟨ n ⟩⇒β t') → (▹_ {a∞ = a∞} t) ⟨ suc n ⟩⇒β (▹_ {a∞ = a∞} t')

subst⇒β : ∀ {n m vt a Γ} {t t' : Tm Γ a} {Δ}
           (σ : RenSub {m} vt Γ Δ) → t ⟨ n ⟩⇒β t' → subst σ t ⟨ n ⟩⇒β subst σ t'
subst⇒β {n} σ (β {t = t} {u = u})            = ≡.subst (λ t' → app (abs (subst (lifts σ) t)) (subst σ u) ⟨ n ⟩⇒β t')
                                                   (sgs-lifts-term {σ = σ} {u} {t})
                                           β
subst⇒β σ β▹                             = β▹
subst⇒β σ βfst                           = βfst
subst⇒β σ βsnd                           = βsnd
subst⇒β σ (cong (appl u) (appl .u) t⇒)   = cong (appl _) (appl _) (subst⇒β σ t⇒)
subst⇒β σ (cong (appr t₁) (appr .t₁) t⇒) = cong (appr _) (appr _) (subst⇒β σ t⇒)
subst⇒β σ (cong fst fst t⇒)              = cong fst fst (subst⇒β σ t⇒)
subst⇒β σ (cong snd snd t⇒)              = cong snd snd (subst⇒β σ t⇒)
subst⇒β σ (cong (u ∗l) (.u ∗l) t⇒)       = cong (_ ∗l) (_ ∗l) (subst⇒β σ t⇒)
subst⇒β σ (cong (∗r t₁) (∗r .t₁) t⇒)     = cong (∗r _) (∗r _) (subst⇒β σ t⇒)
subst⇒β σ (cong abs abs t⇒)              = cong abs abs (subst⇒β (lifts σ) t⇒)
subst⇒β σ (cong ▹_ ▹_ t⇒)                = cong ▹_ ▹_ (subst⇒β σ t⇒)
subst⇒β σ (cong (pairr t) (pairr ._) t⇒) = cong (pairr (subst σ t)) (pairr _) (subst⇒β σ t⇒)
subst⇒β σ (cong (pairl u) (pairl ._) t⇒) = cong (pairl (subst σ u)) (pairl _) (subst⇒β σ t⇒)

data _⟨_⟩⇒β*_ {Γ} {a} : Tm Γ a → ℕ → Tm Γ a → Set where
  []  : ∀ {n t} → t ⟨ n ⟩⇒β* t
  _∷_ : ∀ {n ti tm to} → ti ⟨ n ⟩⇒β tm → tm ⟨ n ⟩⇒β* to → ti ⟨ n ⟩⇒β* to

_++β_ : ∀ {n} {Γ} {a} {t₀ t₁ t₂ : Tm Γ a} → t₀ ⟨ n ⟩⇒β* t₁ → t₁ ⟨ n ⟩⇒β* t₂ → t₀ ⟨ n ⟩⇒β* t₂
[] ++β ys = ys
(x ∷ xs) ++β ys = x ∷ (xs ++β ys)

cong* : ∀ {n n' a Γ Δ} {b} {t tβ* : Tm Γ a} {E : NβECxt Δ Γ a b n n'}{E[t] E[tβ*]} → NβEhole E[t] E t → NβEhole E[tβ*] E tβ* → t ⟨ n ⟩⇒β* tβ* → E[t] ⟨ n' ⟩⇒β* E[tβ*]
cong* (appl u)   (appl .u)   []       = []
cong* (appr t₁)  (appr .t₁)  []       = []
cong* (pairl u)  (pairl .u)  []       = []
cong* (pairr t₁) (pairr .t₁) []       = []
cong* fst        fst         []       = []
cong* snd        snd         []       = []
cong* (u ∗l)     (.u ∗l)     []       = []
cong* (∗r t₁)    (∗r .t₁)    []       = []
cong* abs        abs         []       = []
cong* ▹_        ▹_           []       = []
cong* E1         E2          (x ∷ t⇒) = cong E1 (proj₂ ((mkHole _))) x ∷ cong* (proj₂ ((mkHole _))) E2 t⇒


subst⇒β*₀ : ∀ {n m vt a Γ} {t t' : Tm Γ a} {Δ} (σ : RenSub {m} vt Γ Δ) → t ⟨ n ⟩⇒β* t' → subst σ t ⟨ n ⟩⇒β* subst σ t'
subst⇒β*₀ σ [] = []
subst⇒β*₀ σ (x ∷ xs) = (subst⇒β σ x) ∷ (subst⇒β*₀ σ xs)

open import Reduction

nβ⇒β : ∀ {n a Γ} {t t' : Tm Γ a} → t ⟨ n ⟩⇒β t' → t ⇒β t'
nβ⇒β β = β
nβ⇒β β▹ = β▹
nβ⇒β βfst = βfst
nβ⇒β βsnd = βsnd
nβ⇒β (cong E1 E2 t⇒) = cong (help E1) (help E2) (nβ⇒β t⇒)
 where
    help' : ∀ {n a Γ} {n₁ Δ a₁}
           (E : NβECxt Γ Δ a₁ a n₁ n) → βECxt Γ Δ a₁ a
    help' (appl u) = appl u
    help' (appr t) = appr t
    help' (pairl u) = pairl u
    help' (pairr t) = pairr t
    help' fst = fst
    help' snd = snd
    help' (u ∗l) = u ∗l
    help' (∗r t) = (∗r t)
    help' abs = abs
    help' ▹_ = ▹_

    help : ∀ {n a Γ} {t : Tm Γ a} {n₁ Δ a₁} {t₁ : Tm Δ a₁} 
           {E : NβECxt Γ Δ a₁ a n₁ n} 
           (E1 : NβEhole t E t₁) →
           βEhole t (help' E) t₁
    help (appl u) = appl u
    help (appr t) = appr t
    help (pairl u) = pairl u
    help (pairr t) = pairr t
    help fst = fst
    help snd = snd
    help (u ∗l) = u ∗l
    help (∗r t) = (∗r t)
    help abs = abs
    help ▹_ = ▹_


nβ*⇒β* : ∀ {n a Γ} {t t' : Tm Γ a} → t ⟨ n ⟩⇒β* t' → t ⇒β* t'
nβ*⇒β* [] = []
nβ*⇒β* (x ∷ xs) = nβ⇒β x ∷ nβ*⇒β* xs 

mapNβSNe : ∀ {i n m a Γ} {t t' : Tm Γ a} → t ⟨ m ⟩⇒β t' → SNe {i} n t → SNe {i} n t'
mapNβSNe t⇒ 𝒕 = mapβSNe (nβ⇒β t⇒) 𝒕 

mapNβSN : ∀ {i n m a Γ} {t t' : Tm Γ a} → t ⟨ m ⟩⇒β t' → SN {i} n t → SN {i} n t'
mapNβSN t⇒ 𝒕 = mapβSN (nβ⇒β t⇒) 𝒕

