{-# OPTIONS --copatterns --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --show-implicit #-}
{-# OPTIONS --no-termination-check #-} -- too slow

module SN where

open import Relation.Unary using (_∈_; _⊆_)

open import Library
open import SizedInfiniteTypes
open import Terms
open import Substitution


-- Evaluation contexts.

data ECxt (Γ : Cxt) : (a b : Ty) → Set where
  appl  : ∀ {a b} (u : Tm Γ a)  → ECxt Γ (a →̂ b) b
  fst   : ∀ {a b} → ECxt Γ (a ×̂ b) a
  snd   : ∀ {a b} → ECxt Γ (a ×̂ b) b
  _∗l   : ∀ {a b∞} (u : Tm Γ (▸ a)) → ECxt Γ (▸̂ (delay a ⇒ b∞)) (▸̂ b∞)
  ∗r_   : ∀ {a : Ty}{b∞} (t : Tm Γ (a →̂ force b∞)) → ECxt Γ (▸ a) (▸̂ b∞)

-- Ehole Et E t ~~ Et = E[t]

data Ehole {Γ : Cxt} : {a b : Ty} → Tm Γ b → ECxt Γ a b → Tm Γ a → Set where
  appl  : ∀ {a b t} (u : Tm Γ a)  → Ehole (app t u) (appl u) (t ∶ (a →̂ b))
  fst   : ∀ {a b t} → Ehole {a = a ×̂ b} (fst t) fst t
  snd   : ∀ {a b t} → Ehole {a = a ×̂ b} (snd t) snd t
  _∗l   : ∀ {a b∞ t} (u : Tm Γ (▸ a)) → Ehole {a = (▸̂ (delay a ⇒ b∞))} (t ∗ u) (u ∗l) t
  ∗r_   : ∀ {a : Ty}{b∞}{u} (t : Tm Γ (a →̂ force b∞)) → Ehole (((▹ t) ∗ (u ∶ ▸ a)) ∶ ▸̂ b∞) (∗r t) u


-- Evaluation contexts are closed under substitution.

substEC : ∀ {i vt Γ Δ a b} → (σ : RenSub {i} vt Γ Δ) → ECxt Γ a b → ECxt Δ a b
substEC σ (appl u) = appl (subst σ u)
substEC σ fst      = fst
substEC σ snd      = snd
substEC σ (u ∗l)   = subst σ u ∗l
substEC σ (∗r t₁)  = ∗r subst σ t₁

substEh : ∀ {i vt Γ Δ a b} → (σ : RenSub {i} vt Γ Δ) → ∀ {E}{Et : Tm Γ b}{t : Tm Γ a} → (Eh : Ehole Et E t)
            → Ehole (subst σ Et) (substEC σ E) (subst σ t)
substEh σ (appl u) = appl (subst σ u)
substEh σ fst      = fst
substEh σ snd      = snd
substEh σ (u ∗l)   = subst σ u ∗l
substEh σ (∗r t₁)  = ∗r subst σ t₁


-- Inductive definition of strong normalization.

mutual

  -- Strongly normalizing evaluation contexts

  data SNhole (n : ℕ) {Γ : Cxt} : {a b : Ty} → Tm Γ b → ECxt Γ a b → Tm Γ a → Set where

    appl  : ∀ {a b t u}
            → (𝒖 : SN n u)
            → SNhole n (app t u) (appl u) (t ∶ (a →̂ b))

    fst   : ∀ {a b t}                 → SNhole n (fst {a = a} {b = b} t) fst t

    snd   : ∀ {a b t}                 → SNhole n (snd {a = a} {b = b} t) snd t

    _∗l   : ∀ {a b∞ t u} (𝒖 : SN n u) → SNhole n (_∗_ {a = a} {b∞} t u) (u ∗l) t

    ∗r_   : ∀ {a : Ty}{b∞}{u t}
              (𝒕 : SN n (▹_ {a∞ = delay (a →̂ force b∞)} t))
                                      → SNhole n (_<$>_ {a = a} {b∞} t u) (∗r t) u

  -- Strongly neutral terms.

  data SNe (n : ℕ) {Γ} {b} : Tm Γ b → Set where

    var  : ∀ x                              → SNe n (var x)

    elim : ∀ {a} {t : Tm Γ a} {E Et}
           → (𝒏 : SNe n t) (𝑬𝒕 : SNhole n Et E t) → SNe n Et

  -- Strongly normalizing terms.

  data SN {Γ} : ℕ → ∀ {a} → Tm Γ a → Set where

    ne   : ∀ {a n t}
           → (𝒏 : SNe n t)
           → SN n {a} t

    abs  : ∀ {a b n}{t : Tm (a ∷ Γ) b}
           → (𝒕 : SN n t)
           → SN n (abs t)

    pair : ∀ {a b n t u}
           → (𝒕 : SN n t) (𝒖 : SN n u)
           → SN n {a ×̂ b} (pair t u)

    ▹0_  : ∀ {a∞} {t : Tm Γ (force a∞)}
           → SN 0 {▸̂ a∞} (▹ t)

    ▹_   : ∀ {a∞ n} {t : Tm Γ (force a∞)}
           → (𝒕 : SN n t)
           → SN (suc n) {▸̂ a∞} (▹ t)

    exp  : ∀{a n t t′}
           → (t⇒ : t ⟨ n ⟩⇒ t′) (𝒕′ : SN n t′)
           → SN n {a} t

  -- Strong head reduction

  data _⟨_⟩⇒_ {Γ} : ∀ {a} → Tm Γ a → ℕ → Tm Γ a → Set where

    β     : ∀ {n a b}{t : Tm (a ∷ Γ) b}{u}
            → (𝒖 : SN n u)
            → (app (abs t) u) ⟨ n ⟩⇒ subst0 u t

    β▹    : ∀ {n a b∞}{t : Tm Γ (a →̂  force b∞)}{u : Tm Γ a}
             → (▹ t ∗ ▹ u) ⟨ n ⟩⇒ (▹_ {a∞ = b∞} (app t u))

    βfst  : ∀ {n a b}{t : Tm Γ a}{u : Tm Γ b}
            → (𝒖 : SN n u)
            → fst (pair t u) ⟨ n ⟩⇒ t

    βsnd  : ∀ {n a b}{t : Tm Γ a}{u : Tm Γ b}
            → (𝒕 : SN n t)
            → snd (pair t u) ⟨ n ⟩⇒ u

    cong  : ∀ {n a b t t' Et Et'}{E : ECxt Γ a b}
            → (𝑬𝒕 : Ehole Et E t)
            → (𝑬𝒕' : Ehole Et' E t')
            → (t⇒ : t ⟨ n ⟩⇒ t')
            → Et ⟨ n ⟩⇒ Et'

-- Strong head reduction is deterministic.

det⇒ : ∀ {n a Γ} {t t₁ t₂ : Tm Γ a}
       → (t⇒₁ : t ⟨ n ⟩⇒ t₁) (t⇒₂ : t ⟨ n ⟩⇒ t₂) → t₁ ≡ t₂
det⇒ (β _) (β _)                                              = ≡.refl
det⇒ (β _) (cong (appl u) (appl .u) (cong () _ _))
det⇒ β▹ β▹ = ≡.refl
det⇒ β▹ (cong (._ ∗l) (._ ∗l) (cong () _ _))
det⇒ β▹ (cong (∗r t) (∗r .t) (cong () _ _ ))
det⇒ (βfst _) (βfst _)                                        = ≡.refl
det⇒ (βfst _) (cong fst fst (cong () _ _))
det⇒ (βsnd _) (βsnd _)                                        = ≡.refl
det⇒ (βsnd 𝒕) (cong snd snd (cong () _ _))
det⇒ (cong (appl u) (appl .u) (cong () _ _)) (β _)
det⇒ (cong (._ ∗l) (._ ∗l) (cong () _ _)) β▹
det⇒ (cong (∗r t₁) (∗r .t₁) (cong () _ _)) β▹
det⇒ (cong fst fst (cong () _ _ )) (βfst _)
det⇒ (cong snd snd (cong () _ _ )) (βsnd _)
det⇒ (cong (appl u) (appl .u) x) (cong (appl .u) (appl .u) y) = ≡.cong (λ t → app t u) (det⇒ x y)
det⇒ (cong fst fst x) (cong fst fst y)                        = ≡.cong fst             (det⇒ x y)
det⇒ (cong snd snd x) (cong snd snd y)                        = ≡.cong snd             (det⇒ x y)
det⇒ (cong (u ∗l) (.u ∗l) x) (cong (.u ∗l) (.u ∗l) y)         = ≡.cong (λ t → t ∗ u)   (det⇒ x y)
det⇒ (cong (∗r t) (∗r .t) x) (cong (∗r .t) (∗r .t) y)         = ≡.cong (_∗_ (▹ t))     (det⇒ x y)
det⇒ (cong (u ∗l) (.u ∗l) (cong () _ _)) (cong (∗r t) (∗r .t) _)
det⇒ (cong (∗r t) (∗r .t) _) (cong (u ∗l) (.u ∗l) (cong () _ _))

-- Strongly neutrals are closed under application.

sneApp : ∀{n Γ a b}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} →
  SNe n t → SN n u → SNe n (app t u)
sneApp 𝒏 𝒖 = elim 𝒏 (appl 𝒖)

-- Functoriality of the SN-notions wrt. evaluation depth n.

mutual
  mapSNe : ∀ {m n} → m ≤ℕ n → ∀ {Γ a}{t : Tm Γ a} → SNe n t -> SNe m t
  mapSNe m≤n (var x) = var x
  mapSNe m≤n (elim t∈Ne E∈SNh) = elim (mapSNe m≤n t∈Ne) (mapSNh m≤n E∈SNh)

  mapSN : ∀ {m n} → m ≤ℕ n → ∀ {Γ a}{t : Tm Γ a} → SN n t -> SN m t
  mapSN m≤n (ne u∈SNe) = ne (mapSNe m≤n u∈SNe)
  mapSN m≤n (abs t∈SN) = abs (mapSN m≤n t∈SN)
  mapSN m≤n (pair t∈SN u∈SN) = pair (mapSN m≤n t∈SN) (mapSN m≤n u∈SN)
  mapSN z≤n ▹0_ = ▹0_
  mapSN z≤n (▹ t∈SN) = ▹0_
  mapSN (s≤s m≤n) (▹ t∈SN) = ▹ mapSN m≤n t∈SN
  mapSN m≤n (exp t→t' t∈SN) = exp (map⇒ m≤n t→t') (mapSN m≤n t∈SN)

  map⇒ : ∀ {m n} → m ≤ℕ n → ∀ {Γ a}{t t' : Tm Γ a} → t ⟨ n ⟩⇒ t' → t ⟨ m ⟩⇒ t'
  map⇒ m≤n (β t∈SN) = β (mapSN m≤n t∈SN)
  map⇒ m≤n (β▹ {a = a}) = β▹ {a = a}
  map⇒ m≤n (βfst t∈SN) = βfst (mapSN m≤n t∈SN)
  map⇒ m≤n (βsnd t∈SN) = βsnd (mapSN m≤n t∈SN)
  map⇒ m≤n (cong Et Et' t→t') = cong Et Et' (map⇒ m≤n t→t')

  mapSNh : ∀ {m n} → m ≤ℕ n → ∀ {Γ a b}{E : ECxt Γ a b}{Et t} → SNhole n Et E t -> SNhole m Et E t
  mapSNh m≤n (appl u∈SN) = appl (mapSN m≤n u∈SN)
  mapSNh m≤n fst = fst
  mapSNh m≤n snd = snd
  mapSNh m≤n (u∈SN ∗l) = mapSN m≤n u∈SN ∗l
  mapSNh m≤n (∗r t∈SN) = ∗r mapSN m≤n t∈SN



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
isSNe    (sgs-varSNe x) zero    = var x
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
                                                   (≡.trans (≡.sym (subst-∙ (sgs (subst σ u)) (lifts σ) t))
                                                   (≡.trans (subst-ext sgs-lifts t)
                                                   (subst-∙ σ (sgs u) t)))
                                                   (β {t = subst (lifts σ) t} (substSN (σ , σ∈Ne) x))

  subst⇒         σ (β▹ {a = a})        = β▹ {a = a}
  subst⇒         σ (βfst t∈SN)           = βfst (substSN σ t∈SN)
  subst⇒         σ (βsnd u∈SN)           = βsnd (substSN σ u∈SN)
  subst⇒ {n = n} σ (cong Eh Eh' t→t')    = cong (substEh (theSubst σ) Eh) (substEh (theSubst σ) Eh') (subst⇒ σ t→t')

  -- Lifting a SNe substitution.

  liftsSNe : ∀ {i vt Γ Δ a n} → RenSubSNe {i} vt n Γ Δ → RenSubSNe {i} vt n (a ∷ Γ) (a ∷ Δ)
  theSubst (liftsSNe σ)                   = lifts (theSubst σ)
  isSNe    (liftsSNe {vt = `Var} (σ , σ∈SNe)) zero    = var zero
  isSNe    (liftsSNe {vt = `Var} (σ , σ∈SNe)) (suc y) = var (suc (σ y))
  isSNe    (liftsSNe {vt = `Tm } (σ , σ∈SNe)) zero    = var zero
  isSNe    (liftsSNe {vt = `Tm } (σ , σ∈SNe)) (suc y) = substSNe {vt = `Var} (suc , (λ x → var (suc x))) (σ∈SNe y)

  substSNe : ∀ {i vt Γ Δ τ n} → (σ : RenSubSNe {i} vt n Γ Δ) → ∀ {t : Tm Γ τ} → SNe n t → SNe n (subst (theSubst σ) t)
  substSNe σ (var x)            = isSNe σ x
  substSNe σ (elim t∈SNe E∈SNh) = elim (substSNe σ t∈SNe) (substSNh σ E∈SNh)

  substSN : ∀ {i vt Γ Δ τ n} → (σ : RenSubSNe {i} vt n Γ Δ) → ∀ {t : Tm Γ τ} → SN n t → SN n (subst (theSubst σ) t)
  substSN σ (ne t∈SNe)         = ne (substSNe σ t∈SNe)
  substSN σ (abs t∈SN)         = abs (substSN (liftsSNe σ) t∈SN)
  substSN σ (pair t₁∈SN t₂∈SN) = pair (substSN σ t₁∈SN) (substSN σ t₂∈SN)
  substSN σ ▹0_                = ▹0_
  substSN σ (▹ t∈SN)           = ▹ substSN (mapSubSNe n≤sn σ) t∈SN
  substSN σ (exp t→t' t'∈SN)   = exp (subst⇒ σ t→t') (substSN σ t'∈SN)


-- SN is closed under renaming.

renSN :  ∀{n Γ Δ} (ρ : Γ ≤ Δ) → RenSN n Δ Γ
renSN ρ = (ρ , λ x → var (ρ x))

renameSNe : ∀{n a Γ Δ} (ρ : Γ ≤ Δ) {t : Tm Δ a} →
  SNe n t → SNe n (rename ρ t)
renameSNe ρ = substSNe (renSN ρ)

renameSN : ∀{n a Γ Δ} (ρ : Γ ≤ Δ) {t : Tm Δ a} →
  SN n t → SN n (rename ρ t)
renameSN ρ = substSN (renSN ρ)

-- Variables are SN.

varSN : ∀{Γ a n x} → var x ∈ SN {Γ} n {a}
varSN = ne (var _)

-- SN is closed under application to variables.

appVarSN : ∀{Γ a b n}{t : Tm Γ (a →̂ b)}{x} → t ∈ SN n → app t (var x) ∈ SN n
appVarSN (ne t∈SNe)       = ne (elim t∈SNe (appl varSN))
appVarSN (abs t∈SN)       = exp (β varSN) (substSN (sgs-varSNe _) t∈SN)
appVarSN (exp t→t' t'∈SN) = exp (cong (appl (var _)) (appl (var _)) t→t') (appVarSN t'∈SN)

-- Extensionality of SN for function types:
-- If t x ∈ SN then t ∈ SN.

absVarSNe : ∀{Γ a b n}{t : Tm Γ (a →̂ b)} → app (rename suc t) (var zero) ∈ SNe n → t ∈ SNe n
absVarSNe (elim 𝒏 (appl 𝒖)) = TODO

absVarSN : ∀{Γ a b n}{t : Tm Γ (a →̂ b)} → app (rename suc t) (var zero) ∈ SN n → t ∈ SN n
absVarSN (ne 𝒖) = ne (absVarSNe 𝒖)
absVarSN (exp t⇒ 𝒕′) = TODO -- exp {!!} (absVarSN {!𝒕′!})
-- absVarSN (ne (var ())) = {!𝒏!}
-- absVarSN (ne (elim {E = .(λ u → app u (var _))} 𝒏 (appl y))) = {!𝒏!}
-- absVarSN (exp t⇒ x₁) = {!!}

-- Extensionality of SN for product type:
-- If fst t ∈ SN and snd t ∈ SN then t ∈ SN.

bothProjSN : ∀{n a b Γ}{t : Tm Γ (a ×̂ b)} →
  (𝒕₁ : SN n (fst t)) (𝒕₂ : SN n (snd t)) → SN n t
bothProjSN (ne (elim 𝒏 fst))    _                 = ne 𝒏
bothProjSN (exp (βfst 𝒕₂) 𝒕₁)    _                 = pair 𝒕₁ 𝒕₂
bothProjSN (exp (cong _ _ _) _) (ne (elim 𝒏 snd))  = ne 𝒏
bothProjSN (exp (cong _ _ _) _) (exp (βsnd 𝒕₁) 𝒕₂) = pair 𝒕₁ 𝒕₂
bothProjSN (exp (cong fst fst t⇒₁) 𝒕₁) (exp (cong snd snd t⇒₂) 𝒕₂) rewrite det⇒ t⇒₁ t⇒₂ = exp t⇒₂ (bothProjSN 𝒕₁ 𝒕₂)
