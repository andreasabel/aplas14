{-# OPTIONS --copatterns --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

module SN where

open import Relation.Unary using (_∈_; _⊆_)

open import Library
open import SizedInfiniteTypes
open import Terms
open import Substitution

-- TODOs

postulate
  TODO : ∀ {a}{A : Set a} → A

-- Term contexts which do not include binders.

TmCxt : (Γ : Cxt) (a b : Ty) → Set
TmCxt Γ a b = Tm Γ a → Tm Γ b

-- Evaluation Contexts

data Ehole {Γ : Cxt} : {a b : Ty} → TmCxt Γ a b → Set where
  appl  : ∀ {a b} (u : Tm Γ a)  → Ehole (λ (t : Tm Γ (a →̂ b)) → app t u)
  fst   : ∀ {a b} → Ehole {a = a ×̂ b} fst
  snd   : ∀ {a b} → Ehole {a = a ×̂ b} snd
  _∗l   : ∀ {a b∞} (u : Tm Γ (▸ a)) → Ehole {a = (▸̂ (delay a ⇒ b∞))} (λ t → t ∗ u)
  ∗r_   : ∀ {a : Ty}{b∞} (t : Tm Γ (a →̂ force b∞)) → Ehole (λ u → ▸̂ b∞ ∶ ((▹ t) ∗ (▸ a ∶ u)))


mutual

-- Strongly normalizing evaluation contexts

  data SNhole (n : ℕ) {Γ : Cxt} : {a b : Ty} → TmCxt Γ a b → Set where
    appl  : ∀ {a b u} → SN n u     → SNhole n (λ t → b ∶ app t (a ∶ u))
    fst   : ∀ {a b}                → SNhole n (fst {a = a} {b = b})
    snd   : ∀ {a b}                → SNhole n (snd {a = a} {b = b})
    _∗l   : ∀ {a b∞ u} → SN n u    → SNhole n (λ t → _∗_ {a = a} {b∞} t u)
    ∗r_   : ∀ {a : Ty}{b∞ t} → SN n (▹_ {a∞ = delay (a →̂ force b∞)} t)
                                   → SNhole n (λ u → _<$>_ {a = a} {b∞} t u)

  data SNe (n : ℕ) {Γ} {b} : Tm Γ b → Set where
    var  : ∀ x                    → SNe n (var x)
    elim : ∀ {a} {t : Tm Γ a} {E}
           → SNe n t → SNhole n E → SNe n (E t)

  -- Strongly normalizing

  data SN {Γ} : ℕ → ∀ {a} → Tm Γ a → Set where
    ne   : ∀{a n t}     → SNe n t            → SN n {a} t
    abs  : ∀{a b n t}   → SN {a ∷ Γ} n {b} t → SN n (abs t)
    pair : ∀{a b n t u} → SN n t → SN n u    → SN n {a ×̂ b} (pair t u)
    ▹0_  : ∀{a}   {t : Tm Γ (force a)}          → SN 0       {▸̂ a} (▹ t)
    ▹_   : ∀{a n} {t : Tm Γ (force a)} → SN n t → SN (suc n) {▸̂ a} (▹ t)
    exp  : ∀{a n t t'} → t ⟨ n ⟩⇒ t'  → SN n t' → SN n {a} t

  -- Strong head reduction

  data _⟨_⟩⇒_ {Γ} : ∀ {a} → Tm Γ a → ℕ → Tm Γ a → Set where
    β     : ∀{n a b t u} → SN n (a ∶ u)  →   (b ∶ app (abs t) u)     ⟨ n ⟩⇒ subst0 u t
    β▹    : ∀{n a b t}{u : Tm _ (force a)} → ((▸̂ b) ∶ (t <$> (▹ u))) ⟨ n ⟩⇒ ▹ (app t u)
    βfst  : ∀{n a b t u} → SN n u       → fst (pair (a ∶ t) (b ∶ u)) ⟨ n ⟩⇒ t
    βsnd  : ∀{n a b t u} → SN n t       → snd (pair (a ∶ t) (b ∶ u)) ⟨ n ⟩⇒ u
    cong  : ∀{n a b}{E} → Ehole {Γ} {a} {b} E →
            ∀{t t'} → t ⟨ n ⟩⇒ t' →                              E t ⟨ n ⟩⇒ E t'

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
  map⇒ m≤n (cong Eh t→t') = cong Eh (map⇒ m≤n t→t')

  mapSNh : ∀ {m n} → m ≤ℕ n → ∀ {Γ a b}{E : TmCxt Γ a b} → SNhole n E -> SNhole m E
  mapSNh m≤n (appl u∈SN) = appl (mapSN m≤n u∈SN)
  mapSNh m≤n fst = fst
  mapSNh m≤n snd = snd
  mapSNh m≤n (u∈SN ∗l) = mapSN m≤n u∈SN ∗l
  mapSNh m≤n (∗r t∈SN) = ∗r mapSN m≤n t∈SN


-- Evaluation contexts are closed under substitution.

mutual
  substEh' : ∀ {i vt Γ Δ a b} → (σ : RenSub {i} vt Γ Δ) → ∀ {E : TmCxt Γ a b} → Ehole E → TmCxt Δ a b
  substEh' σ (appl u) t = _
  substEh' σ fst t      = _
  substEh' σ snd t      = _
  substEh' σ (u ∗l) t   = _
  substEh' σ (∗r t) u   = _

  substEh : ∀ {i vt Γ Δ a b} → (σ : RenSub {i} vt Γ Δ) → ∀ {E : TmCxt Γ a b} → (Eh : Ehole E) → Ehole (substEh' σ Eh)
  substEh σ (appl u) = appl (subst σ u)
  substEh σ fst      = fst
  substEh σ snd      = snd
  substEh σ (u ∗l)   = subst σ u ∗l
  substEh σ (∗r t)   = ∗r subst σ t

  substEh'-subst : ∀ {i vt Γ Δ a b} → (σ : RenSub {i} vt Γ Δ) → ∀ {E : TmCxt Γ a b} → (Eh : Ehole E) → (t : Tm Γ a)
                    → substEh' σ Eh (subst σ t) ≡ subst σ (E t)
  substEh'-subst σ (appl u) t = ≡.refl
  substEh'-subst σ fst      t = ≡.refl
  substEh'-subst σ snd      t = ≡.refl
  substEh'-subst σ (u ∗l)   t = ≡.refl
  substEh'-subst σ (∗r t')  t = ≡.refl


-- Substituting strongly neutral terms

record RenSubSNe {i} (vt : VarTm i) (n : ℕ) (Γ Δ : Cxt) : Set where
  constructor _,_
  field theSubst : RenSub vt Γ Δ
        isSNe    : ∀ {a} (x : Var Γ a) → SNe n (vt2tm _ (theSubst x))
open RenSubSNe

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
  substSNh' : ∀ {i vt Γ Δ a b n} → (σ : RenSubSNe {i} vt n Γ Δ) → ∀ {E : TmCxt Γ a b} → SNhole n E → TmCxt Δ a b
  substSNh' σ (appl u) t = _
  substSNh' σ fst t      = _
  substSNh' σ snd t      = _
  substSNh' σ (u ∗l) t   = _
  substSNh' σ (∗r t) u   = _

  substSNh : ∀ {i vt Γ Δ a b n} → (σ : RenSubSNe {i} vt n Γ Δ) → ∀ {E : TmCxt Γ a b} → (SNh : SNhole n E) → SNhole n (substSNh' σ SNh)
  substSNh σ (appl u) = appl (substSN σ u)
  substSNh σ fst      = fst
  substSNh σ snd      = snd
  substSNh σ (u ∗l)   = substSN σ u ∗l
  substSNh σ (∗r t)   = ∗r substSN σ t

  substSNh'-subst : ∀ {i vt Γ Δ a b n} → (σ : RenSubSNe {i} vt n Γ Δ) → ∀ {E : TmCxt Γ a b} → (SNh : SNhole n E) → (t : Tm Γ a)
                    → substSNh' σ SNh (subst (theSubst σ) t) ≡ subst (theSubst σ) (E t)
  substSNh'-subst σ (appl u) t = ≡.refl
  substSNh'-subst σ fst      t = ≡.refl
  substSNh'-subst σ snd      t = ≡.refl
  substSNh'-subst σ (u ∗l)   t = ≡.refl
  substSNh'-subst σ (∗r t)   u = ≡.refl

  subst⇒ : ∀ {i vt Γ Δ a n} (σ : RenSubSNe {i} vt n Γ Δ) {t t' : Tm Γ a} → t ⟨ n ⟩⇒ t' → subst (theSubst σ) t ⟨ n ⟩⇒ subst (theSubst σ) t'
  subst⇒ {n = n} (σ , σ∈Ne) (β {t = t} {u = u} x) = ≡.subst (λ t' → app (abs (subst (lifts σ) t)) (subst σ u) ⟨ n ⟩⇒ t')
                                                   TODO
                                                   (β {t = subst (lifts σ) t} (substSN (σ , σ∈Ne) x))
  subst⇒         σ (β▹ {a = a})          = β▹ {a = a}
  subst⇒         σ (βfst t∈SN)           = βfst (substSN σ t∈SN)
  subst⇒         σ (βsnd u∈SN)           = βsnd (substSN σ u∈SN)
  subst⇒ {n = n} σ (cong E∈Eh t→t')      = ≡.subst₂ (λ t t' → t ⟨ n ⟩⇒ t') 
                                             (substEh'-subst (theSubst σ) E∈Eh _)
                                             (substEh'-subst (theSubst σ) E∈Eh _)
                                             (cong (substEh (theSubst σ) E∈Eh) (subst⇒ σ t→t'))

  -- Lifting a SNe substitution.

  liftsSNe : ∀ {i vt Γ Δ a n} → RenSubSNe {i} vt n Γ Δ → RenSubSNe {i} vt n (a ∷ Γ) (a ∷ Δ)
  theSubst (liftsSNe σ)                   = lifts (theSubst σ)
  isSNe    (liftsSNe {vt = `Var} (σ , σ∈SNe)) zero    = var zero
  isSNe    (liftsSNe {vt = `Var} (σ , σ∈SNe)) (suc y) = var (suc (σ y))
  isSNe    (liftsSNe {vt = `Tm } (σ , σ∈SNe)) zero    = var zero
  isSNe    (liftsSNe {vt = `Tm } (σ , σ∈SNe)) (suc y) = substSNe {vt = `Var} (suc , (λ x → var (suc x))) (σ∈SNe y)

  substSNe : ∀ {i vt Γ Δ τ n} → (σ : RenSubSNe {i} vt n Γ Δ) → ∀ {t : Tm Γ τ} → SNe n t → SNe n (subst (theSubst σ) t)
  substSNe σ (var x)            = isSNe σ x
  substSNe σ (elim t∈SNe E∈SNh) = ≡.subst (SNe _) (substSNh'-subst σ E∈SNh _) (elim (substSNe σ t∈SNe) (substSNh σ E∈SNh))

  substSN : ∀ {i vt Γ Δ τ n} → (σ : RenSubSNe {i} vt n Γ Δ) → ∀ {t : Tm Γ τ} → SN n t → SN n (subst (theSubst σ) t)
  substSN σ (ne t∈SNe)         = ne (substSNe σ t∈SNe)
  substSN σ (abs t∈SN)         = abs (substSN (liftsSNe σ) t∈SN)
  substSN σ (pair t₁∈SN t₂∈SN) = pair (substSN σ t₁∈SN) (substSN σ t₂∈SN)
  substSN σ ▹0_                = ▹0_
  substSN σ (▹ t∈SN)           = ▹ substSN (mapSubSNe n≤sn σ) t∈SN
  substSN σ (exp t→t' t'∈SN)   = exp (subst⇒ σ t→t') (substSN σ t'∈SN)

-- Variables are SN.

varSN : ∀{Γ a n x} → var x ∈ SN {Γ} n {a}
varSN = ne (var _)

-- SN is closed under application to variables.

appVarSN : ∀{Γ a b n}{t : Tm Γ (a →̂ b)}{x} → t ∈ SN n → app t (var x) ∈ SN n
appVarSN (ne t∈SNe)       = ne (elim t∈SNe (appl varSN))
appVarSN (abs t∈SN)       = exp (β varSN) (substSN (sgs-varSNe _) t∈SN)
appVarSN (exp t→t' t'∈SN) = exp (cong (appl (var _)) t→t') (appVarSN t'∈SN)
