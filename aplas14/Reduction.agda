{-# OPTIONS --copatterns --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
--{-# OPTIONS --show-implicit #-}

module Reduction where

open import Data.Sum
open import Library
open import InfiniteTypes
open import Terms
open import Substitution
open import TermShape
open import SN

data βECxt (Γ : Cxt) : (Δ : Cxt) (a b : Ty) → Set where
  appl  : ∀ {a b} (u : Tm Γ a)                        → βECxt Γ Γ (a →̂ b) b
  appr  : ∀ {a b} (t : Tm Γ (a →̂  b))                 → βECxt Γ Γ a b
  pairl : ∀ {a b} (u : Tm Γ b)                        → βECxt Γ Γ a (a ×̂ b)
  pairr : ∀ {a b} (t : Tm Γ a)                        → βECxt Γ Γ b (a ×̂ b)
  fst   : ∀ {a b}                                     → βECxt Γ Γ (a ×̂ b) a
  snd   : ∀ {a b}                                     → βECxt Γ Γ (a ×̂ b) b
  ∗l_   : ∀ {a∞ b∞} (u : Tm Γ (▸̂  a∞))                   → βECxt Γ Γ (▸̂ (a∞ ⇒ b∞)) (▸̂ b∞)
  ∗r_   : ∀ {a∞}{b∞} (t : Tm Γ (▸̂ (a∞ ⇒ b∞))) → βECxt Γ Γ (▸̂  a∞) (▸̂ b∞)
  abs   : ∀ {a b}                                     → βECxt Γ (a ∷ Γ) b (a →̂  b)
  next    : ∀ {a∞}                                      → βECxt Γ Γ (force a∞) (▸̂  a∞)

data βEHole {Γ : Cxt} : {Δ : Cxt} {b a : Ty} → Tm Γ b → βECxt Γ Δ a b → Tm Δ a → Set where
  appl  : ∀ {a b t} (u : Tm Γ a)                          → βEHole (app t u) (appl u) (t ∶ (a →̂ b))
  appr  : ∀ {a b u} (t : Tm Γ (a →̂  b))                   → βEHole (app t u) (appr t) u
  pairl : ∀ {a b}{t} (u : Tm Γ b)                         → βEHole (pair t u) (pairl u) (t ∶ a)
  pairr : ∀ {a b}{u} (t : Tm Γ a)                         → βEHole (pair t u) (pairr t) (u ∶ b)
  fst   : ∀ {a b t}                                       → βEHole {a = a ×̂ b} (fst t) fst t
  snd   : ∀ {a b t}                                       → βEHole {a = a ×̂ b} (snd t) snd t
  ∗l_   : ∀ {a∞ b∞ t} (u : Tm Γ (▸̂  a∞))                   → βEHole {a = (▸̂ (a∞ ⇒ b∞))} (t ∗ u) (∗l u) t
  ∗r_   : ∀ {a∞}{b∞}{u} (t : Tm Γ (▸̂ (a∞ ⇒ b∞))) → βEHole ((t ∗ (u ∶ ▸̂  a∞)) ∶ ▸̂ b∞) (∗r t) u
  abs   : ∀ {a b} {t : Tm (a ∷ Γ) b}                      → βEHole (abs t) abs t
  next    : ∀ {a∞} {t : Tm Γ (force a∞)}                    → βEHole (next {a∞ = a∞} t) next t


mkHole : ∀ {Γ Δ} {a b} (E : βECxt Γ Δ a b) {t} → Σ _ \ E[t] → βEHole E[t] E t
mkHole (appl u)  = _ , appl u
mkHole (appr t)  = _ , appr t
mkHole (pairl u) = _ , pairl u
mkHole (pairr t) = _ , pairr t
mkHole fst       = _ , fst
mkHole snd       = _ , snd
mkHole (∗l u)    = _ , ∗l u
mkHole (∗r t)    = _ , ∗r t
mkHole abs       = _ , abs
mkHole next        = _ , next

infix 2 _⇒β_
data _⇒β_ {Γ} : ∀ {a} → Tm Γ a → Tm Γ a → Set where

  β     : ∀ {a b}{t : Tm (a ∷ Γ) b}{u}
          → (app (abs t) u) ⇒β subst0 u t

  β▸    : ∀ {a∞ b∞}{t : Tm Γ (force a∞ →̂  force b∞)}{u : Tm Γ (force a∞)}
           → (next t ∗ next {a∞ = a∞} u) ⇒β (next {a∞ = b∞} (app t u))

  βfst  : ∀ {a b}{t : Tm Γ a}{u : Tm Γ b}
          → fst (pair t u) ⇒β t

  βsnd  : ∀ {a b}{t : Tm Γ a}{u : Tm Γ b}
          → snd (pair t u) ⇒β u

  cong  : ∀ {Δ a b t t' Et Et'}{E : βECxt Γ Δ a b}
          → (𝑬𝒕 : βEHole Et E t)
          → (𝑬𝒕' : βEHole Et' E t')
          → (t⇒β : t ⇒β t')
          → Et ⇒β Et'


subst⇒β : ∀ {m vt a Γ} {t t' : Tm Γ a} {Δ}
           (σ : RenSub {m} vt Γ Δ) → t ⇒β t' → subst σ t ⇒β subst σ t'
subst⇒β σ (β {t = t} {u = u})            = ≡.subst (λ t' → app (abs (subst (lifts σ) t)) (subst σ u) ⇒β t')
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

infix 1 _⇒β*_
data _⇒β*_ {Γ} {a} : Tm Γ a → Tm Γ a → Set where
  []  : ∀ {t} → t ⇒β* t
  _∷_ : ∀ {ti tm to} → ti ⇒β tm → tm ⇒β* to → ti ⇒β* to

_++β_ : ∀ {Γ} {a} {t₀ t₁ t₂ : Tm Γ a} → t₀ ⇒β* t₁ → t₁ ⇒β* t₂ → t₀ ⇒β* t₂
[] ++β ys = ys
(x ∷ xs) ++β ys = x ∷ (xs ++β ys)

cong* : ∀ {a Γ Δ} {b} {t tβ* : Tm Γ a} {E : βECxt Δ Γ a b}{E[t] E[tβ*]} → βEHole E[t] E t → βEHole E[tβ*] E tβ* → t ⇒β* tβ* → E[t] ⇒β* E[tβ*]
cong* (appl u)   (appl .u)   []       = []
cong* (appr t₁)  (appr .t₁)  []       = []
cong* (pairl u)  (pairl .u)  []       = []
cong* (pairr t₁) (pairr .t₁) []       = []
cong* fst        fst         []       = []
cong* snd        snd         []       = []
cong* (∗l u)     (∗l .u)     []       = []
cong* (∗r t₁)    (∗r .t₁)    []       = []
cong* abs        abs         []       = []
cong* next         next          []       = []
cong* E1         E2          (x ∷ t⇒) = cong E1 (proj₂ (mkHole _)) x ∷ cong* (proj₂ (mkHole _)) E2 t⇒

mutual
  EC→βEC : ∀ {Γ} {a b} (E : ECxt Γ a b) → βECxt Γ Γ a b
  EC→βEC (appl u) = appl u
  EC→βEC fst = fst
  EC→βEC snd = snd
  EC→βEC (∗l u) = ∗l u
  EC→βEC (∗r t) = ∗r (next t)

  mkHole4 : ∀ {Γ} {a b} (E : ECxt Γ a b) {t : Tm Γ a} → βEHole (E [ t ]) (EC→βEC E) t
  mkHole4 (appl u) = appl u
  mkHole4 fst = fst
  mkHole4 snd = snd
  mkHole4 (∗l u) = ∗l u
  mkHole4 (∗r t) = ∗r (next t)

cong*3 : ∀ {Γ a b t t'}(E : ECxt* Γ a b)
          → (t⇒ : t ⇒β t')
          → E [ t ]* ⇒β E [ t' ]*
cong*3 [] t⇒ = t⇒
cong*3 (x ∷ E) t⇒ = cong*3 E (cong (mkHole4 x) (mkHole4 x) t⇒)

cong*4 : ∀ {Γ a b t t'}(E : ECxt* Γ a b)
          → (t⇒ : t ⇒β* t')
          → E [ t ]* ⇒β* E [ t' ]*
cong*4 E [] = []
cong*4 E (x ∷ xs) = cong*3 E x ∷ cong*4 E xs

subst⇒β*₀ : ∀ {m vt a Γ} {t t' : Tm Γ a} {Δ} (σ : RenSub {m} vt Γ Δ) → t ⇒β* t' → subst σ t ⇒β* subst σ t'
subst⇒β*₀ σ [] = []
subst⇒β*₀ σ (x ∷ xs) = (subst⇒β σ x) ∷ (subst⇒β*₀ σ xs)

-- map⇒β : ∀ {m n} → .(m ≤ℕ n) → ∀ {Γ a}{t t' : Tm Γ a} → t ⟨ n ⟩⇒ t' → t ⟨ m ⟩⇒ t'
-- map⇒β m≤n (β t∈SN) = β (mapSN m≤n t∈SN)
-- map⇒β m≤n (β▸ {a = a}) = β▸ {a = a}
-- map⇒β m≤n (βfst t∈SN) = βfst (mapSN m≤n t∈SN)
-- map⇒β m≤n (βsnd t∈SN) = βsnd (mapSN m≤n t∈SN)
-- map⇒β m≤n (cong Et Et' t→t') = cong Et Et' (map⇒ m≤n t→t')

mutual
  subst⇒β* : ∀ {m vt a Γ} {Δ} {σ ρ : RenSub {m} vt Γ Δ} → (∀ {b} (x : Var Γ b) → vt2tm _ (σ x) ⇒β* vt2tm _ (ρ x))
             → (t : Tm Γ a) → subst σ t ⇒β* subst ρ t
  subst⇒β* σ₁ (var x) = σ₁ x
  subst⇒β* {vt = vt} σ₁ (abs t) = cong* abs abs (subst⇒β* (lifts⇒β* {vt = vt} σ₁) t)
  subst⇒β* σ₁ (app t t₁) = cong* (appl _) (appl _) (subst⇒β* σ₁ t) ++β cong* (appr _) (appr _) (subst⇒β* σ₁ t₁)
  subst⇒β* σ₁ (pair t t₁) = cong* (pairl _) (pairl _) (subst⇒β* σ₁ t) ++β
                              cong* (pairr _) (pairr _) (subst⇒β* σ₁ t₁)
  subst⇒β* σ₁ (fst t) = cong* fst fst (subst⇒β* σ₁ t)
  subst⇒β* σ₁ (snd t) = cong* snd snd (subst⇒β* σ₁ t)
  subst⇒β* σ₁ (next t) = cong* next next (subst⇒β* σ₁ t)
  subst⇒β* σ₁ (t ∗ t₁) =  cong* (∗l _) (∗l _) (subst⇒β* σ₁ t) ++β
                           cong* (∗r _) (∗r _) (subst⇒β* σ₁ t₁)

  lifts⇒β* : ∀ {m vt a Γ} {Δ} {σ ρ : RenSub {m} vt Γ Δ} → (∀ {b} (x : Var Γ b) → vt2tm _ (σ x) ⇒β* vt2tm _ (ρ x))
             →  (∀ {b} (x : Var (a ∷ Γ) b) → vt2tm _ (lifts {a = a} σ x) ⇒β* vt2tm _ (lifts {a = a} ρ x))
  lifts⇒β* {vt = `Var} σ₁ (zero) = []
  lifts⇒β* {vt = `Tm}  σ₁ (zero) = []
  lifts⇒β* {vt = `Var} σ₁ (suc x)   = subst⇒β*₀ {vt = `Var} suc (σ₁ x)
  lifts⇒β* {vt = `Tm}  σ₁ (suc x)   = subst⇒β*₀ {vt = `Var} suc (σ₁ x)

mutual
  beta-shr : ∀ {i n a Γ} {t tβ th : Tm Γ a} → t ⇒β tβ → i size t ⟨ n ⟩⇒ th → (tβ ≡ th) ⊎ Σ _ \ t' → (i size tβ ⟨ n ⟩⇒ t') × (th ⇒β* t')
  beta-shr β (β 𝒖)                                                   = inj₁ ≡.refl
  beta-shr (cong (appl u) (appl .u) (cong abs abs tβ⇒)) (β 𝒖)        = inj₂ (_ , β 𝒖 , (subst⇒β (sgs u) tβ⇒ ∷ []))
  beta-shr (cong (appr ._) (appr ._) tβ⇒) (β {t = t} 𝒖)
    = inj₂ (_ , β (mapβSN tβ⇒ 𝒖) , subst⇒β* {vt = `Tm} (λ { {._} (zero) → tβ⇒ ∷ [] ; (suc x) → [] }) t)
  beta-shr β▸ β▸                                                     = inj₁ ≡.refl
  beta-shr (cong (∗l ._) (∗l ._) (cong next next tβ⇒)) β▸                = inj₂ (_ , β▸ , cong next next (cong (appl _) (appl _) tβ⇒) ∷ [])
  beta-shr (cong (∗r ._) (∗r ._) (cong next next tβ⇒)) β▸                = inj₂ (_ , β▸ , cong next next (cong (appr _) (appr _) tβ⇒) ∷ [])
  beta-shr βfst (βfst 𝒖)                                             = inj₁ ≡.refl
  beta-shr (cong fst fst (cong (pairl u) (pairl .u) tβ⇒)) (βfst 𝒖)   = inj₂ (_ , ((βfst 𝒖) , (tβ⇒ ∷ [])))
  beta-shr (cong fst fst (cong (pairr th) (pairr .th) tβ⇒)) (βfst 𝒖) = inj₂ (_ , βfst (mapβSN tβ⇒ 𝒖) , [])
  beta-shr (cong snd snd (cong (pairl u) (pairl .u) tβ⇒)) (βsnd 𝒖)   = inj₂ (_ , βsnd (mapβSN tβ⇒ 𝒖) , [])
  beta-shr (cong snd snd (cong (pairr th) (pairr .th) tβ⇒)) (βsnd 𝒖) = inj₂ (_ , ((βsnd 𝒖) , (tβ⇒ ∷ [])))
  beta-shr βsnd (βsnd 𝒖)                                             = inj₁ ≡.refl
  beta-shr β (cong (appl u) (appl .u) (cong () 𝑬𝒕' th⇒))
  beta-shr β▸ (cong (∗l ._) (∗l ._) (cong () 𝑬𝒕' th⇒))
  beta-shr β▸ (cong (∗r t) (∗r .t) (cong () 𝑬𝒕' th⇒))
  beta-shr βfst (cong fst fst (cong () 𝑬𝒕' th⇒))
  beta-shr βsnd (cong snd snd (cong () 𝑬𝒕' th⇒))
  beta-shr (cong E1 E2 t⇒) (cong E0 E3 th⇒)                          = helper E1 E2 t⇒ E0 E3 th⇒

    where
         -- helper : ∀ {i}{j : Size< i}{n a Γ} {t tβ th : Tm Γ a} {Δ a₁} {t₁ ta : Tm Δ a₁}
         --   {E : βECxt Γ Δ a₁ a} {a₂} {t₂ tb : Tm Γ a₂} {E₁ : ECxt Γ a₂ a} →
         -- βEHole t E t₁ →
         -- βEHole tβ E ta →
         -- t₁ ⇒β ta →
         -- EHole t E₁ t₂ →
         -- EHole th E₁ tb →
         -- j size t₂ ⟨ n ⟩⇒ tb →
         -- tβ ≡ th ⊎
         -- Σ (Tm Γ a) (λ tm → Σ (i size tβ ⟨ n ⟩⇒ tm) (λ x → th ⇒β* tm))
      helper : ∀ {i}{n a Γ} {t tβ th : Tm Γ a} {Δ a₁} {t₁ ta : Tm Δ a₁}
           {E : βECxt Γ Δ a₁ a} {a₂} {t₂ tb : Tm Γ a₂} {E₁ : ECxt Γ a₂ a} →
         βEHole t E t₁ →
         βEHole tβ E ta →
         t₁ ⇒β ta →
         EHole t E₁ t₂ →
         EHole th E₁ tb →
         i size t₂ ⟨ n ⟩⇒ tb →
         tβ ≡ th ⊎
         Σ (Tm Γ a) (λ tm → Σ (i size tβ ⟨ n ⟩⇒ tm) (λ x → th ⇒β* tm))
      helper (appl u) (appl .u) t⇒₁ (appl .u) (appl .u) th⇒₁ with beta-shr t⇒₁ th⇒₁
      helper (appl u) (appl .u) t⇒₁ (appl .u) (appl .u) th⇒₁ | inj₁ ≡.refl = inj₁ ≡.refl
      helper (appl u) (appl .u) t⇒₁ (appl .u) (appl .u) th⇒₁ | inj₂ (tm , h⇒tm , tm⇒β)
             = inj₂ (_ , cong (appl _) (appl _) h⇒tm , cong* (appl _) (appl _) tm⇒β)
      helper (appr t₂) (appr .t₂) t⇒₁ (appl t₁) (appl .t₁) th⇒₁ = inj₂ (_ , cong (appl _) (appl _) th⇒₁ , (cong (appr _) (appr _) t⇒₁ ∷ []))
      helper fst fst t⇒₁ fst fst th⇒₁ with beta-shr t⇒₁ th⇒₁
      helper fst fst t⇒₁ fst fst th⇒₁ | inj₁ x = inj₁ (≡.cong fst x)
      helper fst fst t⇒₁ fst fst th⇒₁ | inj₂ (tm , h⇒tm , tm⇒β) = inj₂ (_ , ((cong fst fst h⇒tm) , cong* fst fst tm⇒β))
      helper snd snd t⇒₁ snd snd th⇒₁ with beta-shr t⇒₁ th⇒₁
      helper snd snd t⇒₁ snd snd th⇒₁ | inj₁ x = inj₁ (≡.cong snd x)
      helper snd snd t⇒₁ snd snd th⇒₁ | inj₂ (tm , h⇒tm , tm⇒β) = inj₂ (_ , ((cong snd snd h⇒tm) , cong* snd snd tm⇒β))
      helper (∗l u) (∗l .u) t⇒₁ (∗l .u) (∗l .u) th⇒₁ with beta-shr t⇒₁ th⇒₁
      helper (∗l u) (∗l .u) t⇒₁ (∗l .u) (∗l .u) th⇒₁ | inj₁ ≡.refl = inj₁ ≡.refl
      helper (∗l u) (∗l .u) t⇒₁ (∗l .u) (∗l .u) th⇒₁ | inj₂ (tm , h⇒tm , tm⇒β) = inj₂ (_ , ((cong (∗l _) (∗l _) h⇒tm) , (cong* (∗l _) (∗l _) tm⇒β)))
      helper (∗r t₂) (∗r .t₂) t⇒₁ (∗l t₁) (∗l .t₁) th⇒₁ = inj₂ (_ , ((cong (∗l _) (∗l _) th⇒₁) , (cong (∗r _) (∗r _) t⇒₁ ∷ [])))
      helper (∗l t₂) (∗l .t₂) (cong next next t⇒₁) (∗r t) (∗r .t) th⇒₁
            = inj₂ (_ , ((cong (∗r _) (∗r _) th⇒₁) , (cong (∗l _) (∗l _) (cong next next t⇒₁) ∷ [])))
      helper (∗r .(next t)) (∗r .(next t)) t⇒₁ (∗r t) (∗r .t) th⇒₁ with beta-shr t⇒₁ th⇒₁
      ... | inj₁ ≡.refl = inj₁ ≡.refl
      ... | inj₂ (tm , h⇒tm , tm⇒β) = inj₂ (_ , ((cong (∗r _) (∗r _) h⇒tm) , cong* (∗r _) (∗r _) tm⇒β))

  mapβSNe : ∀ {i n a Γ} {t t' : Tm Γ a} → t ⇒β t' → SNe {i} n t → SNe {i} n t'
  mapβSNe β                                     (elim (elim 𝒏 ()) (appl 𝒖))
  mapβSNe β▸                                    (elim (elim 𝒏 ()) (∗l 𝒖))
  mapβSNe β▸                                    (elim (elim 𝒏 ()) (∗r 𝒕))
  mapβSNe βfst                                  (elim (elim 𝒏 ()) fst)
  mapβSNe βsnd                                  (elim (elim 𝒏 ()) snd)
  mapβSNe (cong (appl u) (appl .u) t⇒)          (elim 𝒏 (appl 𝒖))   = elim (mapβSNe t⇒ 𝒏) (appl 𝒖)
  mapβSNe (cong (appr t₁) (appr .t₁) t⇒)        (elim 𝒏 (appl 𝒖))   = elim 𝒏 (appl (mapβSN t⇒ 𝒖))
  mapβSNe (cong fst fst t⇒)                     (elim  𝒏 fst)        = elim  (mapβSNe t⇒ 𝒏) fst
  mapβSNe (cong snd snd t⇒)                     (elim  𝒏 snd)        = elim  (mapβSNe t⇒ 𝒏) snd
  mapβSNe (cong (∗l u) (∗l .u) t⇒)              (elim  𝒏 (∗l 𝒖))     = elim  (mapβSNe t⇒ 𝒏) (∗l 𝒖)
  mapβSNe (cong (∗l u) (∗l .u) (cong next next t⇒)) (elim 𝒏 (∗r ne (elim _ ())))
  mapβSNe (cong (∗l u) (∗l .u) (cong next next t⇒)) (elim  𝒏 (∗r next0))    = elim  𝒏 (∗r_ next0)
  mapβSNe (cong (∗l u) (∗l .u) (cong next next t⇒)) (elim  𝒏 (∗r (next 𝒕))) = elim  𝒏 (∗r (next (mapβSN t⇒ 𝒕)))
  mapβSNe (cong (∗l u) (∗l .u) (cong next next t⇒)) (elim 𝒏 (∗r exp (cong () 𝑬𝒕' t⇒₁) 𝒕))
  mapβSNe (cong (∗r t₁) (∗r .t₁) t⇒)            (elim  𝒏 (∗l 𝒖))     = elim  𝒏 (∗l (mapβSN t⇒ 𝒖))
  mapβSNe (cong (∗r ._) (∗r ._) t⇒)             (elim  𝒏 (∗r 𝒕))     = elim  (mapβSNe t⇒ 𝒏) (∗r 𝒕)
  mapβSNe (cong abs abs t⇒)                     (elim 𝒏 ())
  mapβSNe (cong next next t⇒)                       (elim 𝒏 ())
  mapβSNe (cong (pairr _) (pairr ._) t⇒)        (elim 𝒏 ())
  mapβSNe (cong (pairl _) (pairl ._) t⇒)        (elim 𝒏 ())

  mapβSN : ∀ {i n a Γ} {t t' : Tm Γ a} → t ⇒β t' → SN {i} n t → SN {i} n t'
  mapβSN t⇒                (ne 𝒏)                      = ne (mapβSNe t⇒ 𝒏)
  mapβSN (cong abs abs t⇒) (abs 𝒕)                     = abs (mapβSN t⇒ 𝒕)
  mapβSN (cong (pairl u)   (pairl .u) t⇒) (pair 𝒕 𝒕₁)  = pair (mapβSN t⇒ 𝒕) 𝒕₁
  mapβSN (cong (pairr t₁)  (pairr .t₁) t⇒) (pair 𝒕 𝒕₁) = pair 𝒕 (mapβSN t⇒ 𝒕₁)
  mapβSN (cong next next t⇒)   next0                          = next0
  mapβSN (cong next next t⇒)   (next 𝒕)                       = next (mapβSN t⇒ 𝒕)
  mapβSN t⇒                (exp t⇒₁ 𝒕)                 with beta-shr t⇒ t⇒₁
  mapβSN t⇒ (exp t⇒₁ 𝒕) | inj₁ ≡.refl = 𝒕
  mapβSN t⇒ (exp t⇒₁ 𝒕) | inj₂ (_ , t⇒h , t⇒β*) = exp t⇒h (mapβ*SN t⇒β* 𝒕)

  mapβ*SN : ∀ {i n a Γ} {t t' : Tm Γ a} → t ⇒β* t' → SN {i} n t → SN {i} n t'
  mapβ*SN []          𝒕 = 𝒕
  mapβ*SN (t⇒ ∷ t⇒β*) 𝒕 = mapβ*SN t⇒β* (mapβSN t⇒ 𝒕)
