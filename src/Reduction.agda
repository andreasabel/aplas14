{-# OPTIONS --copatterns --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
--{-# OPTIONS --show-implicit #-}
{-# OPTIONS --no-termination-check #-} -- too slow

module Reduction where

open import Data.Sum
open import Library
open import SizedInfiniteTypes
open import Terms
open import Substitution
open import SN

data βECxt (Γ : Cxt) : (Δ : Cxt) (a b : Ty) → Set where
  appl  : ∀ {a b} (u : Tm Γ a)                        → βECxt Γ Γ (a →̂ b) b
  appr  : ∀ {a b} (t : Tm Γ (a →̂  b))                 → βECxt Γ Γ a b
  pairl : ∀ {a b} (u : Tm Γ b)                        → βECxt Γ Γ a (a ×̂ b)
  pairr : ∀ {a b} (t : Tm Γ a)                        → βECxt Γ Γ b (a ×̂ b)
  fst   : ∀ {a b}                                     → βECxt Γ Γ (a ×̂ b) a
  snd   : ∀ {a b}                                     → βECxt Γ Γ (a ×̂ b) b
  _∗l   : ∀ {a b∞} (u : Tm Γ (▸ a))                   → βECxt Γ Γ (▸̂ (delay a ⇒ b∞)) (▸̂ b∞)
  ∗r_   : ∀{a : Ty}{b∞} (t : Tm Γ (▸̂ (delay a ⇒ b∞))) → βECxt Γ Γ (▸ a) (▸̂ b∞)
  abs   : ∀ {a b}                                     → βECxt Γ (a ∷ Γ) b (a →̂  b)
  ▹_    : ∀ {a∞}                                      → βECxt Γ Γ (force a∞) (▸̂  a∞)

data βEhole {Γ : Cxt} : {Δ : Cxt} {b a : Ty} → Tm Γ b → βECxt Γ Δ a b → Tm Δ a → Set where
  appl  : ∀ {a b t} (u : Tm Γ a)                          → βEhole (app t u) (appl u) (t ∶ (a →̂ b))
  appr  : ∀ {a b u} (t : Tm Γ (a →̂  b))                   → βEhole (app t u) (appr t) u
  pairl : ∀ {a b}{t} (u : Tm Γ b)                         → βEhole (pair t u) (pairl u) (t ∶ a)
  pairr : ∀ {a b}{u} (t : Tm Γ a)                         → βEhole (pair t u) (pairr t) (u ∶ b)
  fst   : ∀ {a b t}                                       → βEhole {a = a ×̂ b} (fst t) fst t
  snd   : ∀ {a b t}                                       → βEhole {a = a ×̂ b} (snd t) snd t
  _∗l   : ∀ {a b∞ t} (u : Tm Γ (▸ a))                     → βEhole {a = (▸̂ (delay a ⇒ b∞))} (t ∗ u) (u ∗l) t
  ∗r_   : ∀ {a : Ty}{b∞}{u} (t : Tm Γ (▸̂ (delay a ⇒ b∞))) → βEhole ((t ∗ (u ∶ ▸ a)) ∶ ▸̂ b∞) (∗r t) u
  abs   : ∀ {a b} {t : Tm (a ∷ Γ) b}                      → βEhole (abs t) abs t
  ▹_    : ∀ {a∞} {t : Tm Γ (force a∞)}                    → βEhole (▹_ {a∞ = a∞} t) ▹_ t 


mkHole : ∀ {Γ Δ} {a b} (E : βECxt Γ Δ a b) {t} → Σ _ \ E[t] → βEhole E[t] E t
mkHole (appl u) = _ , appl u
mkHole (appr t) = _ , appr t
mkHole (pairl u) = _ , pairl u
mkHole (pairr t) = _ , pairr t
mkHole fst = _ , fst
mkHole snd = _ , snd
mkHole (u ∗l) = _ , u ∗l
mkHole (∗r t) = _ , ∗r t
mkHole abs = _ , abs
mkHole ▹_ = _ , ▹_
 
data _⇒β_ {Γ} : ∀ {a} → Tm Γ a → Tm Γ a → Set where

  β     : ∀ {a b}{t : Tm (a ∷ Γ) b}{u}
          → (app (abs t) u) ⇒β subst0 u t

  β▹    : ∀ {a b∞}{t : Tm Γ (a →̂  force b∞)}{u : Tm Γ a}
           → (▹ t ∗ ▹ u) ⇒β (▹_ {a∞ = b∞} (app t u))

  βfst  : ∀ {a b}{t : Tm Γ a}{u : Tm Γ b}
          → fst (pair t u) ⇒β t

  βsnd  : ∀ {a b}{t : Tm Γ a}{u : Tm Γ b}
          → snd (pair t u) ⇒β u

  cong  : ∀ {Δ a b t t' Et Et'}{E : βECxt Γ Δ a b}
          → (𝑬𝒕 : βEhole Et E t)
          → (𝑬𝒕' : βEhole Et' E t')
          → (t⇒β : t ⇒β t')
          → Et ⇒β Et'


subst⇒β : ∀ {m vt a Γ} {t t' : Tm Γ a} {Δ}
           (σ : RenSub {m} vt Γ Δ) → t ⇒β t' → subst σ t ⇒β subst σ t'
subst⇒β σ (β {t = t} {u = u})            = ≡.subst (λ t' → app (abs (subst (lifts σ) t)) (subst σ u) ⇒β t') 
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

data _⇒β*_ {Γ} {a} : Tm Γ a → Tm Γ a → Set where
  []  : ∀ {t} → t ⇒β* t
  _∷_ : ∀ {ti tm to} → ti ⇒β tm → tm ⇒β* to → ti ⇒β* to
 
cong* : ∀ {a Γ Δ} {b} {t tβ* : Tm Γ a} {E : βECxt Δ Γ a b}{E[t] E[tβ*]} → βEhole E[t] E t → βEhole E[tβ*] E tβ* → t ⇒β* tβ* → E[t] ⇒β* E[tβ*]
cong* (appl u)   (appl .u)   []       = []
cong* (appr t₁)  (appr .t₁)  []       = []
cong* (pairl u)  (pairl .u)  []       = []
cong* (pairr t₁) (pairr .t₁) []       = []
cong* fst        fst         []       = []
cong* snd        snd         []       = []
cong* (u ∗l)     (.u ∗l)     []       = []
cong* (∗r t₁)    (∗r .t₁)    []       = []
cong* abs        abs         []       = []
cong* ▹_         ▹_          []       = []
cong* E1         E2          (x ∷ t⇒) = cong E1 (proj₂ (mkHole _)) x ∷ cong* (proj₂ (mkHole _)) E2 t⇒


mutual
  beta-shr : ∀ {n}{a} {Γ} {t tβ th : Tm Γ a} → t ⇒β tβ → t ⟨ n ⟩⇒ th → (tβ ≡ th) ⊎ Σ _ \ t' → tβ ⟨ n ⟩⇒ t' × th ⇒β* t'
  beta-shr β (β 𝒖) = inj₁ ≡.refl
  beta-shr (cong (appl u) (appl .u) (cong abs abs tβ⇒)) (β 𝒖) = inj₂ (_ , β 𝒖 , (subst⇒β (sgs u) tβ⇒ ∷ []))
  beta-shr (cong (appr ._) (appr ._) tβ⇒) (β 𝒖) = inj₂ (_ , β (mapβSN tβ⇒ 𝒖) , TODO)
  beta-shr β▹ β▹ = inj₁ ≡.refl
  beta-shr (cong (._ ∗l) (._ ∗l) (cong ▹_ ▹_ tβ⇒)) β▹ = inj₂ (_ , β▹ , cong ▹_ ▹_ (cong (appl _) (appl _) tβ⇒) ∷ [])
  beta-shr (cong (∗r ._) (∗r ._) (cong ▹_ ▹_ tβ⇒)) β▹ = inj₂ (_ , β▹ , cong ▹_ ▹_ (cong (appr _) (appr _) tβ⇒) ∷ [])
  beta-shr βfst (βfst 𝒖) = inj₁ ≡.refl
  beta-shr (cong fst fst (cong (pairl u) (pairl .u) tβ⇒)) (βfst 𝒖) = inj₂ (_ , ((βfst 𝒖) , (tβ⇒ ∷ [])))
  beta-shr (cong fst fst (cong (pairr th) (pairr .th) tβ⇒)) (βfst 𝒖) = inj₂ (_ , βfst (mapβSN tβ⇒ 𝒖) , [])
  beta-shr (cong snd snd (cong (pairl u) (pairl .u) tβ⇒)) (βsnd 𝒖) = inj₂ (_ , βsnd (mapβSN tβ⇒ 𝒖) , [])
  beta-shr (cong snd snd (cong (pairr th) (pairr .th) tβ⇒)) (βsnd 𝒖) = inj₂ (_ , ((βsnd 𝒖) , (tβ⇒ ∷ [])))
  beta-shr βsnd (βsnd 𝒖) = inj₁ ≡.refl
  beta-shr β (cong (appl u) (appl .u) (cong () 𝑬𝒕' th⇒))
  beta-shr β▹ (cong (._ ∗l) (._ ∗l) (cong () 𝑬𝒕' th⇒))
  beta-shr β▹ (cong (∗r t) (∗r .t) (cong () 𝑬𝒕' th⇒))
  beta-shr βfst (cong fst fst (cong () 𝑬𝒕' th⇒))
  beta-shr βsnd (cong snd snd (cong () 𝑬𝒕' th⇒))
  beta-shr (cong E1 E2 t⇒) (cong E0 E3 th⇒) = helper E1 E2 t⇒ E0 E3 th⇒
    where
      helper : ∀ {n a Γ} {t tβ th : Tm Γ a} {Δ a₁} {t₁ ta : Tm Δ a₁}
           {E : βECxt Γ Δ a₁ a} {a₂} {t₂ tb : Tm Γ a₂} {E₁ : ECxt Γ a₂ a} →
         βEhole t E t₁ →
         βEhole tβ E ta →
         t₁ ⇒β ta →
         Ehole t E₁ t₂ →
         Ehole th E₁ tb →
         t₂ ⟨ n ⟩⇒ tb →
         tβ ≡ th ⊎
         Σ (Tm Γ a) (λ tm → Σ (tβ ⟨ n ⟩⇒ tm) (λ x → th ⇒β* tm))
      helper (appl u) (appl .u) t⇒₁ (appl .u) (appl .u) th⇒₁ = TODO
      helper (appr t₂) (appr .t₂) t⇒₁ (appl t₁) (appl .t₁) th⇒₁ = inj₂ (_ , cong (appl _) (appl _) th⇒₁ , (cong (appr _) (appr _) t⇒₁ ∷ []))
      helper fst fst t⇒₁ fst fst th⇒₁ with beta-shr t⇒₁ th⇒₁ 
      helper fst fst t⇒₁ fst fst th⇒₁ | inj₁ x = inj₁ (≡.cong fst x)
      helper fst fst t⇒₁ fst fst th⇒₁ | inj₂ (tm , h⇒tm , tm⇒β) = inj₂ (_ , ((cong fst fst h⇒tm) , cong* fst fst tm⇒β))
      helper snd snd t⇒₁ snd snd th⇒₁ = TODO
      helper (u ∗l) (.u ∗l) t⇒₁ (.u ∗l) (.u ∗l) th⇒₁ with beta-shr t⇒₁ th⇒₁ 
      helper (u ∗l) (.u ∗l) t⇒₁ (.u ∗l) (.u ∗l) th⇒₁ | inj₁ ≡.refl = inj₁ ≡.refl
      helper (u ∗l) (.u ∗l) t⇒₁ (.u ∗l) (.u ∗l) th⇒₁ | inj₂ (tm , h⇒tm , tm⇒β) = inj₂ (_ , ((cong (_ ∗l) (_ ∗l) h⇒tm) , (cong* (_ ∗l) (_ ∗l) tm⇒β)))
      helper (∗r t₂) (∗r .t₂) t⇒₁ (t₁ ∗l) (.t₁ ∗l) th⇒₁ = TODO
      helper (t₂ ∗l) (.t₂ ∗l) t⇒₁ (∗r t) (∗r .t) th⇒₁ = TODO
      helper (∗r .(▹ t)) (∗r .(▹ t)) t⇒₁ (∗r t) (∗r .t) th⇒₁ with beta-shr t⇒₁ th⇒₁ 
      ... | inj₁ ≡.refl = inj₁ ≡.refl
      ... | inj₂ (tm , h⇒tm , tm⇒β) = inj₂ (_ , ((cong (∗r _) (∗r _) h⇒tm) , cong* (∗r _) (∗r _) tm⇒β))

  mapβSNe : ∀ {n}{a} {Γ} {t t' : Tm Γ a} → t ⇒β t' → SNe n t → SNe n t'
  mapβSNe β                                     (elim (elim 𝒏 ()) (appl 𝒖))
  mapβSNe β▹                                    (elim (elim 𝒏 ()) (𝒖 ∗l))
  mapβSNe β▹                                    (elim (elim 𝒏 ()) (∗r 𝒕))
  mapβSNe βfst                                  (elim (elim 𝒏 ()) fst)
  mapβSNe βsnd                                  (elim (elim 𝒏 ()) snd)
  mapβSNe (cong (appl u) (appl .u) t⇒)          (elim 𝒏 (appl 𝒖))   = elim (mapβSNe t⇒ 𝒏) (appl 𝒖)
  mapβSNe (cong (appr t₁) (appr .t₁) t⇒)        (elim 𝒏 (appl 𝒖))   = elim 𝒏 (appl (mapβSN t⇒ 𝒖))
  mapβSNe (cong fst fst t⇒)                     (elim 𝒏 fst)        = elim (mapβSNe t⇒ 𝒏) fst
  mapβSNe (cong snd snd t⇒)                     (elim 𝒏 snd)        = elim (mapβSNe t⇒ 𝒏) snd
  mapβSNe (cong (u ∗l) (.u ∗l) t⇒)              (elim 𝒏 (𝒖 ∗l))     = elim (mapβSNe t⇒ 𝒏) (𝒖 ∗l)
  mapβSNe (cong (u ∗l) (.u ∗l) (cong ▹_ ▹_ t⇒)) (elim 𝒏 (∗r ne (elim _ ())))
  mapβSNe (cong (u ∗l) (.u ∗l) (cong ▹_ ▹_ t⇒)) (elim 𝒏 (∗r ▹0))    = elim 𝒏 (∗r ▹0)
  mapβSNe (cong (u ∗l) (.u ∗l) (cong ▹_ ▹_ t⇒)) (elim 𝒏 (∗r (▹ 𝒕))) = elim 𝒏 (∗r (▹ mapβSN t⇒ 𝒕))
  mapβSNe (cong (u ∗l) (.u ∗l) (cong ▹_ ▹_ t⇒)) (elim 𝒏 (∗r exp (cong () 𝑬𝒕' t⇒₁) 𝒕))
  mapβSNe (cong (∗r t₁) (∗r .t₁) t⇒)            (elim 𝒏 (𝒖 ∗l))     = elim 𝒏 (mapβSN t⇒ 𝒖 ∗l)
  mapβSNe (cong (∗r ._) (∗r ._) t⇒)             (elim 𝒏 (∗r 𝒕))     = elim (mapβSNe t⇒ 𝒏) (∗r 𝒕)
  mapβSNe (cong abs abs t⇒)                     (elim 𝒏 ())
  mapβSNe (cong ▹_ ▹_ t⇒)                       (elim 𝒏 ())
  mapβSNe (cong (pairr _) (pairr ._) t⇒)        (elim 𝒏 ())
  mapβSNe (cong (pairl _) (pairl ._) t⇒)        (elim 𝒏 ())

  mapβSN : ∀ {n}{a} {Γ} {t t' : Tm Γ a} → t ⇒β t' → SN n t → SN n t'
  mapβSN t⇒                (ne 𝒏)                      = ne (mapβSNe t⇒ 𝒏)
  mapβSN (cong abs abs t⇒) (abs 𝒕)                     = abs (mapβSN t⇒ 𝒕)
  mapβSN (cong (pairl u)   (pairl .u) t⇒) (pair 𝒕 𝒕₁)  = pair (mapβSN t⇒ 𝒕) 𝒕₁
  mapβSN (cong (pairr t₁)  (pairr .t₁) t⇒) (pair 𝒕 𝒕₁) = pair 𝒕 (mapβSN t⇒ 𝒕₁)
  mapβSN (cong ▹_ ▹_ t⇒)   ▹0                          = ▹0
  mapβSN (cong ▹_ ▹_ t⇒)   (▹ 𝒕)                       = ▹ mapβSN t⇒ 𝒕
  mapβSN t⇒                (exp t⇒₁ 𝒕)                 with beta-shr t⇒ t⇒₁ 
  mapβSN t⇒ (exp t⇒₁ 𝒕) | inj₁ ≡.refl = 𝒕
  mapβSN t⇒ (exp t⇒₁ 𝒕) | inj₂ (_ , t⇒h , t⇒β*) = exp t⇒h (mapβ*SN t⇒β* 𝒕)

  mapβ*SN : ∀ {n}{a} {Γ} {t t' : Tm Γ a} → t ⇒β* t' → SN n t → SN n t'
  mapβ*SN []          𝒕 = 𝒕
  mapβ*SN (t⇒ ∷ t⇒β*) 𝒕 = mapβ*SN t⇒β* (mapβSN t⇒ 𝒕)