module TermShape where

open import Relation.Unary using (_∈_; _⊆_)
open import Size
open import Library
open import SizedInfiniteTypes
open import Terms
open import Substitution


-- Evaluation contexts.

data ECxt (Γ : Cxt) : (a b : Ty) → Set where
  appl  : ∀ {a b} (u : Tm Γ a)  → ECxt Γ (a →̂ b) b
  fst   : ∀ {a b} → ECxt Γ (a ×̂ b) a
  snd   : ∀ {a b} → ECxt Γ (a ×̂ b) b
  _∗l   : ∀ {a b∞} (u : Tm Γ (▸ a)) → ECxt Γ (▸̂ (delay (λ {_} → a) ⇒ b∞)) (▸̂ b∞)
  ∗r_   : ∀ {a : Ty}{b∞} (t : Tm Γ (a →̂ force b∞)) → ECxt Γ (▸ a) (▸̂ b∞)

-- Ehole Et E t ~~ Et = E[t]

data Ehole {Γ : Cxt} : {a b : Ty} → Tm Γ b → ECxt Γ a b → Tm Γ a → Set where
  appl  : ∀ {a b t} (u : Tm Γ a)  → Ehole (app t u) (appl u) (t ∶ (a →̂ b))
  fst   : ∀ {a b t} → Ehole {a = a ×̂ b} (fst t) fst t
  snd   : ∀ {a b t} → Ehole {a = a ×̂ b} (snd t) snd t
  _∗l   : ∀ {a b∞ t} (u : Tm Γ (▸ a)) → Ehole {a = (▸̂ (delay (λ {_} → a) ⇒ b∞))} (t ∗ u) (u ∗l) t
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

mkEHole : ∀ {Γ} {a b} (E : ECxt Γ a b) {t} → Σ _ \ E[t] → Ehole E[t] E t
mkEHole (appl u)  = _ , appl u
--mkEHole (appr t)  = _ , appr t
--mkEHole (pairl u) = _ , pairl u
--mkEHole (pairr t) = _ , pairr t
mkEHole fst       = _ , fst
mkEHole snd       = _ , snd
mkEHole (u ∗l)    = _ , u ∗l
mkEHole (∗r t)    = _ , ∗r t
--mkEHole abs       = _ , abs
--mkEHole ▹_        = _ , ▹_


_[_] : ∀ {Γ} {a b} (E : ECxt Γ a b) (t : Tm Γ a) → Tm Γ b
E [ t ] = proj₁ (mkEHole E {t})

data ECxt* (Γ : Cxt) : Ty → Ty → Set where
  [] : ∀ {a} → ECxt* Γ a a
  _∷_ : ∀ {a₀ a₁ a₂} → ECxt Γ a₀ a₁ → ECxt* Γ a₁ a₂ → ECxt* Γ a₀ a₂

_[_]* : ∀ {Γ} {a b} (E : ECxt* Γ a b) (t : Tm Γ a) → Tm Γ b
[] [ t ]* = t
(E ∷ Es) [ t ]* = Es [ E [ t ] ]*

_++*_ : ∀ {Γ a b c} → ECxt* Γ a b → ECxt* Γ b c → ECxt* Γ a c
[] ++* ys = ys
(x ∷ xs) ++* ys = x ∷ (xs ++* ys)

_∷r_ : ∀ {Γ a b c} → ECxt* Γ a b → ECxt Γ b c → ECxt* Γ a c
xs ∷r x = xs ++* (x ∷ [])

data Ehole* {Γ : Cxt} : {a b : Ty} → Tm Γ b → ECxt* Γ a b → Tm Γ a → Set where
  [] : ∀ {a} {t : Tm Γ a} → Ehole* t [] t
  _∷_ : ∀ {a b c t} {E : ECxt Γ b c} {Es : ECxt* Γ a b} {EEst Est}
        → Ehole EEst E Est → Ehole* Est Es t → Ehole* EEst (Es ∷r E) t


-- Inductive definition of strong normalization.


-- Parameterized evaluation contexts

data PCxt {Γ : Cxt} (P : ∀{c} → Tm Γ c → Set) : {a b : Ty} → Tm Γ b → ECxt Γ a b → Tm Γ a → Set where

  appl  : ∀ {a b t u}
          → (𝒖 : P u)
          → PCxt P (app t u) (appl u) (t ∶ (a →̂ b))

  fst   : ∀ {a b t}                 → PCxt P (fst {a = a} {b = b} t) fst t

  snd   : ∀ {a b t}                 → PCxt P (snd {a = a} {b = b} t) snd t

  _∗l   : ∀ {a b∞ t u} (𝒖 : P u) → PCxt P (_∗_ {a = a} {b∞} t u) (u ∗l) t

  ∗r_   : ∀ {a : Ty}{b∞}{u t}
            (𝒕 : P (▹_ {a∞ = delay (λ {_} → a) ⇒ b∞} t))
                                    → PCxt P (_<$>_ {a = a} {b∞} t u) (∗r t) u

-- Parameterized neutral terms.

data PNe {Γ} (P : ∀{c} → Tm Γ c → Set) {b} : Tm Γ b → Set where

  var  : ∀ x                              → PNe P (var x)

  elim : ∀ {a} {t : Tm Γ a} {E Et}
         → (𝒏 : PNe P t) (𝑬𝒕 : PCxt P Et E t) → PNe P Et

-- Parametrized weak head reduction

infix 10 _/_⇒_

data _/_⇒_ {Γ} (P : ∀{c} → Tm Γ c → Set): ∀ {a} → Tm Γ a  → Tm Γ a → Set where

  β     : ∀ {a b}{t : Tm (a ∷ Γ) b}{u}
          → (𝒖 : P u)
          → P / (app (abs t) u) ⇒ subst0 u t

  β▹    : ∀ {a b∞}{t : Tm Γ (a →̂  force b∞)}{u : Tm Γ a}
           → P / (▹ t ∗ ▹ u) ⇒ (▹_ {a∞ = b∞} (app t u))

  βfst  : ∀ {a b}{t : Tm Γ a}{u : Tm Γ b}
          → (𝒖 : P u)
          → P / fst (pair t u) ⇒ t

  βsnd  : ∀ {a b}{t : Tm Γ a}{u : Tm Γ b}
          → (𝒕 : P t)
          → P / snd (pair t u) ⇒ u

  cong  : ∀ {a b t t' Et Et'}{E : ECxt Γ a b}
          → (𝑬𝒕 : Ehole Et E t)
          → (𝑬𝒕' : Ehole Et' E t')
          → (t⇒ : P / t ⇒ t')
          → P / Et ⇒ Et'

-- Weak head reduction is deterministic.

detP⇒ : ∀ {a Γ} {P : ∀ {c} → Tm Γ c → Set} {t t₁ t₂ : Tm Γ a}
       → (t⇒₁ : P / t ⇒ t₁) (t⇒₂ : P / t ⇒ t₂) → t₁ ≡ t₂
detP⇒ (β _) (β _)                                              = ≡.refl
detP⇒ (β _) (cong (appl u) (appl .u) (cong () _ _))
detP⇒ β▹ β▹ = ≡.refl
detP⇒ β▹ (cong (._ ∗l) (._ ∗l) (cong () _ _))
detP⇒ β▹ (cong (∗r t) (∗r .t) (cong () _ _ ))
detP⇒ (βfst _) (βfst _)                                        = ≡.refl
detP⇒ (βfst _) (cong fst fst (cong () _ _))
detP⇒ (βsnd _) (βsnd _)                                        = ≡.refl
detP⇒ (βsnd 𝒕) (cong snd snd (cong () _ _))
detP⇒ (cong (appl u) (appl .u) (cong () _ _)) (β _)
detP⇒ (cong (._ ∗l) (._ ∗l) (cong () _ _)) β▹
detP⇒ (cong (∗r t₁) (∗r .t₁) (cong () _ _)) β▹
detP⇒ (cong fst fst (cong () _ _ )) (βfst _)
detP⇒ (cong snd snd (cong () _ _ )) (βsnd _)
detP⇒ (cong (appl u) (appl .u) x) (cong (appl .u) (appl .u) y) = ≡.cong (λ t → app t u) (detP⇒ x y)
detP⇒ (cong fst fst x) (cong fst fst y)                        = ≡.cong fst             (detP⇒ x y)
detP⇒ (cong snd snd x) (cong snd snd y)                        = ≡.cong snd             (detP⇒ x y)
detP⇒ (cong (u ∗l) (.u ∗l) x) (cong (.u ∗l) (.u ∗l) y)         = ≡.cong (λ t → t ∗ u)   (detP⇒ x y)
detP⇒ (cong (∗r t) (∗r .t) x) (cong (∗r .t) (∗r .t) y)         = ≡.cong (_∗_ (▹ t))     (detP⇒ x y)
detP⇒ (cong (u ∗l) (.u ∗l) (cong () _ _)) (cong (∗r t) (∗r .t) _)
detP⇒ (cong (∗r t) (∗r .t) _) (cong (u ∗l) (.u ∗l) (cong () _ _))

-- Neutrals are closed under application.

pneApp : ∀{Γ a b}{P : ∀{c} → Tm Γ c → Set}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} →
  PNe P t → P u → PNe P (app t u)
pneApp 𝒏 𝒖 = elim 𝒏 (appl 𝒖)


-- Functoriality of the notions wrt. P.

mapPCxt : ∀ {Γ} {P Q : ∀{c} → Tm Γ c → Set} (P⊆Q : ∀ {c}{t : Tm Γ c} → P t → Q t) {a b} {E : ECxt Γ a b}{Et t} → PCxt P Et E t -> PCxt Q Et E t
mapPCxt P⊆Q (appl u∈P) = appl (P⊆Q u∈P)
mapPCxt P⊆Q fst = fst
mapPCxt P⊆Q snd = snd
mapPCxt P⊆Q (u∈P ∗l) = P⊆Q u∈P ∗l
mapPCxt P⊆Q (∗r t∈P) = ∗r P⊆Q t∈P

mapPNe : ∀ {Γ} {P Q : ∀{c} → Tm Γ c → Set} (P⊆Q : ∀ {c}{t : Tm Γ c} → P t → Q t) {a}{t : Tm Γ a} → PNe P t -> PNe Q t
mapPNe P⊆Q (var x) = var x
mapPNe P⊆Q (elim t∈Ne E∈SNh) = elim (mapPNe P⊆Q t∈Ne) (mapPCxt P⊆Q E∈SNh)

mapP⇒ : ∀ {Γ} {P Q : ∀{c} → Tm Γ c → Set} (P⊆Q : ∀ {c}{t : Tm Γ c} → P t → Q t) {a}{t t' : Tm Γ a} → P / t ⇒ t' → Q / t ⇒ t'
mapP⇒ P⊆Q (β t∈P) = β (P⊆Q t∈P)
mapP⇒ P⊆Q (β▹ {a = a}) = β▹ {a = a}
mapP⇒ P⊆Q (βfst t∈P) = βfst (P⊆Q t∈P)
mapP⇒ P⊆Q (βsnd t∈P) = βsnd (P⊆Q t∈P)
mapP⇒ P⊆Q (cong Et Et' t→t') = cong Et Et' (mapP⇒ P⊆Q t→t')


_[_]⇒ : ∀ {Γ} {P : ∀{c} → Tm Γ c → Set} {a b} (E : ECxt Γ a b) {t₁ t₂ : Tm Γ a} → P / t₁ ⇒ t₂ → P / E [ t₁ ] ⇒ E [ t₂ ]
E [ t⇒ ]⇒ = cong (proj₂ (mkEHole E)) (proj₂ (mkEHole E)) t⇒

_[_]⇒* : ∀ {Γ} {P : ∀{c} → Tm Γ c → Set} {a b} (E : ECxt* Γ a b) {t₁ t₂ : Tm Γ a} → P / t₁ ⇒ t₂ → P / E [ t₁ ]* ⇒ E [ t₂ ]*
[]       [ t⇒ ]⇒* = t⇒
(E ∷ Es) [ t⇒ ]⇒* = Es [ E [ t⇒ ]⇒ ]⇒*

hole→≡ : ∀ {Γ a b}{Et t}{E : ECxt Γ a b} → (Es : Ehole Et E t) → Et ≡ E [ t ]
hole→≡ (appl u) = ≡.refl
hole→≡ fst = ≡.refl
hole→≡ snd = ≡.refl
hole→≡ (u ∗l) = ≡.refl
hole→≡ (∗r t₁) = ≡.refl

lemma : ∀ {Γ b} {a} {t : Tm Γ a} (Es : ECxt* Γ a b)
         {b₁} {E : ECxt Γ b b₁}
         → E [ Es [ t ]* ] ≡ (Es ++* (E ∷ [])) [ t ]*
lemma [] = ≡.refl
lemma (x ∷ Es) = lemma Es

hole*→≡ : ∀ {Γ a b}{Et t}{E : ECxt* Γ a b} → (Es : Ehole* Et E t) → Et ≡ E [ t ]*
hole*→≡ [] = ≡.refl
hole*→≡ {t = t} (_∷_ {Es = Es} x Es₁) rewrite hole→≡ x | hole*→≡ Es₁ = lemma Es

++*-unit : ∀ {Γ a b} → (xs : ECxt* Γ a b) → xs ++* [] ≡ xs
++*-unit [] = ≡.refl
++*-unit (x ∷ xs) = ≡.cong (_∷_ x) (++*-unit xs)
++*-assoc : ∀ {Γ a b c d} → (xs : ECxt* Γ a b) → {ys : ECxt* Γ b c} → {zs : ECxt* Γ c d} → xs ++* (ys ++* zs) ≡ (xs ++* ys) ++* zs
++*-assoc [] = ≡.refl
++*-assoc (x ∷ xs) = ≡.cong (_∷_ x) (++*-assoc xs)

_++h*_ : ∀ {Γ a b c} {Es1 : ECxt* Γ a b} {Es2 : ECxt* Γ b c} → ∀ {t1 t2 t3} → Ehole* t2 Es1 t3 → Ehole* t1 Es2 t2  → Ehole* t1 (Es1 ++* Es2) t3
_++h*_ {Es1 = Es1} xs [] rewrite ++*-unit Es1      = xs
_++h*_ {Es1 = Es1} xs (_∷_ {E = E} {Es = Es} x ys) rewrite ++*-assoc Es1 {Es} {E ∷ []} = x ∷ (xs ++h* ys)


mkEhole* : ∀ {Γ} {a b} (E : ECxt* Γ a b) {t} → Ehole* (E [ t ]*) E t
mkEhole* [] = []
mkEhole* (E ∷ Es) {t} = (proj₂ (mkEHole E) ∷ []) ++h* mkEhole* Es
