-- Saturated sets.

{-# OPTIONS --copatterns --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

module SAT where

open import Library
open import SizedInfiniteTypes
open import Terms
open import Substitution
open import SN
open import SN.AntiSubst
open import SN.AntiRename

-- Kripke predicates on well-typed terms.

TmSet : (a : Ty) → Set₁
TmSet a = {Γ : Cxt} (t : Tm Γ a) → Set

_⊆_ : ∀{a} (𝑨 𝑨′ : TmSet a) → Set
𝑨 ⊆ 𝑨′ = ∀{Γ}{t : Tm Γ _} → 𝑨 t → 𝑨′ t

-- Closure by strong head expansion

Closed : ∀ (n : ℕ) {a} (𝑨 : TmSet a) → Set
Closed n 𝑨 = ∀{Γ}{t t' : Tm Γ _} → t ⟨ n ⟩⇒ t' → 𝑨 t' → 𝑨 t

data Cl (n : ℕ) {a} (𝑨 : TmSet a) {Γ} (t : Tm Γ a) : Set where
  emb : 𝑨 t                             → Cl n 𝑨 t
  exp : ∀{t'} → t ⟨ n ⟩⇒ t' → Cl n 𝑨 t' → Cl n 𝑨 t

-- Operations on predicates.

_[→]_ : ∀{a b} → TmSet a → TmSet b → TmSet (a →̂ b)
(𝓐 [→] 𝓑) {Γ} t = ∀{Δ} (ρ : Δ ≤ Γ) {u : Tm Δ _} → 𝓐 u → 𝓑 (app (rename ρ t) u)

_[×]_ :  ∀{a b} → TmSet a → TmSet b → TmSet (a ×̂ b)
(𝓐 [×] 𝓑) t = 𝓐 (fst t) × 𝓑 (snd t)

data [▸] {a∞} (𝑨 : TmSet (force a∞)) {Γ} : (n : ℕ) → Tm Γ (▸̂ a∞) → Set where
  ▹0_ : ∀   {t    : Tm Γ (force a∞)}                                     → [▸] 𝑨 zero (▹ t)
  ▹_  : ∀{n}{t    : Tm Γ (force a∞)} (𝒕 : 𝑨 t)                           → [▸] 𝑨 (suc n) (▹ t)
  ne  : ∀{n}{t    : Tm Γ (▸̂ a∞)}     (𝒏 : SNe n t)                       → [▸] 𝑨 n t
  exp : ∀{n}{t t' : Tm Γ (▸̂ a∞)}     (t⇒ : t ⟨ n ⟩⇒ t') (𝒕 : [▸] 𝑨 n t') → [▸] 𝑨 n t

-- Saturated term sets.

record IsSAT (n : ℕ) {a} (𝑨 : TmSet a) : Set where
  -- constructor isSat
  field
    satSNe  : SNe n ⊆ 𝑨
    satSN   : 𝑨 ⊆ SN n
    satExp  : Closed n 𝑨
--open IsSAT

record SAT : Set₁ where
  field
    {satTy}  : Ty
    satSet : ℕ → TmSet satTy
    satMono  : ∀ {m n}{Γ}{t : Tm Γ satTy} → m ≤ℕ n → satSet n t → satSet m t 
    satProp : ∀ {n} → IsSAT n (satSet n)
  open module X {n} = IsSAT (satProp {n}) public
open SAT    
{-
record SAT (n : ℕ) : Set₁ where
  -- constructor sat
  field
    {satTy} : Ty
    satSet  : TmSet satTy
    satProp : IsSAT n satSet
  open IsSAT satProp public
open SAT
-}
-- Elementhood for saturated sets.

-- Workaround. Agda does not accept projection satSet directly,
-- maybe since it is defined in another module.
satSet' = \ 𝓐 {Γ} t n → satSet 𝓐 n {Γ} t
syntax satSet' 𝓐 t n = t ∈ 𝓐 at n

-- Semantic function type.

_⟦→⟧_ : (𝓐 𝓑 : SAT) → SAT
𝓐 ⟦→⟧ 𝓑 = record
  { satTy   = satTy 𝓐 →̂ satTy 𝓑
  ; satSet  = 𝑪
  ; satMono = λ m≤n Cnt l≤m ρ Alu → Cnt (≤ℕ.trans l≤m m≤n) ρ Alu
  ; satProp = record 
    { satSNe = CSNe 
    ; satSN  = CSN 
    ; satExp = CExp 
    }
  }
  where
    𝑨 = satSet 𝓐
    𝑩 = satSet 𝓑
    𝑪 : ℕ → TmSet _
    𝑪 = λ n t → ∀ {m} → m ≤ℕ n → (𝑨 m [→] 𝑩 m) t

    CSNe : ∀ {n} → SNe n ⊆ 𝑪 n
    CSNe 𝒏 m≤n ρ 𝒖 = satSNe 𝓑 (sneApp (renameSNe ρ (mapSNe m≤n 𝒏)) (satSN 𝓐 𝒖))

    CSN : ∀ {n} → 𝑪 n ⊆ SN n
    CSN 𝒕 = unRenameSN (prop→Ind suc ≡.refl)
              (absVarSN (satSN 𝓑 (𝒕 ≤ℕ.refl suc (satSNe 𝓐 (var (zero ≅refl))))))

    CExp : ∀{n}{Γ}{t t' : Tm Γ _} → t ⟨ n ⟩⇒ t' → 𝑪 n t' → 𝑪 n t 
    CExp t⇒ 𝒕 m≤n ρ 𝒖 = satExp 𝓑 (cong (appl _) (appl _) (subst⇒ (renSN ρ) (map⇒ m≤n t⇒))) (𝒕 m≤n ρ 𝒖)

-- Lemma: If 𝓐, 𝓑 ∈ SAT and t[u] ∈ 𝓑 for all a ∈ 𝓐, then λt ∈ 𝓐 ⟦→⟧ 𝓑

module _ {𝓐 𝓑 : SAT} where
  private
    a = SAT.satTy 𝓐
    b = SAT.satTy 𝓑

  semAbs : ∀{n}{Γ}{t : Tm (a ∷ Γ) b} →
    (∀{m} → m ≤ℕ n → ∀ {Δ} (ρ : Δ ≤ Γ) {u : Tm Δ a} → u ∈ 𝓐 at m → satSet 𝓑 m (subst0 u (subst (lifts ρ) t))) → satSet (𝓐 ⟦→⟧ 𝓑) n (abs t)
  semAbs 𝒕 m≤n ρ 𝒖 = satExp 𝓑 (β (satSN 𝓐 𝒖)) (𝒕 m≤n ρ 𝒖)

-- Semantic product type

_⟦×⟧_ : (𝓐 𝓑 : SAT) → SAT
𝓐 ⟦×⟧ 𝓑 = record
  { satSet   = 𝑪
  ; satMono  = λ m≤n → map× (satMono 𝓐 m≤n) (satMono 𝓑 m≤n)
  ; satProp  = record
    { satSNe = CSNe
    ; satSN  = CSN
    ; satExp = CExp
    }
  }
  where
    𝑨 = satSet 𝓐
    𝑩 = satSet 𝓑
    𝑪 : ℕ → TmSet _
    𝑪 = \ n → 𝑨 n [×] 𝑩 n

    CSNe : ∀ {n} → SNe n ⊆ 𝑪 n
    CSNe 𝒏 = (SAT.satSNe 𝓐 (elim  𝒏 fst))
           , (SAT.satSNe 𝓑 (elim  𝒏 snd))

    CSN : ∀ {n} → 𝑪 n ⊆ SN n
    CSN (𝒕₁ , 𝒕₂) = bothProjSN (SAT.satSN 𝓐 𝒕₁) (SAT.satSN 𝓑 𝒕₂)

    CExp : ∀{n}{Γ}{t t' : Tm Γ _} → t ⟨ n ⟩⇒ t' → 𝑪 n t' → 𝑪 n t
    CExp t⇒ (𝒕₁ , 𝒕₂) = (SAT.satExp 𝓐 (cong fst fst t⇒) 𝒕₁)
                     , (SAT.satExp 𝓑 (cong snd snd t⇒) 𝒕₂)

semPair : ∀ {𝓐 𝓑 : SAT} → ∀ {Γ}{t : Tm Γ _}{u : Tm Γ _} → ∀ {n} → t ∈ 𝓐 at n → u ∈ 𝓑 at n → pair t u ∈ (𝓐 ⟦×⟧ 𝓑) at n
semPair {𝓐} {𝓑} 𝒕 𝒖 = satExp 𝓐 (βfst (satSN 𝓑 𝒖)) 𝒕 , satExp 𝓑 (βsnd (satSN 𝓐 𝒕)) 𝒖

-- Semantic delay type

⟦▸⟧_ : (𝓐 : SAT) → SAT
⟦▸⟧_ 𝓐 = record
  { satSet = 𝑪
  ; satMono = CMono
  ; satProp = record
    { satSNe = ne
    ; satSN  = CSN
    ; satExp = exp
    }
  }
  where
    𝑪 : ℕ → TmSet (▸ _)
    𝑪 n = [▸] (satSet 𝓐 (pred n)) n

    CMono : {m n : ℕ} {Γ : List Ty} {t : Tm Γ (▸ satTy 𝓐)} → m ≤ℕ n → 𝑪 n t → 𝑪 m t
    CMono z≤n ▹0_ = ▹0_
    CMono z≤n (▹ 𝒕) = ▹0_
    CMono (s≤s m≤n) (▹ 𝒕) = ▹ (satMono 𝓐 m≤n 𝒕)
    CMono m≤n (ne 𝒏) = ne (mapSNe m≤n 𝒏)
    CMono m≤n (exp t⇒ 𝒕) = exp (map⇒ m≤n t⇒) (CMono m≤n 𝒕)

    CSN : ∀ {n} → 𝑪 n ⊆ SN n
    CSN  ▹0_        = ▹0
    CSN  (▹ 𝒕)      = ▹ satSN 𝓐 𝒕
    CSN  (ne 𝒏)     = ne 𝒏
    CSN  (exp t⇒ 𝒕) = exp t⇒ (CSN 𝒕)

sem∗ : ∀ {𝓐 𝓑 : SAT} → let a = satTy 𝓐; b = satTy 𝓑 in
       ∀ {Γ}{t : Tm Γ  _}{u : Tm Γ (▸ a)} → ∀ {n} → t ∈ ⟦▸⟧ (𝓐 ⟦→⟧ 𝓑) at n → u ∈ ⟦▸⟧ 𝓐 at n → ▹app (≅delay ≅refl) t u ∈ ⟦▸⟧ 𝓑 at n
sem∗ ▹0_ ▹0_ = exp β▹ ▹0_
sem∗ ▹0_ (ne 𝒏) = {!!}
sem∗ ▹0_ (exp t⇒ 𝒖) = {!!}
sem∗ (▹ 𝒕) (▹ 𝒕₁) = exp β▹ (▹ {!𝒕!})
sem∗ (▹ 𝒕) (ne 𝒏) = {!!}
sem∗ (▹ 𝒕) (exp t⇒ 𝒖) = exp (cong (∗r _) (∗r _) t⇒) (sem∗ {{!!}} {{!!}} {{!!}} {{!!}} {{!!}} {{!!}} {! (▹ 𝒕) !} {! 𝒖 !})
sem∗ (ne 𝒏) 𝒖 = {!!}
sem∗ (exp t⇒ 𝒕) 𝒖 = {!!}
