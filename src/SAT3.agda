-- Saturated sets.

{-# OPTIONS --copatterns --sized-types #-}

module SAT3 where

open import Library
open import SizedInfiniteTypes
open import Terms
open import Substitution
open import Reduction
open import SN
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

-- Function space.

_[→]_ : ∀{a b} → TmSet a → TmSet b → TmSet (a →̂ b)
(𝓐 [→] 𝓑) {Γ} t = ∀{Δ} (ρ : Δ ≤ Γ) → {u : Tm Δ _} → 𝓐 u → 𝓑 (app (rename ρ t) u)

-- Cartesian product.

_[×]_ :  ∀{a b} → TmSet a → TmSet b → TmSet (a ×̂ b)
(𝓐 [×] 𝓑) t = 𝓐 (fst t) × 𝓑 (snd t)


data [▸] {a∞} (𝑨 : TmSet (force a∞)) {Γ} : (n : ℕ) → Tm Γ (▸̂ a∞) → Set where
  ▹0  : ∀   {t    : Tm Γ (force a∞)}                                     → [▸] 𝑨 zero (▹ t)
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
    satRename : ∀ {Γ Δ} → (ρ : Ren Γ Δ) → ∀ {t} → 𝑨 t → 𝑨 (subst ρ t)
--open IsSAT

record SAT (a : Ty) (n : ℕ) : Set₁ where
  -- constructor sat
  field
    satSet  : TmSet a
    satProp : IsSAT n satSet

  open IsSAT satProp public
open SAT

SAT≤ : (a : Ty) (n : ℕ) → Set₁
SAT≤ a n = ∀ {m} → (m ≤ℕ n) → SAT a m

module SAT≤ {a : Ty} {n : ℕ} (𝓐 : SAT≤ a n) {m} (m≤n : m ≤ℕ _) where
  open SAT (𝓐 m≤n) public

-- Elementhood for saturated sets.
-- We use a record to instead of just application to help Agda's unifier.
record _∈_ {a n Γ} (t : Tm Γ a) (𝓐 : SAT a n) : Set where
  constructor ↿_
  field       ⇃_ : satSet 𝓐 t
open _∈_ public

_∈⟨_⟩_ : ∀ {a n Γ} (t : Tm Γ a) {m} (m≤n : m ≤ℕ n) (𝓐 : SAT≤ a n) → Set
t ∈⟨ m≤n ⟩ 𝓐 = t ∈ (𝓐 m≤n)

-- -- Workaround. Agda does not accept projection satSet directly,
-- -- maybe since it is defined in another module.
-- satSet' = satSet
-- syntax satSet' 𝓐 t = t ∈ 𝓐

-- Semantic function type.

_⟦→⟧_ : ∀ {n a b} (𝓐 : SAT≤ a n) (𝓑 : SAT≤ b n) → SAT (a →̂ b) n
𝓐 ⟦→⟧ 𝓑 = record
  { satSet  = 𝑪
  ; satProp = record
    { satSNe = CSNe
    ; satSN  = CSN
    ; satExp = CExp
    ; satRename = λ ρ {t} 𝒕 m m≤n ρ₁ {u} 𝒖 → ≡.subst (λ t₁ → 𝑩 {m} m≤n (app t₁ u)) (subst-∙ ρ₁ ρ t) (𝒕 m m≤n (λ x₂ → ρ₁ (ρ x₂)) 𝒖)
    }
  }
  where
    module 𝓐 = SAT≤ 𝓐
    module 𝓑 = SAT≤ 𝓑
    𝑨 = 𝓐.satSet
    𝑩 = 𝓑.satSet
    𝑪 : TmSet (_ →̂ _)
    𝑪 t = ∀ m (m≤n : m ≤ℕ _) → (𝑨 m≤n [→] 𝑩 m≤n) t

    CSNe : SNe _ ⊆ 𝑪
    CSNe 𝒏 m m≤n ρ 𝒖 = 𝓑.satSNe m≤n (sneApp (mapSNe m≤n (renameSNe ρ 𝒏)) (𝓐.satSN m≤n 𝒖))

    CSN : 𝑪 ⊆ SN _
    CSN 𝒕 = unRenameSN (prop→Ind suc ≡.refl) (absVarSN (𝓑.satSN ≤ℕ.refl (𝒕 _ ≤ℕ.refl suc (𝓐.satSNe ≤ℕ.refl (var v₀)))))

    CExp : ∀{Γ}{t t' : Tm Γ _} → t ⟨ _ ⟩⇒ t' → 𝑪 t' → 𝑪 t
    CExp t⇒ 𝒕 m m≤n ρ 𝒖 = 𝓑.satExp m≤n ((cong (appl _) (appl _) (map⇒ m≤n (subst⇒ (renSN ρ) t⇒)))) (𝒕 m m≤n ρ 𝒖)


-- Lemma: If 𝓐, 𝓑 ∈ SAT and t[u] ∈ 𝓑 for all a ∈ 𝓐, then λt ∈ 𝓐 ⟦→⟧ 𝓑

⟦abs⟧ : ∀{n a b}{𝓐 : SAT≤ a n}{𝓑 : SAT≤ b n}{Γ}{t : Tm (a ∷ Γ) b} →
    (∀ {m} (m≤n : m ≤ℕ n) {Δ} (ρ : Δ ≤ Γ) {u : Tm Δ a} →
      u ∈⟨ m≤n ⟩ 𝓐 → (subst0 u (subst (lifts ρ) t)) ∈⟨ m≤n ⟩ 𝓑 ) → abs t ∈ (𝓐 ⟦→⟧ 𝓑)
(⇃ ⟦abs⟧ {𝓐 = 𝓐}{𝓑 = 𝓑} 𝒕) m m≤n ρ 𝒖 =
  SAT≤.satExp 𝓑 m≤n (β (SAT≤.satSN 𝓐 m≤n 𝒖)) (⇃ 𝒕 m≤n ρ (↿ 𝒖))

-- Lemma: If 𝓐, 𝓑 ∈ SAT and t ∈ 𝓐 ⟦→⟧ 𝓑 and u ∈ 𝓐, then app t u ∈ 𝓑

⟦app⟧ : ∀ {n a b}{𝓐 : SAT≤ a n}{𝓑 : SAT≤ b n}{Γ}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} →
        ∀ {m} (m≤n : m ≤ℕ n) → t ∈ (𝓐 ⟦→⟧ 𝓑) → u ∈⟨ m≤n ⟩ 𝓐 → app t u ∈⟨ m≤n ⟩ 𝓑
⟦app⟧ {𝓑 = 𝓑} {u = u} m≤n (↿ 𝒕) (↿ 𝒖) = ≡.subst (λ t → app t u ∈⟨ m≤n ⟩ 𝓑) renId (↿ 𝒕 _ m≤n id 𝒖)


-- Semantic product type

_⟦×⟧_ : ∀ {n a b} (𝓐 : SAT a n) (𝓑 : SAT b n) → SAT (a ×̂ b) n
𝓐 ⟦×⟧ 𝓑 = record
  { satSet   = 𝑪
  ; satProp  = record
    { satSNe = CSNe
    ; satSN = CSN
    ; satExp = CExp
    ; satRename = λ ρ x → satRename 𝓐 ρ (proj₁ x) , satRename 𝓑 ρ (proj₂ x)
    }
  }
  where
    𝑨 = satSet 𝓐
    𝑩 = satSet 𝓑
    𝑪 : TmSet _
    𝑪 = 𝑨 [×] 𝑩

    CSNe : SNe _ ⊆ 𝑪
    CSNe 𝒏 = SAT.satSNe 𝓐 (elim  𝒏 fst)
           , SAT.satSNe 𝓑 (elim  𝒏 snd)

    CSN : 𝑪 ⊆ SN _
    CSN (𝒕₁ , 𝒕₂) = bothProjSN (SAT.satSN 𝓐 𝒕₁) (SAT.satSN 𝓑 𝒕₂)

    CExp : ∀{Γ}{t t' : Tm Γ _} → t ⟨ _ ⟩⇒ t' → 𝑪 t' → 𝑪 t
    CExp t⇒ (𝒕₁ , 𝒕₂) = SAT.satExp 𝓐 (cong fst fst t⇒) 𝒕₁
                      , SAT.satExp 𝓑 (cong snd snd t⇒) 𝒕₂


-- Lemma (introduction):  If t₁ ∈ 𝓐 and t₂ ∈ 𝓑 then pair t₁ t₂ ∈ 𝓐 ⟦×⟧ 𝓑

⟦pair⟧ : ∀ {n a b} {𝓐 : SAT a n} {𝓑 : SAT b n} {Γ} {t₁ : Tm Γ a} {t₂ : Tm Γ b}
         → t₁ ∈ 𝓐 → t₂ ∈ 𝓑 → pair t₁ t₂ ∈ (𝓐 ⟦×⟧ 𝓑)
⇃ ⟦pair⟧ {𝓐 = 𝓐} {𝓑 = 𝓑} (↿ 𝒕₁) (↿ 𝒕₂) = satExp 𝓐 (βfst (satSN 𝓑 𝒕₂)) 𝒕₁ , satExp 𝓑 (βsnd (satSN 𝓐 𝒕₁)) 𝒕₂

-- Lemma (elimination):  If t ∈ 𝓐 ⟦×⟧ 𝓑 then t₁ ∈ 𝓐 and t₂ ∈ 𝓑.

⟦fst⟧ : ∀ {n a b} {𝓐 : SAT a n} {𝓑 : SAT b n} {Γ} {t : Tm Γ (a ×̂  b)}
        → t ∈ (𝓐 ⟦×⟧ 𝓑) → fst t ∈ 𝓐
⟦fst⟧ 𝒕 =  ↿ (proj₁ (⇃ 𝒕))

⟦snd⟧ : ∀ {n a b} {𝓐 : SAT a n} {𝓑 : SAT b n} {Γ} {t : Tm Γ (a ×̂  b)}
        → t ∈ (𝓐 ⟦×⟧ 𝓑) → snd t ∈ 𝓑
⟦snd⟧ 𝒕 =  ↿ (proj₂ (⇃ 𝒕))

-- Any term set is saturated at level -1

SATpred : (a : Ty) (n : ℕ) → Set₁
SATpred a zero    = ⊤
SATpred a (suc n) = SAT a n

-- The underlying set at level -1 is the set of all terms of appropriate type

SATpredSet : {n : ℕ}{a : Ty} → SATpred a n → TmSet a
SATpredSet {zero}  𝓐 _ = ⊤
SATpredSet {suc n} 𝓐 = satSet 𝓐

-- Semantic delay type

module _ {a∞ : ∞Ty} where
  private
    a = force a∞
    𝑪 : ∀{n} (𝓐 : SATpred a n) → TmSet (▸̂ a∞)
    𝑪 {n} 𝓐 = [▸] (SATpredSet 𝓐) n

    CSN : ∀ {n} (𝓐 : SATpred a n) → 𝑪 {n} 𝓐 ⊆ SN n
    CSN 𝓐 ▹0         = ▹0
    CSN 𝓐 (▹ 𝒕)      = ▹ satSN 𝓐 𝒕
    CSN 𝓐 (ne 𝒏)     = ne 𝒏
    CSN 𝓐 (exp t⇒ 𝒕) = exp t⇒ (CSN 𝓐 𝒕)

    CRen : ∀ {n} (𝓐 : SATpred a n) → ∀ {Γ Δ} (ρ : Γ ≤ Δ) → ∀ {t} → 𝑪 {n} 𝓐 t → 𝑪 {n} 𝓐 (subst ρ t)
    CRen 𝓐 ρ ▹0         = ▹0
    CRen 𝓐 ρ (▹ 𝒕)      = ▹ satRename 𝓐 ρ 𝒕
    CRen 𝓐 ρ (ne 𝒏)     = ne (substSNe (ρ , (λ x → var (ρ x))) 𝒏)
    CRen 𝓐 ρ (exp t⇒ 𝒕) = exp (subst⇒ (ρ , (λ x → var (ρ x))) t⇒) (CRen 𝓐 ρ 𝒕)

  ⟦▸⟧_ : ∀{n} (𝓐 : SATpred a n) → SAT (▸̂ a∞) n
  ⟦▸⟧_ {n} 𝓐 = record
    { satSet = 𝑪 𝓐
    ; satProp = record
      { satSNe = ne
      ; satSN  = CSN 𝓐
      ; satExp = exp
      ; satRename = CRen 𝓐
      }
    }
