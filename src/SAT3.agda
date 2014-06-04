-- Saturated sets.

{-# OPTIONS --copatterns --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

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
    satSet  : ∀ {m} .(m≤n : m ≤ℕ n) → TmSet a
    satProp : ∀ {m} .(m≤n : m ≤ℕ n) → IsSAT m (satSet m≤n)

  open module X {m} .(m≤n : m ≤ℕ n) = IsSAT (satProp m≤n) public
open SAT

-- Elementhood for saturated sets.
-- We use a record to instead of just application to help Agda's unifier.
record _∈⟨_⟩_ {a n Γ} (t : Tm Γ a) {m} .(m≤n : m ≤ℕ n) (𝓐 : SAT a n) : Set where
  constructor ↿_
  field       ⇃_ : satSet 𝓐 m≤n t
open _∈⟨_⟩_ public

_∈_ : ∀ {a n Γ} (t : Tm Γ a) (𝓐 : SAT a n) → Set
t ∈ 𝓐 = t ∈⟨ ≤ℕ.refl ⟩ 𝓐
-- -- Workaround. Agda does not accept projection satSet directly,
-- -- maybe since it is defined in another module.
-- satSet' = satSet
-- syntax satSet' 𝓐 t = t ∈ 𝓐

-- Semantic function type.

_⟦→⟧_ : ∀ {n a b} (𝓐 : SAT a n) (𝓑 : SAT b n) → SAT (a →̂ b) n
𝓐 ⟦→⟧ 𝓑 = record
  { satSet  = 𝑪
  ; satProp = λ m≤n → record
    { satSNe = CSNe m≤n
    ; satSN  = CSN  m≤n
    ; satExp = CExp m≤n
    ; satRename = λ ρ {t} 𝒕 l l≤m ρ₁ {u} 𝒖 → ≡.subst (λ t → 𝑩 {l} _ (app t u)) (subst-∙ ρ₁ ρ t) (𝒕 l l≤m (λ x₂ → ρ₁ (ρ x₂)) 𝒖)
    }
  }
  where
    𝑨 = satSet 𝓐
    𝑩 = satSet 𝓑
    𝑪 : ∀ {m} .(m≤n : m ≤ℕ _) → TmSet (_ →̂ _)
    𝑪 {m} m≤n t = ∀ l .l≤m →
      let .l≤n : l ≤ℕ _
          l≤n = ≤ℕ.trans l≤m m≤n in
      ((𝑨 l≤n) [→] (𝑩 l≤n)) t

    CSNe : ∀ {m} .(m≤n : m ≤ℕ _) → SNe m ⊆ 𝑪 m≤n
    CSNe m≤n 𝒏 l l≤m ρ 𝒖 = let .l≤n : _ ; l≤n = ≤ℕ.trans l≤m m≤n in SAT.satSNe 𝓑 l≤n (sneApp (mapSNe l≤m (renameSNe ρ 𝒏)) (SAT.satSN 𝓐 l≤n 𝒖))

    CSN : ∀ {m} .(m≤n : m ≤ℕ _) → 𝑪 m≤n ⊆ SN m
    CSN {m} m≤n 𝒕 = unRenameSN (prop→Ind suc ≡.refl) (absVarSN (SAT.satSN 𝓑 m≤n (𝒕 m ≤ℕ.refl suc (SAT.satSNe 𝓐 m≤n (var v₀)))))

    CExp : ∀ {m} .(m≤n : m ≤ℕ _) →  ∀{Γ}{t t' : Tm Γ _} → t ⟨ _ ⟩⇒ t' → 𝑪 m≤n t' → 𝑪 m≤n t
    CExp m≤n t⇒ 𝒕 l l≤m ρ 𝒖 = let .l≤n : _ ; l≤n = ≤ℕ.trans l≤m m≤n in SAT.satExp 𝓑 l≤n ((cong (appl _) (appl _) (map⇒ l≤m (subst⇒ (renSN ρ) t⇒)))) (𝒕 l l≤m ρ 𝒖)


-- Lemma: If 𝓐, 𝓑 ∈ SAT and t[u] ∈ 𝓑 for all a ∈ 𝓐, then λt ∈ 𝓐 ⟦→⟧ 𝓑

⟦abs⟧ : ∀{n a b}{𝓐 : SAT a n}{𝓑 : SAT b n}{Γ}{t : Tm (a ∷ Γ) b}{m} → .(m≤n : m ≤ℕ n) →
    (∀ {l} .(l≤m : l ≤ℕ m) {Δ} (ρ : Δ ≤ Γ) {u : Tm Δ a} → let .l≤n : _ ; l≤n = ≤ℕ.trans l≤m m≤n in  
      u ∈⟨ l≤n ⟩ 𝓐 → (subst0 u (subst (lifts ρ) t)) ∈⟨ l≤n ⟩ 𝓑 ) → abs t ∈⟨ m≤n ⟩ (𝓐 ⟦→⟧ 𝓑)
(⇃ ⟦abs⟧ {𝓐 = 𝓐}{𝓑 = 𝓑} m≤n 𝒕) l l≤m ρ 𝒖 = let .l≤n : _ ; l≤n = ≤ℕ.trans l≤m m≤n in
  SAT.satExp 𝓑 l≤n (β (SAT.satSN 𝓐 l≤n 𝒖)) (⇃ (𝒕 l≤m ρ (↿ 𝒖)))

-- Lemma: If 𝓐, 𝓑 ∈ SAT and t ∈ 𝓐 ⟦→⟧ 𝓑 and u ∈ 𝓐, then app t u ∈ 𝓑

⟦app⟧ : ∀ {n a b}{𝓐 : SAT a n}{𝓑 : SAT b n}{Γ}{t : Tm Γ (a →̂ b)}{u : Tm Γ a} →
        ∀ {m} .(m≤n : m ≤ℕ n) → t ∈⟨ m≤n ⟩ (𝓐 ⟦→⟧ 𝓑) → u ∈⟨ m≤n ⟩ 𝓐 → app t u ∈⟨ m≤n ⟩ 𝓑
⟦app⟧ {𝓑 = 𝓑} {u = u} m≤n (↿ 𝒕) (↿ 𝒖) = ≡.subst (λ t → app t u ∈⟨ m≤n ⟩ 𝓑) renId (↿ 𝒕 _ ≤ℕ.refl id 𝒖)

-- Semantic product type

_⟦×⟧_ : ∀ {n a b} (𝓐 : SAT a n) (𝓑 : SAT b n) → SAT (a ×̂ b) n
𝓐 ⟦×⟧ 𝓑 = record
  { satSet   = 𝑪
  ; satProp  = λ m≤n → record
    { satSNe = CSNe m≤n
    ; satSN = CSN m≤n
    ; satExp = CExp m≤n
    ; satRename = λ ρ x → (satRename 𝓐 m≤n ρ (proj₁ x)) , (satRename 𝓑 m≤n ρ (proj₂ x))
    }
  }
  where
    𝑨 = satSet 𝓐
    𝑩 = satSet 𝓑
    𝑪 : ∀ {m} .(m≤n : m ≤ℕ _) → TmSet _
    𝑪 = λ {m} m≤n t → (𝑨 m≤n [×] 𝑩 m≤n) t

    CSNe : ∀ {m} .(m≤n : m ≤ℕ _) → SNe m ⊆ 𝑪 m≤n
    CSNe m≤n 𝒏 = (SAT.satSNe 𝓐 m≤n (elim  𝒏 fst))
           , (SAT.satSNe 𝓑 m≤n (elim  𝒏 snd))

    CSN : ∀ {m} .(m≤n : m ≤ℕ _) → 𝑪 m≤n ⊆ SN m
    CSN m≤n (𝒕₁ , 𝒕₂) = bothProjSN (SAT.satSN 𝓐 m≤n 𝒕₁) (SAT.satSN 𝓑 m≤n 𝒕₂)

    CExp : ∀ {m} .(m≤n : m ≤ℕ _) →  ∀{Γ}{t t' : Tm Γ _} → t ⟨ _ ⟩⇒ t' → (𝑪 m≤n) t' → (𝑪 m≤n) t
    CExp m≤n t⇒ (𝒕₁ , 𝒕₂) = (SAT.satExp 𝓐 m≤n (cong fst fst t⇒) 𝒕₁)
                     , (SAT.satExp 𝓑 m≤n (cong snd snd t⇒) 𝒕₂)


-- Lemma (introduction):  If t₁ ∈ 𝓐 and t₂ ∈ 𝓑 then pair t₁ t₂ ∈ 𝓐 ⟦×⟧ 𝓑

⟦pair⟧ : ∀ {n a b} {𝓐 : SAT a n} {𝓑 : SAT b n} {Γ} {t₁ : Tm Γ a} {t₂ : Tm Γ b}
         → ∀ {m} .(m≤n : m ≤ℕ _) → t₁ ∈⟨ m≤n ⟩ 𝓐 → t₂ ∈⟨ m≤n ⟩ 𝓑 → pair t₁ t₂ ∈⟨ m≤n ⟩ (𝓐 ⟦×⟧ 𝓑)
⇃ ⟦pair⟧ {𝓐 = 𝓐} {𝓑 = 𝓑} m≤n (↿ 𝒕₁) (↿ 𝒕₂) = satExp 𝓐 m≤n (βfst (satSN 𝓑 m≤n 𝒕₂)) 𝒕₁ , satExp 𝓑 m≤n (βsnd (satSN 𝓐 m≤n 𝒕₁)) 𝒕₂

-- Lemma (elimination):  If t ∈ 𝓐 ⟦×⟧ 𝓑 then t₁ ∈ 𝓐 and t₂ ∈ 𝓑.

⟦fst⟧ : ∀ {n a b} {𝓐 : SAT a n} {𝓑 : SAT b n} {Γ} {t : Tm Γ (a ×̂  b)}
        → ∀ {m} .(m≤n : m ≤ℕ _) → t ∈⟨ m≤n ⟩ (𝓐 ⟦×⟧ 𝓑) → fst t ∈⟨ m≤n ⟩ 𝓐
⟦fst⟧ m≤n 𝒕 =  ↿ (proj₁ (⇃ 𝒕))

⟦snd⟧ : ∀ {n a b} {𝓐 : SAT a n} {𝓑 : SAT b n} {Γ} {t : Tm Γ (a ×̂  b)}
        → ∀ {m} .(m≤n : m ≤ℕ n) → t ∈⟨ m≤n ⟩ (𝓐 ⟦×⟧ 𝓑) → snd t ∈⟨ m≤n ⟩ 𝓑
⟦snd⟧ m≤n 𝒕 =  ↿ (proj₂ (⇃ 𝒕))

-- Any term set is saturated at level -1

SATpred : (a : Ty) (n : ℕ) → Set₁
SATpred a zero    = ⊤
SATpred a (suc n) = SAT a n

-- The underlying set at level -1 is the set of all terms of appropriate type

SATpredSet : {n : ℕ}{a : Ty} → SATpred a n → ∀ {m} → .(m ≤ℕ n) → TmSet a
SATpredSet {_}     𝓐 {zero}  m≤n _ = ⊤
SATpredSet {suc n} 𝓐 {suc m} m≤n = satSet 𝓐 (pred≤ℕ m≤n) 
SATpredSet {zero}  _ {suc _} ()

-- Semantic delay type

module _ {a∞ : ∞Ty} where
  private
    a = force a∞
    𝑪 : ∀{n} (𝓐 : SATpred a n) → ∀ {m} → .(m ≤ℕ n) → TmSet (▸̂ a∞)
    𝑪 {n} 𝓐 {m} m≤n = [▸] (SATpredSet 𝓐 m≤n) m

    CSN : ∀ {n} (𝓐 : SATpred a n) → ∀ {m} → .(m≤n : m ≤ℕ n) → 𝑪 {n} 𝓐  m≤n ⊆ SN m
    CSN         𝓐 m≤n ▹0         = ▹0
    CSN {zero}  𝓐 ()  (▹ 𝒕)
    CSN {suc n} 𝓐 m≤n (▹ 𝒕)      = ▹ satSN 𝓐 (pred≤ℕ m≤n) 𝒕
    CSN         𝓐 m≤n (ne 𝒏)     = ne 𝒏
    CSN         𝓐 m≤n (exp t⇒ 𝒕) = exp t⇒ (CSN 𝓐 m≤n 𝒕)

    CRen : ∀ {n} (𝓐 : SATpred a n) → ∀ {m} → .(m≤n : m ≤ℕ n) → ∀ {Γ Δ} (ρ : Γ ≤ Δ) → ∀ {t} → 𝑪 {n} 𝓐  m≤n t → 𝑪 {n} 𝓐  m≤n (subst ρ t)
    CRen         𝓐 m≤n ρ ▹0         = ▹0
    CRen {zero}  𝓐 ()  ρ (▹ 𝒕)
    CRen {suc n} 𝓐 m≤n ρ (▹ 𝒕)      = ▹ satRename 𝓐 (pred≤ℕ m≤n) ρ 𝒕
    CRen         𝓐 m≤n ρ (ne 𝒏)     = ne (substSNe (ρ , (λ x → var (ρ x))) 𝒏)
    CRen         𝓐 m≤n ρ (exp t⇒ 𝒕) = exp (subst⇒ (ρ , (λ x → var (ρ x))) t⇒) (CRen 𝓐 m≤n ρ 𝒕)

  ⟦▸⟧_ : ∀{n} (𝓐 : SATpred a n) → SAT (▸̂ a∞) n
  ⟦▸⟧_ {n} 𝓐 = record
    { satSet = 𝑪 𝓐
    ; satProp = λ m≤n → record
      { satSNe = ne
      ; satSN  = CSN 𝓐 m≤n
      ; satExp = exp
      ; satRename = CRen 𝓐 m≤n
      }
    }