-- Saturated sets.

{-# OPTIONS --copatterns --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

module SAT2 where

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
--open IsSAT

record SAT (a : Ty) (n : ℕ) : Set₁ where
  -- constructor sat
  field
    satSet  : TmSet a
    satProp : IsSAT n satSet
  open IsSAT satProp public
open SAT

-- Elementhood for saturated sets.

-- Workaround. Agda does not accept projection satSet directly,
-- maybe since it is defined in another module.
satSet' = satSet
syntax satSet' 𝓐 t = t ∈ 𝓐

-- Semantic function type.

_⟦→⟧_ : ∀ {n a b} (𝓐 : SAT a n) (𝓑 : SAT b n) → SAT (a →̂ b) n
𝓐 ⟦→⟧ 𝓑 = record
  { satSet  = 𝑪
  ; satProp = record
    { satSNe = CSNe
    ; satSN  = CSN
    ; satExp = CExp
    }
  }
  where
    𝑨 = satSet 𝓐
    𝑩 = satSet 𝓑
    𝑪 = 𝑨 [→] 𝑩

    CSNe : SNe _ ⊆ 𝑪
    CSNe 𝒏 ρ 𝒖 = SAT.satSNe 𝓑 (sneApp (renameSNe ρ 𝒏) (SAT.satSN 𝓐 𝒖))

    CSN : 𝑪 ⊆ SN _
    CSN 𝒕 = unRenameSN (prop→Ind suc ≡.refl) (absVarSN (SAT.satSN 𝓑 (𝒕 suc (SAT.satSNe 𝓐 (var zero)))))

    CExp :  ∀{Γ}{t t' : Tm Γ _} → t ⟨ _ ⟩⇒ t' → 𝑪 t' → 𝑪 t
    CExp t⇒ 𝒕 ρ 𝒖 = SAT.satExp 𝓑 (cong (appl _) (appl _) (subst⇒ (renSN ρ) t⇒)) (𝒕 ρ 𝒖)

-- Lemma: If 𝓐, 𝓑 ∈ SAT and t[u] ∈ 𝓑 for all a ∈ 𝓐, then λt ∈ 𝓐 ⟦→⟧ 𝓑

semAbs : ∀{n a b}{𝓐 : SAT a n}{𝓑 : SAT b n}{Γ}{t : Tm (a ∷ Γ) b} →
    (∀{Δ} (ρ : Δ ≤ Γ) {u : Tm Δ a} → u ∈ 𝓐 → subst0 u (subst (lifts ρ) t) ∈ 𝓑) → abs t ∈ (𝓐 ⟦→⟧ 𝓑)
semAbs {𝓐 = 𝓐}{𝓑 = 𝓑} 𝒕 ρ 𝒖 = SAT.satExp 𝓑 (β (SAT.satSN 𝓐 𝒖)) (𝒕 ρ 𝒖)

-- Semantic product type

_⟦×⟧_ : ∀ {n a b} (𝓐 : SAT a n) (𝓑 : SAT b n) → SAT (a ×̂ b) n
𝓐 ⟦×⟧ 𝓑 = record
  { satSet   = 𝑪
  ; satProp  = record
    { satSNe = CSNe
    ; satSN  = CSN
    ; satExp = CExp
    }
  }
  where
    𝑨 = satSet 𝓐
    𝑩 = satSet 𝓑
    𝑪 = 𝑨 [×] 𝑩

    CSNe : SNe _ ⊆ 𝑪
    CSNe 𝒏 = (SAT.satSNe 𝓐 (elim  𝒏 fst))
           , (SAT.satSNe 𝓑 (elim  𝒏 snd))

    CSN : 𝑪 ⊆ SN _
    CSN (𝒕₁ , 𝒕₂) = bothProjSN (SAT.satSN 𝓐 𝒕₁) (SAT.satSN 𝓑 𝒕₂)

    CExp :  ∀{Γ}{t t' : Tm Γ _} → t ⟨ _ ⟩⇒ t' → 𝑪 t' → 𝑪 t
    CExp t⇒ (𝒕₁ , 𝒕₂) = (SAT.satExp 𝓐 (cong fst fst t⇒) 𝒕₁)
                     , (SAT.satExp 𝓑 (cong snd snd t⇒) 𝒕₂)

semPair : ∀ {n a b} (𝓐 : SAT a n) (𝓑 : SAT b n) {Γ} {t₁ : Tm Γ a} {t₂ : Tm Γ b}
          → t₁ ∈ 𝓐 → t₂ ∈ 𝓑 → pair t₁ t₂ ∈ 𝓐 ⟦×⟧ 𝓑
semPair 𝓐 𝓑 𝒕₁ 𝒕₂ = satExp 𝓐 (βfst (satSN 𝓑 𝒕₂)) 𝒕₁ , satExp 𝓑 (βsnd (satSN 𝓐 𝒕₁)) 𝒕₂

-- Any term set is saturated at level -1

SATpred : (a : Ty) (n : ℕ) → Set₁
SATpred a zero    = ⊤
SATpred a (suc n) = SAT a n

-- The underlying set at level -1 is the set of all terms of appropriate type

SATpredSet : {n : ℕ}{a : Ty} → SATpred a n → TmSet a
SATpredSet {zero} _ _ = ⊤
SATpredSet {suc n} = satSet

-- Semantic delay type

module _ {a∞ : ∞Ty} where
  private
    a = force a∞
    𝑪 : ∀{n} (𝓐 : SATpred a n) → TmSet (▸̂ a∞)
    𝑪 {n} 𝓐 = [▸] (SATpredSet 𝓐) n

    CSN : ∀ {n} (𝓐 : SATpred a n) → 𝑪 {n} 𝓐  ⊆ SN n
    CSN 𝓐  ▹0         = ▹0
    CSN 𝓐  (▹ 𝒕)      = ▹ satSN 𝓐 𝒕
    CSN 𝓐  (ne 𝒏)     = ne 𝒏
    CSN 𝓐  (exp t⇒ 𝒕) = exp t⇒ (CSN 𝓐 𝒕)

  ⟦▸⟧_ : ∀{n} (𝓐 : SATpred a n) → SAT (▸̂ a∞) n
  ⟦▸⟧_ {n} 𝓐 = record
    { satSet = 𝑪 𝓐
    ; satProp = record
      { satSNe = ne
      ; satSN  = CSN 𝓐
      ; satExp = exp
      }
    }

{-
module _ {a : Ty} where
  private
    𝑪 : ∀{n} (𝓐 : SAT a (pred n)) → TmSet (▸ _)
    𝑪 {n} 𝓐 = [▸] (satSet 𝓐) n

    CSN : ∀ {n} (𝓐 : SAT a (pred n)) → 𝑪 {n} 𝓐  ⊆ SN n
    CSN 𝓐  ▹0_        = ▹0
    CSN 𝓐  (▹ 𝒕)      = ▹ satSN 𝓐 𝒕
    CSN 𝓐  (ne 𝒏)     = ne 𝒏
    CSN 𝓐  (exp t⇒ 𝒕) = exp t⇒ (CSN 𝓐 𝒕)

  ⟦▸⟧_ : ∀{n} (𝓐 : SAT a (pred n)) → SAT (▸ a) n
  ⟦▸⟧_ {n} 𝓐 = record
    { satSet = 𝑪 𝓐
    ; satProp = record
      { satSNe = ne
      ; satSN  = CSN 𝓐
      ; satExp = exp
      }
    }
-}
