-- Saturated sets.

{-# OPTIONS --copatterns --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}

module SAT where

open import Library
open import SizedInfiniteTypes
open import Terms
open import Substitution
open import SN

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

-- Saturated term sets.

record IsSAT (n : ℕ) {a} (𝑨 : TmSet a) : Set where
  -- constructor isSat
  field
    satSNe  : SNe n ⊆ 𝑨
    satSN   : 𝑨 ⊆ SN n
    satExp  : Closed n 𝑨
open IsSAT

record SAT (n : ℕ) : Set₁ where
  -- constructor sat
  field
    {satTy} : Ty
    satSet  : TmSet satTy
    satProp : IsSAT n satSet
  open IsSAT satProp public
open SAT

-- Semantic types

_⟦→⟧_ : ∀{n} (𝓐 𝓑 : SAT n) → SAT n
𝓐 ⟦→⟧ 𝓑 = record
  { satSet  = 𝑪
  ; satProp = record
    { satSNe = {!!}
    ; satSN  = {!!}
    ; satExp = {!!}
    }
  }
  where
    𝑨 = satSet 𝓐
    𝑩 = satSet 𝓑
    𝑪 = 𝑨 [→] 𝑩
    CSNe : SNe _ ⊆ 𝑪
    CSNe (var x) ρ 𝓾 = {!!}
    CSNe (elim ν E) ρ 𝓾 = {!!}

{-
_⟦×⟧_ :  ∀{a b} → TmSet a → TmSet b → TmSet (a ×̂ b)
(𝓐 ⟦×⟧ 𝓑) t = 𝓐 (fst t) × 𝓑 (snd t)

-- If 𝓐, 𝓑 ∈ SAT
-- Lemma: λ x → t ∈ (𝓐 ⟦→⟧ 𝓑)

semAbs : ∀{a b}{𝓐 : TmSet a}{𝓑 : TmSet b}{Γ}{t : Tm (a ∷ Γ) b} →
  (∀{u} → u ∈ 𝓐 → subst0 u t ∈ 𝓑) → abs t ∈ (𝓐 ⟦→⟧ 𝓑)
semAbs = TODO
-}

