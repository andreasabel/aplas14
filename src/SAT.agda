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

-- Elementhood for saturated sets.

-- Workaround. Agda does not accept projection satSet directly,
-- maybe since it is defined in another module.
satSet' = satSet
syntax satSet' 𝓐 t = t ∈ 𝓐

-- Semantic function type.

_⟦→⟧_ : ∀{n} (𝓐 𝓑 : SAT n) → SAT n
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
    CSN 𝒕 = absVarSN (SAT.satSN 𝓑 (𝒕 suc (SAT.satSNe 𝓐 (var zero))))

    CExp :  ∀{Γ}{t t' : Tm Γ _} → t ⟨ _ ⟩⇒ t' → 𝑪 t' → 𝑪 t
    CExp t⇒ 𝒕 ρ 𝒖 = SAT.satExp 𝓑 (cong (appl _) (appl _) (subst⇒ (renSN ρ) t⇒)) (𝒕 ρ 𝒖)

-- Lemma: If 𝓐, 𝓑 ∈ SAT and t[u] ∈ 𝓑 for all a ∈ 𝓐, then λt ∈ 𝓐 ⟦→⟧ 𝓑

module _ {n}{𝓐 𝓑 : SAT n} where
  a = SAT.satTy 𝓐
  b = SAT.satTy 𝓑

  semAbs : ∀{Γ}{t : Tm (a ∷ Γ) b} →
    (∀{Δ} (ρ : Δ ≤ Γ) {u : Tm Δ a} → u ∈ 𝓐 → subst0 u (subst (lifts ρ) t) ∈ 𝓑) → abs t ∈ (𝓐 ⟦→⟧ 𝓑)
  semAbs 𝒕 ρ 𝒖 = SAT.satExp 𝓑 (β (SAT.satSN 𝓐 𝒖)) (𝒕 ρ 𝒖)

bothProjSN : ∀{n a b Γ}{t : Tm Γ (a ×̂ b)} →
  (𝒕₁ : SN n (fst t)) (𝒕₂ : SN n (snd t)) → SN n t
bothProjSN (ne (elim 𝒏 fst)) 𝒕₂ = ne 𝒏
bothProjSN (exp (βfst 𝒕₂) 𝒕₁) _  = pair 𝒕₁ 𝒕₂
{-
bothProjSN (exp (βfst 𝒖) 𝒕₁) (ne (elim 𝒏 snd)) = ne 𝒏
bothProjSN (exp (βfst 𝒖) 𝒕₁) (exp (βsnd 𝒕) 𝒕₂) = pair 𝒕₁ 𝒕₂
bothProjSN (exp (βfst 𝒖) 𝒕₁) (exp (cong 𝑬𝒕 𝑬𝒕' t⇒) 𝒕₂) = pair 𝒕₁ 𝒖
-}
bothProjSN (exp (cong _ _ _) _) (ne (elim 𝒏 snd)) = ne 𝒏
bothProjSN (exp (cong _ _ _) _) (exp (βsnd 𝒕₁) 𝒕₂) = pair 𝒕₁ 𝒕₂
bothProjSN (exp (cong fst fst t⇒) 𝒕₁) (exp (cong snd snd t⇒₁) 𝒕₂) = {!bothProjSN 𝒕₁ 𝒕₂!}
{-
bothProjSN (ne (elim () 𝒏 (appl 𝒖))) (ne 𝒏₁)
bothProjSN (ne (elim eq 𝒏 fst)) (ne 𝒏₁) = {!!}
bothProjSN (ne (elim () 𝒏 snd)) (ne 𝒏₁)
bothProjSN (ne (elim () 𝒏 (𝒖 ∗l))) (ne 𝒏₁)
bothProjSN (ne (elim () 𝒏 (∗r 𝒕))) (ne 𝒏₁)
bothProjSN (ne 𝒏) (exp t⇒ 𝒕₂) = {!!}
bothProjSN (exp t⇒ 𝒕₁) 𝒕₂ = {!!}
-}

-- Semantic product type

_⟦×⟧_ : ∀{n} (𝓐 𝓑 : SAT n) → SAT n
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

