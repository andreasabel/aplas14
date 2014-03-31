{-# OPTIONS --copatterns --sized-types #-}

-- Type interpretation and soundness of typing.

module Soundness where

open import Library
open import SizedInfiniteTypes
open import Terms
open import Substitution
open import SN
open import SN.AntiSubst
open import SN.AntiRename
open import SAT2

-- Type interpretation

⟦_⟧_ : (a : Ty) (n : ℕ) → SAT a n
⟦ a ×̂ b ⟧ n     = ⟦ a ⟧ n ⟦×⟧ ⟦ b ⟧ n
⟦ a →̂ b ⟧ n     = ⟦ a ⟧ n ⟦→⟧ ⟦ b ⟧ n
⟦ ▸̂ a∞  ⟧ zero  = ⟦▸⟧ _
⟦ ▸̂ a∞  ⟧ suc n = ⟦▸⟧ ⟦ force a∞ ⟧ n

-- Context interpretation (semantic substitutions)

⟦_⟧C : ∀ Γ n {Δ} (σ : Subst Γ Δ) → Set
⟦ Γ ⟧C n σ = ∀ {a} (x : Var Γ a) → σ x ∈ ⟦ a ⟧ n

-- Lift : ∀ {a n Γ Δ} {σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C n σ) → ⟦ a ∷ Γ ⟧C n (lifts σ)
-- Lift θ (zero eq) = ↿ SAT.satSNe (⟦ _ ⟧ _) (var (zero eq))
-- Lift θ (suc x)   = {! θ x !}  -- TODO: semantic types closed under renaming

Ext : ∀ {a n Δ Γ} {t : Tm Δ a} (𝒕 : t ∈ ⟦ a ⟧ n) →
      ∀ {σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C n σ) → ⟦ a ∷ Γ ⟧C n (t ∷s σ)
Ext {a} 𝒕 θ (zero eq) = {! 𝒕 !} -- need to cast
Ext {a} 𝒕 θ (suc x) = θ x

Rename : ∀ {n Δ Δ'} (ρ : Ren Δ Δ') →
         ∀ {Γ}{σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C n σ) →
         ⟦ Γ ⟧C n (ρ •s σ)
Rename ρ θ x = {!!} -- TODO: semantic types closed under renaming

⟦∗⟧ : ∀ {n Γ}{a : Ty} {b∞} {t : Tm Γ (▸̂ ((delay a) ⇒ b∞))}
           {t₁ : Tm Γ (▸ a)} →
         t ∈ (⟦ ▸̂ ((delay a) ⇒ b∞) ⟧ n) →
         t₁ ∈ (⟦ ▸̂ (delay a) ⟧ n) →
         (t ∗ t₁) ∈ (⟦ ▸̂ b∞ ⟧ n)
⟦∗⟧ {zero}  (↿ ▹0)       (↿ ▹0)        = ↿ (exp β▹ ▹0)
⟦∗⟧ {zero}  (↿ ▹0)       (↿ ne 𝒏)      = ↿ ne (elim 𝒏 (∗r ▹0))
⟦∗⟧ {zero}  (↿ ▹0)       (↿ exp t⇒ 𝒕₁) = ↿ (exp (cong (∗r _) (∗r _) t⇒) (⇃ (⟦∗⟧ {n = 0} (↿ ▹0) (↿ 𝒕₁))))
⟦∗⟧ {zero}  (↿ ne 𝒏)     (↿ 𝒕₁)        = ↿ (ne (elim 𝒏 (SAT.satSN (⟦ _ ⟧ zero) 𝒕₁ ∗l)))
⟦∗⟧ {zero}  (↿ exp t⇒ 𝒕) (↿ 𝒕₁)        = ↿ exp (cong (_ ∗l) (_ ∗l) t⇒) (⇃ ⟦∗⟧ {n = zero} (↿ 𝒕) (↿ 𝒕₁))
⟦∗⟧ {suc n} (↿ (▹ 𝒕))    (↿ exp t⇒ 𝒕₁) = ↿ (exp (cong (∗r _) (∗r _) t⇒) (⇃ (⟦∗⟧ {n = suc n} (↿ (▹ 𝒕)) (↿ 𝒕₁))))
⟦∗⟧ {suc n} (↿ ne 𝒏)     (↿ 𝒕₁)        = ↿ (ne (elim 𝒏 (SAT.satSN (⟦ _ ⟧ suc n) 𝒕₁ ∗l)))
⟦∗⟧ {suc n} (↿ exp t⇒ 𝒕) (↿ 𝒕₁)        = ↿ (exp (cong (_ ∗l) (_ ∗l) t⇒) (⇃ ⟦∗⟧ {n = suc n} (↿ 𝒕) (↿ 𝒕₁)))
⟦∗⟧ {suc n}         {b∞ = b∞} (↿ (▹ 𝒕)) (↿ (▹ 𝒕₁)) = ↿ (exp β▹ (▹ ≡.subst (λ t → SAT.satSet (⟦ force b∞ ⟧ n) (app t _)) renId (𝒕 id {!!} 𝒕₁)))
⟦∗⟧ {suc n} {a = a} {b∞ = b∞} (↿ (▹ 𝒕)) (↿ ne 𝒏)   = ↿ ne (elim 𝒏 (∗r (▹ ( SAT.satSN ((⟦ a ⟧ n) ⟦→⟧ (⟦ force b∞ ⟧ n)) (\ {Δ} → 𝒕)))))

-- Soundness

sound : ∀ {n a Γ} (t : Tm Γ a) {Δ} {σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C n σ) → subst σ t ∈ ⟦ a ⟧ n
sound (var x) θ = θ x
sound {n = n} (abs t) {σ = σ} θ = ⟦abs⟧ (λ ρ {u} 𝒖 →
  let open ≡-Reasoning
      eq : subst (u ∷s (ρ •s σ)) t ≡ subst0 u (subst (lifts ρ) (subst (lifts σ) t))
      eq = begin

             subst (u ∷s (ρ •s σ)) t

           ≡⟨ subst-ext (cons-to-sgs u _) t ⟩

              subst (sgs u •s lifts (ρ •s σ)) t

           ≡⟨ subst-∙ _ _ t ⟩

             subst0 u (subst (lifts (ρ •s σ)) t)

           ≡⟨ ≡.cong (subst0 u) (subst-ext (lifts-∙ ρ σ) t) ⟩

             subst0 u (subst (lifts ρ •s lifts σ) t)

           ≡⟨ ≡.cong (subst0 u) (subst-∙ (lifts ρ) (lifts σ) t) ⟩

             subst0 u (subst (lifts ρ) (subst (lifts σ) t))
           ∎
  in  ≡.subst (λ tu → tu ∈ ⟦ _ ⟧ n) eq (sound t (Ext 𝒖 (Rename ρ θ))))
sound (app t u   ) θ = ⟦app⟧ (sound t θ) (sound u θ)
sound (pair t₁ t₂) θ = ⟦pair⟧ (sound t₁ θ) (sound t₂ θ)
sound (fst t) θ = ↿ (proj₁ (⇃ (sound t θ)))
sound (snd t) θ = ↿ (proj₂ (⇃ (sound t θ)))
-- sound (fst t) θ = ⟦fst⟧ (sound t θ)  -- YELLOW, why?
-- sound (snd t) θ = ⟦snd⟧ (sound t θ)
sound {zero} (▹ t) θ = ↿ ▹0
sound {suc n} (▹ t) θ = ↿ (▹ (⇃ sound t {!!}))
sound (t ∗ t₁) {σ} θ = ⟦∗⟧ (sound t θ) (sound t₁ θ)

