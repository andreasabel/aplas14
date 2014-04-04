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
open import SAT3

-- Type interpretation

⟦_⟧_ : (a : Ty) (n : ℕ) → SAT a n
⟦ a →̂ b ⟧ n  = ⟦ a ⟧ n ⟦→⟧ ⟦ b ⟧ n
⟦ a ×̂ b ⟧ n  = ⟦ a ⟧ n ⟦×⟧ ⟦ b ⟧ n
⟦ ▸̂ a∞  ⟧ n  = ⟦▸⟧ P n   
  where
    P : ∀ n → SATpred (force a∞) n
    P zero = _
    P (suc n₁) = ⟦ force a∞ ⟧ n₁

map⟦_⟧ : ∀ (a : Ty) → ∀ {m n l o} → .(l≤m : l ≤ℕ m) → .(o≤n : o ≤ℕ n) → .(l ≤ℕ o) → ∀ {Γ} {t : Tm Γ a} → SAT.satSet (⟦ a ⟧ n) o≤n t 
                                           → SAT.satSet (⟦ a ⟧ m) l≤m t
map⟦_⟧ (a →̂ a₁) l≤m o≤n l≤o  𝑡          = λ q q≤l ρ ρrefl 𝑢 →
       let .q≤m : _; q≤m = ≤ℕ.trans q≤l l≤m
           .q≤o : _; q≤o = ≤ℕ.trans q≤l l≤o
           .q≤n : _; q≤n = ≤ℕ.trans q≤o o≤n in 
       map⟦ a₁ ⟧ q≤m q≤n ≤ℕ.refl (𝑡 q q≤o ρ ρrefl (map⟦ a ⟧ q≤n q≤m ≤ℕ.refl 𝑢))
map⟦_⟧ (a ×̂ a₁)                       l≤m o≤n l≤o (t1 , t2)  = map⟦ a ⟧ l≤m o≤n l≤o t1 , map⟦ a₁ ⟧ l≤m o≤n l≤o t2
map⟦_⟧ (▸̂ a∞) {l = zero}              l≤m o≤n _   ▹0         = ▹0
map⟦_⟧ (▸̂ a∞) {l = suc l}             l≤m o≤n ()  ▹0 
map⟦_⟧ (▸̂ a∞) {l = zero}              l≤m o≤n l≤o (▹ 𝒕)      = ▹0
map⟦_⟧ (▸̂ a∞) {zero} {l = suc l}      ()  o≤n l≤o (▹ 𝒕)
map⟦_⟧ (▸̂ a∞) {suc m} {zero} {suc l}  l≤m ()  l≤o (▹ 𝒕)
map⟦_⟧ (▸̂ a∞) {suc m} {suc n} {suc l} l≤m o≤n l≤o (▹ 𝒕)      = ▹ map⟦ (force a∞) ⟧ (pred≤ℕ l≤m) (pred≤ℕ o≤n) (pred≤ℕ l≤o) 𝒕
map⟦_⟧ (▸̂ a∞)                         l≤m o≤n l≤o (ne 𝒏)     = ne (mapSNe l≤o 𝒏)
map⟦_⟧ (▸̂ a∞)                         l≤m o≤n l≤o (exp t⇒ 𝑡) = exp (map⇒ l≤o t⇒) (map⟦ (▸̂ a∞) ⟧ l≤m o≤n l≤o 𝑡)

map⟦_⟧∈ : ∀ (a : Ty) → ∀ {m n} → .(m ≤ℕ n) → ∀ {Γ} {t : Tm Γ a} → t ∈ (⟦ a ⟧ n) 
                                           → t ∈ (⟦ a ⟧ m)
map⟦_⟧∈ a m≤n (↿ 𝑡) = ↿ (map⟦ a ⟧ ≤ℕ.refl ≤ℕ.refl m≤n 𝑡)

-- Context interpretation (semantic substitutions)

⟦_⟧C⟨_⟩ : ∀ Γ {n m} → .(m ≤ℕ n) → ∀ {Δ} (σ : Subst Γ Δ) → Set
⟦ Γ ⟧C⟨ m≤n ⟩  σ = ∀ {a} (x : Var Γ a) → σ x ∈⟨ m≤n ⟩ ⟦ a ⟧ _

⟦_⟧C : ∀ Γ n {Δ} (σ : Subst Γ Δ) → Set
⟦ Γ ⟧C n σ = ∀ {a} (x : Var Γ a) → σ x ∈ ⟦ a ⟧ n

-- Lift : ∀ {a n Γ Δ} {σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C n σ) → ⟦ a ∷ Γ ⟧C n (lifts σ)
-- Lift θ (zero eq) = ↿ SAT.satSNe (⟦ _ ⟧ _) (var (zero eq))
-- Lift θ (suc x)   = {! θ x !}  -- TODO: semantic types closed under renaming

Ext : ∀ {a n Δ Γ} {t : Tm Δ a} → ∀ {m} .(m≤n : m ≤ℕ n) → (𝒕 : t ∈⟨ m≤n ⟩ ⟦ a ⟧ n) →
      ∀ {σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C⟨ m≤n ⟩ σ) → ⟦ a ∷ Γ ⟧C⟨ m≤n ⟩ (t ∷s σ)
Ext {a} m≤n 𝒕 θ (zero eq) = {! 𝒕 !} -- need to cast
Ext {a} m≤n 𝒕 θ (suc x) = θ x

Rename : ∀ {n Δ Δ'} → ∀ {m} .(m≤n : m ≤ℕ n) → (ρ : Ren Δ Δ') →
         ∀ {Γ}{σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C⟨ m≤n ⟩ σ) →
         ⟦ Γ ⟧C⟨ m≤n ⟩ (ρ •s σ)
Rename ρ θ x = {!!} -- TODO: semantic types closed under renaming

⟦∗⟧ : ∀ {n Γ}{a : Ty} {b∞} {t : Tm Γ (▸̂ ((delay a) ⇒ b∞))} {u : Tm Γ (▸ a)}
      → t ∈ (⟦ ▸̂ ((delay a) ⇒ b∞) ⟧ n) → u ∈ (⟦ ▸̂ (delay a) ⟧ n) → (t ∗ u) ∈ (⟦ ▸̂ b∞ ⟧ n)
⟦∗⟧ {zero}  (↿ ▹0)       (↿ ▹0)        = ↿ exp β▹ ▹0
⟦∗⟧ {zero}  (↿ ▹0)       (↿ ne 𝒏)      = ↿ ne (elim 𝒏 (∗r ▹0))
⟦∗⟧ {zero}  (↿ ▹0)       (↿ exp t⇒ 𝒕₁) = ↿ exp (cong (∗r _) (∗r _) t⇒) (⇃ (⟦∗⟧ {n = 0} (↿ ▹0) (↿ 𝒕₁)))
⟦∗⟧ {zero}  (↿ ne 𝒏)     (↿ 𝒕₁)        = ↿ ne (elim 𝒏 (SAT.satSN (⟦ _ ⟧ zero) ≤ℕ.refl 𝒕₁ ∗l))
⟦∗⟧ {zero}  (↿ exp t⇒ 𝒕) (↿ 𝒕₁)        = ↿ exp (cong (_ ∗l) (_ ∗l) t⇒) (⇃ ⟦∗⟧ {n = zero} (↿ 𝒕) (↿ 𝒕₁))
⟦∗⟧ {suc n} (↿ (▹ 𝒕))    (↿ exp t⇒ 𝒕₁) = ↿ exp (cong (∗r _) (∗r _) t⇒) (⇃ (⟦∗⟧ {n = suc n} (↿ (▹ 𝒕)) (↿ 𝒕₁)))
⟦∗⟧ {suc n} (↿ ne 𝒏)     (↿ 𝒕₁)        = ↿ ne (elim 𝒏 (SAT.satSN (⟦ _ ⟧ suc n) ≤ℕ.refl 𝒕₁ ∗l))
⟦∗⟧ {suc n} (↿ exp t⇒ 𝒕) (↿ 𝒕₁)        = ↿ exp (cong (_ ∗l) (_ ∗l) t⇒) (⇃ ⟦∗⟧ {n = suc n} (↿ 𝒕) (↿ 𝒕₁))
⟦∗⟧ {suc n}         {b∞ = b∞} (↿ (▹ 𝒕)) (↿ (▹ 𝒕₁)) = ↿ exp β▹ (▹ ≡.subst (λ t → SAT.satSet (⟦ force b∞ ⟧ n) ≤ℕ.refl (app t _)) renId (𝒕 n ≤ℕ.refl id TODO 𝒕₁))
⟦∗⟧ {suc n} {a = a} {b∞ = b∞} (↿ (▹ 𝒕)) (↿ ne 𝒏)   = ↿ ne (elim 𝒏 (∗r (▹ ( SAT.satSN ((⟦ a ⟧ n) ⟦→⟧ (⟦ force b∞ ⟧ n)) ≤ℕ.refl 𝒕))))

-- Soundness
{-
sound : ∀ {n a Γ} (t : Tm Γ a) {Δ} {σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C n σ) → subst σ t ∈ ⟦ a ⟧ n
sound (var x) θ = θ x
sound {n = n} (abs t) {σ = σ} θ = ⟦abs⟧ {n = n} {𝓐 = ⟦ _ ⟧ n} {𝓑 = ⟦ _ ⟧ n} (λ m≤n ρ {u} 𝒖 →
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
  in  ≡.subst (λ tu → tu ∈⟨ m≤n ⟩ (⟦ _ ⟧ n)) eq {! (sound t {!𝒖 !} m≤n) !})
sound (app t u   ) θ = ⟦app⟧ (sound t θ) (sound u θ)
sound (pair t₁ t₂) θ = ⟦pair⟧ (sound t₁ θ) (sound t₂ θ)
sound (fst t) θ = ↿ (proj₁ (⇃ (sound t θ)))
sound (snd t) θ = ↿ (proj₂ (⇃ (sound t θ)))
-- sound (fst t) θ = ⟦fst⟧ (sound t θ)  -- YELLOW, why?
-- sound (snd t) θ = ⟦snd⟧ (sound t θ)
sound {zero} (▹ t) θ = ↿ ▹0
sound {suc n} (▹ t) θ = ↿ (▹ (⇃ sound t (λ x → map⟦ _ ⟧∈ n≤sn (θ x))))
sound (t ∗ t₁) {σ} θ = ⟦∗⟧ (sound t θ) (sound t₁ θ)
-}

sound≤ : ∀ {n a Γ} (t : Tm Γ a) {Δ} {σ : Subst Γ Δ} → ∀ {m} .(m≤n : m ≤ℕ n) → (θ : ⟦ Γ ⟧C⟨ m≤n ⟩ σ) →  subst σ t ∈⟨ m≤n ⟩ ⟦ a ⟧ n
sound≤ (var x)     m≤n θ = θ x
sound≤ {n} (abs {a = a} {b = b} t) {σ = σ}    m≤n θ = ⟦abs⟧ {𝓐 = ⟦ _ ⟧ _} {𝓑 = ⟦ _ ⟧ _} m≤n (λ l≤m ρ {u} 𝑢 → 
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
  in
                                 ≡.subst (λ tu → tu ∈⟨ ≤ℕ.trans l≤m m≤n ⟩ (⟦ b ⟧ n)) eq (sound≤ t (≤ℕ.trans l≤m m≤n) 
                   (Ext (≤ℕ.trans l≤m m≤n) 𝑢 (Rename (≤ℕ.trans l≤m m≤n) ρ (λ {a} x → ↿ (map⟦ a ⟧ (≤ℕ.trans l≤m m≤n) m≤n l≤m (⇃ θ x)))))))
sound≤ (app t t₁)  m≤n θ = ⟦app⟧ m≤n (sound≤ t m≤n θ) (sound≤ t₁ m≤n θ)
sound≤ (pair t t₁) m≤n θ = {!!}
sound≤ (fst t)     m≤n θ = {!!}
sound≤ (snd t)     m≤n θ = {!!}
sound≤ (t ∗ t₁)    m≤n θ = {!!}
sound≤         (▹ t) {m = zero}  m≤n θ = ↿ ▹0
sound≤ {zero}  (▹ t) {m = suc m} ()  θ 
sound≤ {suc n} (▹ t) {m = suc m} m≤n θ = ↿ (▹ (⇃ sound≤ t (pred≤ℕ m≤n) (λ {a} x → ↿ map⟦ a ⟧ (pred≤ℕ m≤n) m≤n n≤sn (⇃ θ x))))

sound : ∀ {n a Γ} (t : Tm Γ a) {Δ} {σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C n σ) → subst σ t ∈ ⟦ a ⟧ n
sound t θ = sound≤ t ≤ℕ.refl θ