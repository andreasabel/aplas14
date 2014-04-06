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
Rename m≤n ρ θ {a} x = ↿ SAT.satRename (⟦ a ⟧ _) m≤n ρ (⇃ θ x)

Map : ∀ {m n l o} → .(l≤m : l ≤ℕ m) → .(o≤n : o ≤ℕ n) → .(l≤o : l ≤ℕ o) 
      → ∀ {Γ Δ} {σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C⟨ o≤n ⟩ σ) → ⟦ Γ ⟧C⟨ l≤m ⟩ σ
Map l≤m o≤n l≤o θ {a} x = ↿ (map⟦ a ⟧ l≤m o≤n l≤o (⇃ θ x))

⟦∗⟧ : ∀ {n Γ}{a : Ty} {b∞} {t : Tm Γ (▸̂ ((delay a) ⇒ b∞))} {u : Tm Γ (▸ a)}
      → ∀ {m} .(m≤n : m ≤ℕ n) → t ∈⟨ m≤n ⟩ (⟦ ▸̂ ((delay a) ⇒ b∞) ⟧ n) → u ∈⟨ m≤n ⟩ (⟦ ▸̂ (delay a) ⟧ n) → (t ∗ u) ∈⟨ m≤n ⟩ (⟦ ▸̂ b∞ ⟧ n)
⟦∗⟧ m≤n (↿ ▹0) (↿ ▹0) = ↿ (exp β▹ ▹0)
⟦∗⟧ m≤n (↿ ▹0) (↿ ne 𝒏) = ↿ (ne (elim 𝒏 (∗r ▹0)))
⟦∗⟧ m≤n (↿ ▹0) (↿ exp t⇒ 𝑡1) = ↿ exp (cong (∗r _) (∗r _) t⇒) (⇃ ⟦∗⟧ m≤n (↿ ▹0) (↿ 𝑡1))
⟦∗⟧ {suc n} {a = a} {b∞ = b∞}  {m = suc m} m≤n (↿ (▹ 𝒕)) (↿ (▹_ {t = u} 𝒕₁)) 
 = ↿ exp β▹
     (▹ ≡.subst (λ t → SAT.satSet (⟦ force b∞ ⟧ n) (pred≤ℕ m≤n) (app t u))
          renId (𝒕 m ≤ℕ.refl id TODO 𝒕₁))
⟦∗⟧ {zero} {a = a} {b∞ = b∞}  {m = suc m} () (↿ (▹ 𝒕)) _
⟦∗⟧ {suc n} {a = a} {b∞ = b∞}  {m = suc m} m≤n (↿ (▹ 𝒕)) (↿ ne 𝒏) = ↿ (ne (elim 𝒏 (∗r (▹ SAT.satSN ((⟦ a ⟧ n) ⟦→⟧ (⟦ force b∞ ⟧ n)) (pred≤ℕ m≤n) 𝒕))))
⟦∗⟧ m≤n (↿ (▹ 𝒕)) (↿ exp t⇒ 𝑡1) = ↿ exp (cong (∗r _) (∗r _) t⇒) (⇃ ⟦∗⟧  m≤n (↿ (▹ 𝒕)) (↿ 𝑡1))
⟦∗⟧ m≤n (↿ ne 𝒏) (↿ 𝑡1) = ↿ ne (elim 𝒏 (SAT.satSN (⟦ _ ⟧ _) m≤n 𝑡1 ∗l))
⟦∗⟧ m≤n (↿ exp t⇒ 𝑡) (↿ 𝑡1) = ↿ exp (cong (_ ∗l) (_ ∗l) t⇒) (⇃ ⟦∗⟧ m≤n (↿ 𝑡) (↿ 𝑡1))

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
      .l≤n : _
      l≤n = ≤ℕ.trans l≤m m≤n
  in ≡.subst (λ tu → tu ∈⟨ l≤n ⟩ (⟦ b ⟧ n)) eq (sound≤ t l≤n 
                   (Ext l≤n 𝑢 (Rename l≤n ρ (Map l≤n m≤n l≤m θ)))))
sound≤ (app t t₁)  m≤n θ = ⟦app⟧ m≤n (sound≤ t m≤n θ) (sound≤ t₁ m≤n θ)
sound≤ (pair t t₁) m≤n θ = ⟦pair⟧ m≤n (sound≤ t m≤n θ) (sound≤ t₁ m≤n θ)
sound≤ (fst t)     m≤n θ = ⟦fst⟧ {𝓐 = ⟦ _ ⟧ _} {𝓑 = ⟦ _ ⟧ _} m≤n (sound≤ t m≤n θ)
sound≤ (snd t)     m≤n θ = ⟦snd⟧ {𝓐 = ⟦ _ ⟧ _} {𝓑 = ⟦ _ ⟧ _} m≤n (sound≤ t m≤n θ)
sound≤ (t ∗ t₁)    m≤n θ = ⟦∗⟧ m≤n (sound≤ t m≤n θ) (sound≤ t₁ m≤n θ)
sound≤         (▹ t) {m = zero}  m≤n θ = ↿ ▹0
sound≤ {zero}  (▹ t) {m = suc m} ()  θ 
sound≤ {suc n} (▹ t) {m = suc m} m≤n θ = ↿ (▹ (⇃ sound≤ t (pred≤ℕ m≤n) (Map (pred≤ℕ m≤n) m≤n n≤sn θ)))

sound : ∀ {n a Γ} (t : Tm Γ a) {Δ} {σ : Subst Γ Δ} (θ : ⟦ Γ ⟧C n σ) → subst σ t ∈ ⟦ a ⟧ n
sound t θ = sound≤ t ≤ℕ.refl θ
